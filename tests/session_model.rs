//! Model-based property tests of the gateway session layer (wire 2.1 / 3.2,
//! `PqSession` in src/crypto.rs).
//!
//! Each case draws a session key, a handshake version and a sequence of up to
//! 48 operations: the client or the server sealing a message; the network
//! delivering, losing or swapping frames in flight; and an active attacker
//! replaying any earlier frame, reflecting a frame back to the end that
//! sealed it, flipping one bit of a frame, truncating one, or forging one at
//! the receiver's expected counter under the key of another session, of the
//! other handshake version, or of the opposite direction. After every
//! operation the two real ends are compared with a reference model that holds
//! four counters and the frames sealed so far:
//!
//! - a frame is accepted if and only if it is an unmodified frame of the
//!   receiver's incoming direction whose position is the receiver's counter;
//!   it then yields exactly what was sealed and that counter moves by one.
//!   Every other delivery is refused and neither end's state moves (the
//!   counters are read from the public `Debug` output; the keys are fixed at
//!   construction);
//! - every frame an end seals carries `session_nonce(n)` for its own counter
//!   `n`, opens under exactly one of the two published direction keys (the
//!   expected one; checked by trial decryption with an independent
//!   AES-256-GCM instance), and no (key, nonce) pair is produced twice in the
//!   session, across both directions;
//! - at the end, the frames each receiver has not yet accepted are delivered
//!   in order and all open, then one more frame each way opens: the stream
//!   continues after any refusal.
//!
//! The record-layer variant (`encrypt` / `decrypt`) runs 256 cases by default
//! and the full-frame variant (`sign_and_encrypt` / `decrypt_and_verify`, real
//! Falcon-512 signatures, what the gateway runs) 16; PROPTEST_CASES overrides
//! both.

use aes_gcm::aead::Aead;
use aes_gcm::{Aes256Gcm, Key, KeyInit, Nonce};
use pq_qkd_proxy::crypto::{
    derive_direction_keys, session_nonce, HandshakeVersion, PqKeyExchange, PqSession, Role,
};
use proptest::prelude::*;
use proptest::sample::Index;
use proptest::test_runner::{TestCaseError, TestRunner};
use std::cell::RefCell;
use std::collections::{HashSet, VecDeque};
use std::sync::OnceLock;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Dir {
    C2S,
    S2C,
}

impl Dir {
    fn i(self) -> usize {
        match self {
            Dir::C2S => 0,
            Dir::S2C => 1,
        }
    }
}

#[derive(Clone, Copy, Debug)]
enum Forgery {
    /// Sealed under the same direction's key of an unrelated session.
    OtherSession,
    /// Sealed under the same session key expanded with the other version's
    /// domains (a peer that picked the wrong schedule).
    OtherVersion,
    /// Sealed under this session's key for the opposite direction.
    OppositeDirection,
}

#[derive(Clone, Debug)]
enum Op {
    Send(Dir, Vec<u8>),
    Deliver(Dir),
    Lose(Dir),
    Swap(Dir),
    Replay(Dir, Index),
    Reflect(Dir, Index),
    Flip(Dir, Index, Index, u8),
    Truncate(Dir, Index, Index),
    Forge(Dir, Forgery),
}

fn dir() -> impl Strategy<Value = Dir> {
    prop_oneof![Just(Dir::C2S), Just(Dir::S2C)]
}

fn op() -> impl Strategy<Value = Op> {
    prop_oneof![
        4 => (dir(), prop::collection::vec(any::<u8>(), 0..48)).prop_map(|(d, m)| Op::Send(d, m)),
        4 => dir().prop_map(Op::Deliver),
        1 => dir().prop_map(Op::Lose),
        1 => dir().prop_map(Op::Swap),
        2 => (dir(), any::<Index>()).prop_map(|(d, i)| Op::Replay(d, i)),
        2 => (dir(), any::<Index>()).prop_map(|(d, i)| Op::Reflect(d, i)),
        2 => (dir(), any::<Index>(), any::<Index>(), 0u8..8)
            .prop_map(|(d, i, p, b)| Op::Flip(d, i, p, b)),
        1 => (dir(), any::<Index>(), any::<Index>()).prop_map(|(d, i, c)| Op::Truncate(d, i, c)),
        1 => (
            dir(),
            prop_oneof![
                Just(Forgery::OtherSession),
                Just(Forgery::OtherVersion),
                Just(Forgery::OppositeDirection)
            ]
        )
            .prop_map(|(d, f)| Op::Forge(d, f)),
    ]
}

fn version() -> impl Strategy<Value = HandshakeVersion> {
    prop_oneof![Just(HandshakeVersion::V2), Just(HandshakeVersion::V3)]
}

/// `send_counter` and `recv_counter` from the public `Debug` output.
fn counters(s: &PqSession) -> (u64, u64) {
    let d = format!("{s:?}");
    let field = |name: &str| -> u64 {
        let start = d.find(name).unwrap_or_else(|| panic!("{name} in {d}")) + name.len();
        d[start..]
            .chars()
            .take_while(|c| c.is_ascii_digit())
            .collect::<String>()
            .parse()
            .unwrap()
    };
    (field("send_counter: "), field("recv_counter: "))
}

fn cipher(key: &[u8; 32]) -> Aes256Gcm {
    Aes256Gcm::new(Key::<Aes256Gcm>::from_slice(key))
}

/// Long-lived Falcon identities for the full-frame variant: generated once.
fn identities() -> &'static (PqKeyExchange, PqKeyExchange) {
    static IDS: OnceLock<(PqKeyExchange, PqKeyExchange)> = OnceLock::new();
    IDS.get_or_init(|| (PqKeyExchange::new().unwrap(), PqKeyExchange::new().unwrap()))
}

/// A frame as sealed: its position in its direction, its wire bytes
/// (nonce ‖ ciphertext) and what the receiver must get back.
struct Sealed {
    pos: u64,
    wire: Vec<u8>,
    yields: Vec<u8>,
}

/// What a delivery is, for the tally.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Kind {
    /// An unmodified frame of the receiver's direction (in order, replayed,
    /// reordered or after a loss).
    Genuine,
    /// A frame handed back to the end that sealed it; `true` when its
    /// position is the counter that end expects, so only the keys refuse it.
    Reflected(bool),
    Flipped,
    Truncated,
    Forged,
}

/// Counts over a run, printed by the property tests (`--nocapture`), so the
/// report can say how much each kind of delivery was exercised.
#[derive(Default, Debug, Clone, Copy)]
struct Tally {
    cases: u64,
    ops: u64,
    sealed: u64,
    accepted: u64,
    refused_genuine_out_of_place: u64,
    refused_reflected: u64,
    refused_reflected_at_matching_counter: u64,
    refused_flipped: u64,
    refused_truncated: u64,
    refused_forged: u64,
}

impl Tally {
    fn add(&mut self, o: &Tally) {
        self.cases += o.cases;
        self.ops += o.ops;
        self.sealed += o.sealed;
        self.accepted += o.accepted;
        self.refused_genuine_out_of_place += o.refused_genuine_out_of_place;
        self.refused_reflected += o.refused_reflected;
        self.refused_reflected_at_matching_counter += o.refused_reflected_at_matching_counter;
        self.refused_flipped += o.refused_flipped;
        self.refused_truncated += o.refused_truncated;
        self.refused_forged += o.refused_forged;
    }
}

struct World {
    tally: Tally,
    /// `sign_and_encrypt` / `decrypt_and_verify` instead of `encrypt` / `decrypt`.
    full: bool,
    /// [client, server]
    ends: [PqSession; 2],
    /// Model: frames sealed per direction (= the sender's send counter).
    sent: [u64; 2],
    /// Model: frames accepted per direction (= the receiver's recv counter).
    accepted: [u64; 2],
    history: [Vec<Sealed>; 2],
    in_flight: [VecDeque<usize>; 2],
    /// The published direction keys, [c2s, s2c], and independent ciphers.
    keys: [[u8; 32]; 2],
    openers: [Aes256Gcm; 2],
    other_version: [[u8; 32]; 2],
    other_session: [[u8; 32]; 2],
    used: HashSet<([u8; 32], [u8; 12])>,
}

impl World {
    fn new(key: [u8; 32], version: HandshakeVersion, full: bool) -> Self {
        let (client_id, server_id) = identities();
        let client = PqSession::new(
            &key,
            version,
            Role::Client,
            [1; 32],
            server_id.falcon_pk_bytes().to_vec(),
        )
        .unwrap();
        let server = PqSession::new(
            &key,
            version,
            Role::Server,
            [2; 32],
            client_id.falcon_pk_bytes().to_vec(),
        )
        .unwrap();
        let k = derive_direction_keys(&key, version);
        let other_v = match version {
            HandshakeVersion::V2 => HandshakeVersion::V3,
            HandshakeVersion::V3 => HandshakeVersion::V2,
        };
        let ov = derive_direction_keys(&key, other_v);
        let mut unrelated = key;
        unrelated[0] ^= 0x80;
        let os = derive_direction_keys(&unrelated, version);
        World {
            tally: Tally::default(),
            full,
            ends: [client, server],
            sent: [0; 2],
            accepted: [0; 2],
            history: [Vec::new(), Vec::new()],
            in_flight: [VecDeque::new(), VecDeque::new()],
            keys: [k.c2s, k.s2c],
            openers: [cipher(&k.c2s), cipher(&k.s2c)],
            other_version: [ov.c2s, ov.s2c],
            other_session: [os.c2s, os.s2c],
            used: HashSet::new(),
        }
    }

    /// The end that seals in `d` (client for c2s) and the end that opens it.
    fn sender(d: Dir) -> usize {
        d.i()
    }
    fn receiver(d: Dir) -> usize {
        1 - d.i()
    }

    fn check_state(&self) -> Result<(), TestCaseError> {
        let (cs, cr) = counters(&self.ends[0]);
        let (ss, sr) = counters(&self.ends[1]);
        prop_assert_eq!(
            (cs, cr, ss, sr),
            (
                self.sent[0],
                self.accepted[1],
                self.sent[1],
                self.accepted[0]
            ),
            "state differs from the model (client send, client recv, server send, server recv)"
        );
        Ok(())
    }

    fn send(&mut self, d: Dir, msg: &[u8]) -> Result<(), TestCaseError> {
        let pos = self.sent[d.i()];
        let (client_id, server_id) = identities();
        let end = &mut self.ends[Self::sender(d)];
        let (nonce, ct, payload) = if self.full {
            let id = if d == Dir::C2S { client_id } else { server_id };
            let wire = end.sign_and_encrypt(msg, id.falcon_signing_key()).unwrap();
            let mut nonce = [0u8; 12];
            nonce.copy_from_slice(&wire[..12]);
            (nonce, wire[12..].to_vec(), None)
        } else {
            let (ct, nonce) = end.encrypt(msg).unwrap();
            (nonce, ct, Some(msg.to_vec()))
        };
        prop_assert_eq!(nonce, session_nonce(pos), "sealed at the wrong counter");

        // Which key sealed it: exactly the published key of direction `d`.
        let opened: Vec<Option<Vec<u8>>> = self
            .openers
            .iter()
            .map(|c| c.decrypt(Nonce::from_slice(&nonce), ct.as_slice()).ok())
            .collect();
        prop_assert!(
            opened[d.i()].is_some(),
            "frame does not open under its direction key"
        );
        prop_assert!(
            opened[1 - d.i()].is_none(),
            "frame opens under the opposite direction's key"
        );
        let inner = opened[d.i()].clone().unwrap();
        match &payload {
            Some(p) => prop_assert_eq!(&inner, p),
            None => {
                // len(4) ‖ data ‖ signature, as sign_and_encrypt documents.
                prop_assert!(inner.len() >= 4 + msg.len());
                prop_assert_eq!(&inner[..4], &(msg.len() as u32).to_be_bytes()[..]);
                prop_assert_eq!(&inner[4..4 + msg.len()], msg);
            }
        }
        prop_assert!(
            self.used.insert((self.keys[d.i()], nonce)),
            "(key, nonce) pair used twice in one session"
        );

        let mut wire = nonce.to_vec();
        wire.extend_from_slice(&ct);
        self.history[d.i()].push(Sealed {
            pos,
            wire,
            yields: msg.to_vec(),
        });
        self.in_flight[d.i()].push_back(self.history[d.i()].len() - 1);
        self.sent[d.i()] += 1;
        self.tally.sealed += 1;
        Ok(())
    }

    /// Present `wire` to the receiver of `d`. `genuine` is the frame it is an
    /// unmodified copy of, if any; the model accepts exactly when that frame's
    /// position is the receiver's counter.
    fn deliver(
        &mut self,
        d: Dir,
        wire: &[u8],
        genuine: Option<(u64, Vec<u8>)>,
        kind: Kind,
    ) -> Result<(), TestCaseError> {
        let end = &mut self.ends[Self::receiver(d)];
        let got = if self.full {
            end.decrypt_and_verify(wire).ok()
        } else if wire.len() < 12 {
            None
        } else {
            let mut nonce = [0u8; 12];
            nonce.copy_from_slice(&wire[..12]);
            end.decrypt(&wire[12..], &nonce).ok()
        };
        match genuine {
            Some((pos, yields)) if pos == self.accepted[d.i()] => {
                prop_assert_eq!(got, Some(yields), "the next genuine frame was not accepted");
                self.accepted[d.i()] += 1;
                self.tally.accepted += 1;
            }
            _ => {
                prop_assert!(got.is_none(), "a frame the model refuses was accepted");
                let t = &mut self.tally;
                match kind {
                    Kind::Genuine => t.refused_genuine_out_of_place += 1,
                    Kind::Reflected(matching) => {
                        t.refused_reflected += 1;
                        t.refused_reflected_at_matching_counter += u64::from(matching);
                    }
                    Kind::Flipped => t.refused_flipped += 1,
                    Kind::Truncated => t.refused_truncated += 1,
                    Kind::Forged => t.refused_forged += 1,
                }
            }
        }
        self.check_state()
    }

    fn deliver_sealed(&mut self, d: Dir, idx: usize) -> Result<(), TestCaseError> {
        let f = &self.history[d.i()][idx];
        let (wire, pos, yields) = (f.wire.clone(), f.pos, f.yields.clone());
        self.deliver(d, &wire, Some((pos, yields)), Kind::Genuine)
    }

    fn pick(&self, d: Dir, i: &Index) -> Option<usize> {
        let n = self.history[d.i()].len();
        (n > 0).then(|| i.index(n))
    }

    /// The network delivers the oldest frame in flight in `d`.
    fn deliver_next(&mut self, d: Dir) -> Result<(), TestCaseError> {
        match self.in_flight[d.i()].pop_front() {
            Some(idx) => self.deliver_sealed(d, idx),
            None => Ok(()),
        }
    }

    /// A frame sealed in `d`, handed back to the end that sealed it, which
    /// receives in the opposite direction.
    fn reflect(&mut self, d: Dir, idx: usize) -> Result<(), TestCaseError> {
        let f = &self.history[d.i()][idx];
        let (wire, pos) = (f.wire.clone(), f.pos);
        let back = if d == Dir::C2S { Dir::S2C } else { Dir::C2S };
        let matching = pos == self.accepted[back.i()];
        self.deliver(back, &wire, None, Kind::Reflected(matching))
    }

    fn flip(&mut self, d: Dir, idx: usize, at: usize, bit: u8) -> Result<(), TestCaseError> {
        let mut wire = self.history[d.i()][idx].wire.clone();
        wire[at] ^= 1 << bit;
        self.deliver(d, &wire, None, Kind::Flipped)
    }

    fn truncate(&mut self, d: Dir, idx: usize, cut: usize) -> Result<(), TestCaseError> {
        let wire = self.history[d.i()][idx].wire.clone();
        self.deliver(d, &wire[..cut], None, Kind::Truncated)
    }

    /// A well-formed frame at the receiver's expected counter, sealed under a
    /// key the receiver must not accept.
    fn forge(&mut self, d: Dir, f: Forgery) -> Result<(), TestCaseError> {
        let key = match f {
            Forgery::OtherSession => self.other_session[d.i()],
            Forgery::OtherVersion => self.other_version[d.i()],
            Forgery::OppositeDirection => self.keys[1 - d.i()],
        };
        let nonce = session_nonce(self.accepted[d.i()]);
        let mut payload = 2u32.to_be_bytes().to_vec();
        payload.extend_from_slice(b"hi");
        let ct = cipher(&key)
            .encrypt(Nonce::from_slice(&nonce), payload.as_slice())
            .unwrap();
        let mut wire = nonce.to_vec();
        wire.extend_from_slice(&ct);
        self.deliver(d, &wire, None, Kind::Forged)
    }

    fn apply(&mut self, op: &Op) -> Result<(), TestCaseError> {
        self.tally.ops += 1;
        match op {
            Op::Send(d, m) => self.send(*d, m)?,
            Op::Deliver(d) => self.deliver_next(*d)?,
            Op::Lose(d) => {
                self.in_flight[d.i()].pop_front();
            }
            Op::Swap(d) => {
                if self.in_flight[d.i()].len() >= 2 {
                    self.in_flight[d.i()].swap(0, 1);
                }
            }
            Op::Replay(d, i) => {
                if let Some(idx) = self.pick(*d, i) {
                    self.deliver_sealed(*d, idx)?;
                }
            }
            Op::Reflect(d, i) => {
                if let Some(idx) = self.pick(*d, i) {
                    self.reflect(*d, idx)?;
                }
            }
            Op::Flip(d, i, p, bit) => {
                if let Some(idx) = self.pick(*d, i) {
                    let at = p.index(self.history[d.i()][idx].wire.len());
                    self.flip(*d, idx, at, *bit)?;
                }
            }
            Op::Truncate(d, i, c) => {
                if let Some(idx) = self.pick(*d, i) {
                    let cut = c.index(self.history[d.i()][idx].wire.len());
                    self.truncate(*d, idx, cut)?;
                }
            }
            Op::Forge(d, f) => self.forge(*d, *f)?,
        }
        self.check_state()
    }

    /// Supply every frame each receiver still lacks, in order, then one new
    /// frame each way: all must open.
    fn drain(&mut self) -> Result<(), TestCaseError> {
        for d in [Dir::C2S, Dir::S2C] {
            while (self.accepted[d.i()] as usize) < self.history[d.i()].len() {
                let next = self.accepted[d.i()] as usize;
                self.deliver_sealed(d, next)?;
            }
            self.send(d, b"after the run")?;
            let last = self.history[d.i()].len() - 1;
            self.deliver_sealed(d, last)?;
            prop_assert_eq!(self.accepted[d.i()], self.sent[d.i()]);
        }
        self.check_state()
    }
}

fn run(
    key: [u8; 32],
    version: HandshakeVersion,
    ops: &[Op],
    full: bool,
) -> Result<Tally, TestCaseError> {
    let mut w = World::new(key, version, full);
    prop_assert_ne!(w.keys[0], w.keys[1]);
    w.check_state()?;
    for op in ops {
        w.apply(op)?;
    }
    w.drain()?;
    w.tally.cases = 1;
    Ok(w.tally)
}

fn cases(default: u32) -> u32 {
    std::env::var("PROPTEST_CASES")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(default)
}

/// Run the property for `cases` cases of up to `max_ops` operations; panics
/// with the shrunk counterexample on failure, prints the tally otherwise.
fn property(full: bool, cases: u32, max_ops: usize) {
    // No failure file: a failure panics with the shrunk case, which is the
    // regression to commit.
    let mut runner = TestRunner::new(ProptestConfig {
        cases,
        failure_persistence: None,
        ..ProptestConfig::default()
    });
    let total = RefCell::new(Tally::default());
    let strategy = (
        any::<[u8; 32]>(),
        version(),
        prop::collection::vec(op(), 0..max_ops),
    );
    let result = runner.run(&strategy, |(key, version, ops)| {
        let t = run(key, version, &ops, full)?;
        total.borrow_mut().add(&t);
        Ok(())
    });
    if let Err(e) = result {
        panic!("{e}");
    }
    eprintln!("session_model full={full}: {:?}", total.into_inner());
}

#[test]
fn record_layer_matches_the_model() {
    property(false, cases(256), 48);
}

#[test]
fn full_frames_match_the_model() {
    property(true, cases(16), 24);
}

/// The model itself must not be vacuous: one scripted run with every kind of
/// attack, in both record-layer and full-frame form, refuses each attack and
/// still accepts the honest frames in order. The reflection is placed at the
/// counter the reflecting end expects, so only the direction keys refuse it.
#[test]
fn the_model_accepts_honest_traffic_and_refuses_each_attack() {
    for full in [false, true] {
        for version in [HandshakeVersion::V2, HandshakeVersion::V3] {
            let mut w = World::new([7; 32], version, full);
            let c2s = Dir::C2S;
            let s2c = Dir::S2C;
            w.send(c2s, b"one").unwrap();
            w.send(c2s, b"two").unwrap();
            w.send(s2c, b"early reply").unwrap();
            // Reflection at the matching counter: the server's frame 0, back
            // to the server, which expects its client's frame 0.
            w.reflect(s2c, 0).unwrap();
            w.reflect(c2s, 0).unwrap();
            w.in_flight[c2s.i()].swap(0, 1);
            w.deliver_next(c2s).unwrap(); // "two" ahead of "one": refused
            w.deliver_next(c2s).unwrap(); // "one": accepted
            w.deliver_sealed(c2s, 0).unwrap(); // replay of "one": refused
            w.deliver_sealed(c2s, 1).unwrap(); // "two", now in order: accepted
            let last = w.history[s2c.i()][0].wire.len() - 1;
            w.flip(s2c, 0, 0, 0).unwrap(); // nonce bit
            w.flip(s2c, 0, last, 7).unwrap(); // tag bit
            w.truncate(s2c, 0, 0).unwrap();
            w.truncate(s2c, 0, 12).unwrap();
            w.truncate(s2c, 0, last).unwrap();
            w.forge(s2c, Forgery::OppositeDirection).unwrap();
            w.forge(s2c, Forgery::OtherVersion).unwrap();
            w.forge(s2c, Forgery::OtherSession).unwrap();
            w.deliver_next(s2c).unwrap(); // the genuine reply: accepted
            assert_eq!(w.accepted, [2, 1], "full={full} {version:?}");
            assert_eq!(w.sent, [2, 1]);
            w.drain().unwrap();
            assert_eq!(w.accepted, [3, 2]);
        }
    }
}
