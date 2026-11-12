//! Main proxy server implementation.
//!
//! Wire protocol (v2, KEM-based):
//!   ClientHello { version, client_random, kem_ek, falcon_vk, slh_dsa_vk, requested_key_size }
//!   ServerHello { version, server_random, falcon_vk, slh_dsa_vk, kem_ciphertext, transcript_sig }
//!
//! Both sides derive `transcript = SHA3(client_random ‖ server_random ‖ kem_ek
//! ‖ server_falcon_vk ‖ kem_ciphertext)` and `session_key = SHA3("pqtg-session-v2"
//! ‖ kem_ss ‖ transcript)`. v2 never mixes a QKD key: `handshake_v2` takes the
//! session with `into_session(None)`, since v2 cannot carry the `key_ID` a
//! client would need. Hybrid mode is v3 only (`handshake_v3`).
//!
//! Session layer (wire `2.1` and `3.2`, both handshakes): the session key is
//! expanded into one AES-256-GCM key per direction and each end accepts only
//! the next expected frame (`crypto::PqSession`, docs/KEY-SCHEDULE.md §5). The
//! server speaks exactly these two versions and refuses older peers at the
//! hello, since their session layer is not compatible.
//!
//! Which of the two a gateway accepts is a setting, `proxy.versions`, and it
//! is `["3.2"]` unless the operator says otherwise. The 2.1 hello is not
//! signed, so wire 2.1 is off by default; where it is switched on, only a
//! client key whose `authorized_keys` line carries `wire=2.1` may use it, and
//! that key is then refused on 3.2 (`check_wire_enabled`, `check_key_wire`).

use crate::{
    audit,
    auth::{Authenticator, AuthorizedKey},
    config::{Config, ProxyConfig, WIRE_2_1, WIRE_3_2},
    crypto::{
        derive_session_key, derive_v3_session_key, encapsulate_to, mix_keys, random_bytes,
        transcript_hash, transcript_hash_v3, HandshakeVersion, PqKeyExchange, PqSession, Role,
        FALCON_512_VK_LEN, MIN_SESSION_FRAME_BYTES, ML_KEM_768_EK_LEN, SLH_DSA_SHAKE128F_VK_LEN,
    },
    qkd_client::QkdClient,
    replay::{ReplayGuard, Verdict},
};
use anyhow::{anyhow, Context, Result};
use serde::{Deserialize, Serialize};
use std::net::SocketAddr;
use std::sync::{Arc, Mutex};
use std::time::{Instant, SystemTime, UNIX_EPOCH};
use tokio::io::{AsyncReadExt, AsyncWriteExt};
use tokio::net::TcpStream;
use tracing::{debug, error, info, warn};
use zeroize::Zeroizing;

#[derive(Clone)]
pub struct ProxyServer {
    config: Arc<Config>,
    qkd_client: Arc<QkdClient>,
    authenticator: Arc<Authenticator>,
    host_key: Arc<PqKeyExchange>,
    /// v3 hello replay guard (backlog B8): every admitted `client_random`
    /// inside the freshness window. Shared by all connections; the critical
    /// section is a hash lookup, and it is taken only after the signature has
    /// verified, so unauthenticated traffic never touches it.
    replay_guard: Arc<Mutex<ReplayGuard>>,
}

/// Seconds since the Unix epoch, the clock the v3 hello timestamp is compared
/// against. A clock before 1970 reads as 0, which fails the freshness check.
fn unix_now() -> u64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_secs())
        .unwrap_or(0)
}

/// Everything the server checks on a v3 hello AFTER the allow-list and BEFORE
/// spending anything on it (QKD allocation, encapsulation): proof of
/// possession (B6), freshness and first sight (B8). The signature is checked
/// first so only authenticated hellos reach the timestamp and the guard; the
/// guard lock is held for a hash lookup only. Pure over its inputs so it can be
/// tested without a socket.
pub fn admit_hello_v3(
    hello: &ClientHelloV3,
    now_unix: u64,
    max_skew_secs: u64,
    guard: &Mutex<ReplayGuard>,
    now: Instant,
) -> Result<()> {
    if !hello.verify_hello_sig()? {
        return Err(anyhow!(
            "hello signature does not verify under its falcon_vk"
        ));
    }
    let skew = hello.timestamp.abs_diff(now_unix);
    if skew > max_skew_secs {
        return Err(anyhow!(
            "hello timestamp is {skew} s from server time (max {max_skew_secs} s): stale, \
             future-dated, or a replay"
        ));
    }
    let mut guard = guard
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner());
    match guard.check_and_insert(hello.client_random, now) {
        Verdict::Fresh => Ok(()),
        Verdict::Replay => Err(anyhow!(
            "replayed ClientHello: this client_random was already admitted inside the window"
        )),
        Verdict::Full => Err(anyhow!(
            "hello replay cache full at {} entries: refusing rather than reopening the replay \
             window; raise proxy.hello_replay_cache_entries",
            guard.len()
        )),
    }
}

#[derive(Serialize, Deserialize)]
pub struct ClientHello {
    pub version: String,
    pub client_random: [u8; 32],
    /// ML-KEM-768 encapsulation key.
    pub kem_ek: Vec<u8>,
    /// Falcon-512 verification key (client identity, used for inner-channel signatures).
    pub falcon_vk: Vec<u8>,
    /// SLH-DSA-Shake128f verification key: a second identity key, matched
    /// against `authorized_keys` together with `falcon_vk`. Nothing is signed
    /// or verified with it.
    pub slh_dsa_vk: Vec<u8>,
    pub requested_key_size: usize,
}

#[derive(Clone, Serialize, Deserialize)]
pub struct ServerHello {
    pub version: String,
    pub server_random: [u8; 32],
    pub falcon_vk: Vec<u8>,
    pub slh_dsa_vk: Vec<u8>,
    /// ML-KEM-768 ciphertext (server's encapsulation against client's EK).
    pub kem_ciphertext: Vec<u8>,
    /// Falcon-512 signature over the transcript hash.
    pub transcript_sig: Vec<u8>,
}

// ── Wire protocol v3 (PROTOCOL-V3-QKD-KEYID.md) ─────────────────────────────
//
// v3 transports the ETSI 014 `key_ID` (a non-secret UUID) inside the signed
// ServerHello so a peer-SAE client can run `dec_keys` at its own KME and
// reproduce the QKD contribution — making hybrid mode interoperable — while
// binding key_ID / key_mode / master SAE-ID / key length under the Falcon-512
// transcript signature (no MITM key-id substitution, no silent downgrade).
// See docs/audit-vs-eprint-2025-1671.md for the attack model this closes.

/// Negotiated key mode, set authoritatively by the server and signed (§5).
#[derive(Clone, Copy, Debug, Serialize, Deserialize, PartialEq, Eq)]
pub enum KeyMode {
    Hybrid,
    PqcOnly,
}

impl KeyMode {
    /// Byte committed into the v3 transcript (spec §4): 0x01 Hybrid, 0x00 PqcOnly.
    pub fn wire_byte(self) -> u8 {
        match self {
            KeyMode::Hybrid => 0x01,
            KeyMode::PqcOnly => 0x00,
        }
    }
}

#[derive(Clone, Serialize, Deserialize)]
pub struct ClientHelloV3 {
    pub version: String,
    pub client_random: [u8; 32],
    pub kem_ek: Vec<u8>,
    pub falcon_vk: Vec<u8>,
    pub slh_dsa_vk: Vec<u8>,
    pub requested_key_size: usize,
    /// ETSI SAE-ID this client is registered as at its KME. Empty ⇒ no KME,
    /// request PQC-only. The server allocates the QKD key for this slave SAE.
    pub client_sae_id: String,
    /// True iff the client can run ETSI 014 `dec_keys` against a KME that
    /// shares keys with the server's KME. Drives QKD-vs-PQC negotiation.
    pub qkd_capable: bool,
    /// Client clock, seconds since the Unix epoch, under the signature. The
    /// server refuses a hello more than `proxy.hello_max_skew_secs` from its
    /// own clock, so a recorded hello is worthless after the window; inside
    /// it, the replay guard refuses a second sight (backlog B8).
    pub timestamp: u64,
    /// Falcon-512 signature by the client's identity key (the one `falcon_vk`
    /// names) over `crypto::client_hello_digest_v3` of every field above.
    /// Proves the sender holds the allow-listed key and binds THIS `kem_ek` to
    /// it, so an on-path attacker cannot present an authorized client's public
    /// keys with its own KEM key and obtain the server's session key (Verifpal
    /// finding F1, backlog B6; `formal/pqtg-handshake-clientauth.vp`). Verified
    /// before any QKD key is allocated, and again inside `respond_v3` so the
    /// type-state cannot produce a session from an unverified hello.
    pub hello_sig: Vec<u8>,
}

#[derive(Clone, Serialize, Deserialize)]
pub struct ServerHelloV3 {
    pub version: String,
    pub server_random: [u8; 32],
    pub falcon_vk: Vec<u8>,
    pub slh_dsa_vk: Vec<u8>,
    pub kem_ciphertext: Vec<u8>,
    /// Falcon-512 signature over the v3 transcript — which includes key_mode,
    /// qkd_key_id, master_sae_id and qkd_key_len (tamper-evident negotiation).
    pub transcript_sig: Vec<u8>,
    /// Negotiated key mode the server actually used (authoritative).
    pub key_mode: KeyMode,
    /// Present iff `key_mode == Hybrid`: the ETSI 014 key_ID (UUID) the client
    /// must fetch via `dec_keys` to reproduce the QKD contribution.
    pub qkd_key_id: Option<String>,
    /// Master SAE-ID for the client's `dec_keys` call (= this gateway's SAE).
    pub master_sae_id: String,
    /// Bytes of QKD material mixed (0 in PqcOnly) — transcript-bound.
    pub qkd_key_len: u32,
}

impl ClientHelloV3 {
    /// The digest `hello_sig` signs: every field except the signature itself.
    pub fn digest(&self) -> [u8; 32] {
        crate::crypto::client_hello_digest_v3(
            &self.client_random,
            self.timestamp,
            &self.kem_ek,
            &self.falcon_vk,
            &self.slh_dsa_vk,
            self.requested_key_size as u64,
            self.client_sae_id.as_bytes(),
            self.qkd_capable,
        )
    }

    /// Client side: sign the hello with the identity whose keys it carries.
    /// `identity.falcon_pk_bytes()` must equal `self.falcon_vk`; a signature by
    /// any other key could never verify under `falcon_vk` on the server.
    /// Library API for clients; the gateway binary itself never signs a hello,
    /// hence the bin-side allow.
    #[allow(dead_code)]
    pub fn sign(&mut self, identity: &PqKeyExchange) -> Result<()> {
        if identity.falcon_pk_bytes() != self.falcon_vk.as_slice() {
            return Err(anyhow!(
                "ClientHelloV3.falcon_vk does not match the signing identity"
            ));
        }
        self.hello_sig = identity.sign_transcript(&self.digest())?;
        Ok(())
    }

    /// Server side: does `hello_sig` verify under the hello's own `falcon_vk`?
    /// The caller has already checked that `falcon_vk` is allow-listed; this is
    /// the proof of possession that turns "names an authorized key" into "is
    /// the authorized client, and this is its KEM key".
    pub fn verify_hello_sig(&self) -> Result<bool> {
        if self.hello_sig.is_empty() {
            return Ok(false);
        }
        PqKeyExchange::verify_falcon(&self.digest(), &self.hello_sig, &self.falcon_vk)
    }
}

/// The handshake a hello's `version` selects. Exact match only: in this
/// protocol a minor bump has always meant an incompatible key schedule or
/// session layer (3.0, 3.1, 3.2; 2.0, 2.1), so a prefix match would let a peer
/// complete a handshake whose session it cannot speak. An older peer is
/// refused here, before authorization, encapsulation or any QKD allocation.
fn handshake_for_version(version: &str) -> Result<HandshakeVersion> {
    match version {
        PROTOCOL_VERSION => Ok(HandshakeVersion::V2),
        PROTOCOL_VERSION_V3 => Ok(HandshakeVersion::V3),
        other => Err(anyhow!(
            "Unsupported protocol version {other:?}: this gateway speaks {PROTOCOL_VERSION_V3} \
             and {PROTOCOL_VERSION} only. Peers on 3.1, 3.0 or 2.0 seal with one session key \
             in both directions and must upgrade (docs/KEY-SCHEDULE.md §5)"
        )),
    }
}

/// The name a wire version has on the wire, in `proxy.versions` and in the
/// `wire=` option of `authorized_keys`.
fn wire_name(version: HandshakeVersion) -> &'static str {
    match version {
        HandshakeVersion::V2 => PROTOCOL_VERSION,
        HandshakeVersion::V3 => PROTOCOL_VERSION_V3,
    }
}

/// Is this wire version switched on at this gateway (`proxy.versions`)? Runs
/// on the version field alone, before the hello is parsed any further: with
/// the default setting a 2.1 hello costs the gateway nothing, whoever sent it
/// and whatever keys it names.
fn check_wire_enabled(proxy: &ProxyConfig, version: HandshakeVersion) -> Result<()> {
    let name = wire_name(version);
    if proxy.accepts_wire(name) {
        return Ok(());
    }
    Err(anyhow!(
        "wire {name} is switched off on this gateway (proxy.versions = {:?}). A client that \
         cannot speak another version yet needs {name:?} in proxy.versions and wire={name} on \
         its authorized_keys line",
        proxy.versions
    ))
}

/// May this authorized key speak this wire version? Each key has one: 3.2, or
/// 2.1 when its `authorized_keys` line says `wire=2.1`. So a key that speaks
/// 3.2 cannot be named in a 2.1 hello, which carries no proof that its sender
/// holds the key, and a request signed in a 3.2 session has no 2.1 session to
/// be replayed in.
fn check_key_wire(key: &AuthorizedKey, version: HandshakeVersion) -> Result<()> {
    if key.wire == version {
        return Ok(());
    }
    Err(anyhow!(
        "client key {} is registered for wire {} and was presented in a wire {} hello",
        key.key_id,
        wire_name(key.wire),
        wire_name(version)
    ))
}

/// Say at startup which wire versions are on and how many keys can use each,
/// and warn about every combination in which a client will be refused or in
/// which wire 2.1 is open.
fn log_wire_policy(proxy: &ProxyConfig, authenticator: &Authenticator) {
    info!("Wire versions accepted: {:?}", proxy.versions);
    for version in [HandshakeVersion::V3, HandshakeVersion::V2] {
        let name = wire_name(version);
        let keys = authenticator.count_for_wire(version);
        match (proxy.accepts_wire(name), keys) {
            (true, 0) => warn!(
                "Wire {name} is switched on but no authorized key is registered for it: no \
                 client can use it"
            ),
            (false, 0) => {}
            (false, n) => warn!(
                "{n} authorized key(s) are registered for wire {name}, which is switched off \
                 (proxy.versions): those clients will be refused"
            ),
            (true, n) => info!("Wire {name}: {n} authorized key(s)"),
        }
    }
    if proxy.accepts_wire(WIRE_2_1) {
        warn!(
            "Wire {WIRE_2_1} is switched ON. Its hello is not signed: anyone who knows the \
             public keys of a client marked wire={WIRE_2_1} can open a session in its name, and \
             a key request that client once signed is accepted again in such a session \
             (docs/THREAT-MODEL.md, L6). Remove {WIRE_2_1:?} from proxy.versions once those \
             clients speak {WIRE_3_2}"
        );
    }
}

/// Minimal prefix decode to pick the struct shape before full deserialization.
/// bincode is not self-describing, but it encodes the leading `version:
/// String` first in both v2 and v3 hellos, so a peek at that one field is
/// reliable (spec §8).
#[derive(Deserialize)]
struct VersionPeek {
    version: String,
}

#[derive(Serialize, Deserialize)]
pub struct KeyRequest {
    pub key_id: String,
    pub size: usize,
    pub purpose: String,
}

#[derive(Serialize, Deserialize)]
pub struct KeyResponse {
    pub key_id: String,
    pub key_data: Vec<u8>,
    pub metadata: KeyMetadata,
}

#[derive(Serialize, Deserialize)]
pub struct KeyMetadata {
    pub algorithm: String,
    pub created_at: i64,
    pub expires_at: Option<i64>,
    pub qkd_enhanced: bool,
}

/// 2.1: the v2 handshake is unchanged, but its session key is now expanded
/// into one record key per direction with strict receive sequencing
/// (`crypto::PqSession`). A 2.0 peer seals with the session key itself, in
/// both directions, so it is refused at the hello.
const PROTOCOL_VERSION: &str = WIRE_2_1;
/// 3.2: the v3 handshake and key schedule of 3.1 are unchanged, and the
/// session layer changes as for 2.1. History: 3.1 moved the v3 hashes and key
/// schedule to the domain tree and keyed chain in `crate::kdf` (backlog
/// B2/B3); 3.0 used flat labels. Neither is accepted.
const PROTOCOL_VERSION_V3: &str = WIRE_3_2;
const MAX_HELLO_BYTES: usize = 16 * 1024;
const MAX_REQUEST_BYTES: usize = 1024 * 1024;
/// Sanity cap on the client-supplied SAE-ID (ETSI 014 SAE_IDs are short
/// logical labels; anything longer is malformed or hostile).
use crate::qkd_client::MAX_SAE_ID_BYTES;

// ── Type-state server handshake ─────────────────────────────────────────────
//
// The PQ handshake is modelled as a state machine whose states are types.
// A `PqSession` — the only thing that can encrypt/decrypt application data —
// can be produced *solely* by `ServerHandshake::<HelloAccepted>::into_session`.
// You therefore cannot send or receive data before the handshake has been
// completed in order (encapsulate → transcript → sign → derive). The ordering
// is enforced by the compiler, not by convention.

/// Initial handshake state: no client hello processed yet.
pub struct AwaitingHello;

/// Reached after a client hello has been accepted: the `ServerHello` is ready
/// to send and the shared secret / transcript are committed.
pub struct HelloAccepted {
    server_hello: ServerHello,
    pqc_secret: [u8; 32],
    transcript: [u8; 32],
    client_falcon_vk: Vec<u8>,
}

/// Server-side PQ handshake, parameterised by protocol state `S`.
pub struct ServerHandshake<S> {
    state: S,
}

impl ServerHandshake<AwaitingHello> {
    pub fn new() -> Self {
        Self {
            state: AwaitingHello,
        }
    }

    /// Encapsulate against the (already length-validated, authorized) client
    /// hello, build and sign the transcript, and prepare the `ServerHello`.
    /// Consumes `self`; on success advances to `HelloAccepted`.
    pub fn respond(
        self,
        client_hello: &ClientHello,
        host_key: &PqKeyExchange,
    ) -> Result<ServerHandshake<HelloAccepted>> {
        let (kem_ciphertext, pqc_secret) = encapsulate_to(&client_hello.kem_ek)?;
        let server_random = random_bytes::<32>();
        let transcript = transcript_hash(
            &client_hello.client_random,
            &server_random,
            &client_hello.kem_ek,
            host_key.falcon_pk_bytes(),
            &kem_ciphertext,
        );
        let transcript_sig = host_key.sign_transcript(&transcript)?;
        let server_hello = ServerHello {
            version: PROTOCOL_VERSION.to_string(),
            server_random,
            falcon_vk: host_key.falcon_pk_bytes().to_vec(),
            slh_dsa_vk: host_key.slh_dsa_pk_bytes().to_vec(),
            kem_ciphertext,
            transcript_sig,
        };
        Ok(ServerHandshake {
            state: HelloAccepted {
                server_hello,
                pqc_secret,
                transcript,
                client_falcon_vk: client_hello.falcon_vk.clone(),
            },
        })
    }
}

impl ServerHandshake<HelloAccepted> {
    /// The `ServerHello` to write to the wire. Only exists in this state, so
    /// it cannot be sent before a client hello has been accepted.
    pub fn server_hello(&self) -> &ServerHello {
        &self.state.server_hello
    }

    /// Derive the session — optionally mixing in one-time QKD key material —
    /// and yield the established `PqSession` plus the client's Falcon vk.
    /// Consumes `self`: this is the *only* constructor of a live session, so
    /// no data can flow before the handshake is complete.
    ///
    /// The handshake cannot be touched after the session is taken:
    ///
    /// ```compile_fail,E0382
    /// use pq_qkd_proxy::proxy::ServerHandshake;
    /// use pq_qkd_proxy::{ClientHello, PqKeyExchange};
    /// fn handshake(hello: &ClientHello, host: &PqKeyExchange) {
    ///     let hs = ServerHandshake::new().respond(hello, host).unwrap();
    ///     let _session = hs.into_session(None); // consumes the handshake
    ///     let _ = hs.server_hello(); // error[E0382]: borrow of moved value
    /// }
    /// ```
    pub fn into_session(self, qkd_material: Option<&[u8]>) -> Result<(PqSession, Vec<u8>)> {
        let s = self.state;
        let final_secret = match qkd_material {
            Some(m) => mix_keys(m, &s.pqc_secret),
            None => s.pqc_secret,
        };
        let session_key = derive_session_key(&final_secret, &s.transcript);
        let session = PqSession::new(
            &session_key,
            HandshakeVersion::V2,
            Role::Server,
            random_bytes::<32>(),
            s.client_falcon_vk.clone(),
        )?;
        Ok((session, s.client_falcon_vk))
    }
}

impl Default for ServerHandshake<AwaitingHello> {
    fn default() -> Self {
        Self::new()
    }
}

// ── v3 type-state ────────────────────────────────────────────────────────────
//
// The v3 ordering difference vs v2 is load-bearing: the QKD key is allocated
// BEFORE the transcript is built, so its key_ID (and the negotiated mode) sit
// under the Falcon-512 signature. In v2 the key was fetched after ServerHello
// was already on the wire — which is exactly why its key_ID could never be
// transcript-bound, and why v2 hybrid mode could not interoperate.

/// Reached after a v3 client hello has been accepted and QKD negotiation has
/// resolved: the signed `ServerHelloV3` is ready and the secrets are committed.
pub struct HelloAcceptedV3 {
    server_hello: ServerHelloV3,
    pqc_secret: [u8; 32],
    transcript: [u8; 32],
    client_falcon_vk: Vec<u8>,
    qkd_material: Option<Zeroizing<Vec<u8>>>,
}

impl ServerHandshake<AwaitingHello> {
    /// v3 responder. `qkd` is the outcome of negotiation: `Some((key_ID,
    /// material))` for Hybrid (already allocated for the client's slave SAE
    /// via `enc_keys`), `None` for PqcOnly. The key mode, key_ID, master
    /// SAE-ID and key length are all committed into the transcript and
    /// therefore signed — tamper-evident negotiation, no silent downgrade.
    pub fn respond_v3(
        self,
        client_hello: &ClientHelloV3,
        host_key: &PqKeyExchange,
        qkd: Option<(String, Zeroizing<Vec<u8>>)>,
        master_sae_id: &str,
    ) -> Result<ServerHandshake<HelloAcceptedV3>> {
        // Proof of possession before encapsulation. `handshake_v3` checks this
        // earlier too (before the QKD allocation); repeating it here means the
        // type-state itself cannot yield a session from an unverified hello.
        if !client_hello.verify_hello_sig()? {
            return Err(anyhow!(
                "ClientHelloV3.hello_sig does not verify under falcon_vk; refusing to encapsulate"
            ));
        }
        let (kem_ciphertext, pqc_secret) = encapsulate_to(&client_hello.kem_ek)?;
        let server_random = random_bytes::<32>();
        let (key_mode, qkd_key_id, qkd_key_len, qkd_material) = match qkd {
            Some((kid, material)) => {
                let len = u32::try_from(material.len())
                    .map_err(|_| anyhow!("QKD key too large for u32 length"))?;
                (KeyMode::Hybrid, Some(kid), len, Some(material))
            }
            None => (KeyMode::PqcOnly, None, 0u32, None),
        };
        let transcript = transcript_hash_v3(
            &client_hello.client_random,
            &server_random,
            &client_hello.kem_ek,
            host_key.falcon_pk_bytes(),
            &kem_ciphertext,
            key_mode.wire_byte(),
            qkd_key_id.as_deref().unwrap_or("").as_bytes(),
            master_sae_id.as_bytes(),
            qkd_key_len,
        );
        let transcript_sig = host_key.sign_transcript(&transcript)?;
        let server_hello = ServerHelloV3 {
            version: PROTOCOL_VERSION_V3.to_string(),
            server_random,
            falcon_vk: host_key.falcon_pk_bytes().to_vec(),
            slh_dsa_vk: host_key.slh_dsa_pk_bytes().to_vec(),
            kem_ciphertext,
            transcript_sig,
            key_mode,
            qkd_key_id,
            master_sae_id: master_sae_id.to_string(),
            qkd_key_len,
        };
        Ok(ServerHandshake {
            state: HelloAcceptedV3 {
                server_hello,
                pqc_secret,
                transcript,
                client_falcon_vk: client_hello.falcon_vk.clone(),
                qkd_material,
            },
        })
    }
}

impl ServerHandshake<HelloAcceptedV3> {
    /// The signed `ServerHelloV3` to write to the wire.
    pub fn server_hello(&self) -> &ServerHelloV3 {
        &self.state.server_hello
    }

    /// Derive the v3 session through the keyed chain
    /// (`crypto::derive_v3_session_key`): KEM secret, then the QKD bytes in
    /// Hybrid mode, then the transcript, which commits the key_ID, mode,
    /// SAE-ID and length (docs/audit-vs-eprint-2025-1671.md). Consumes
    /// `self`; the only constructor of a live v3 session.
    pub fn into_session(self) -> Result<(PqSession, Vec<u8>)> {
        let s = self.state;
        let session_key = derive_v3_session_key(
            &s.pqc_secret,
            s.qkd_material.as_ref().map(|m| m.as_slice()),
            &s.transcript,
        );
        let session = PqSession::new(
            &session_key,
            HandshakeVersion::V3,
            Role::Server,
            random_bytes::<32>(),
            s.client_falcon_vk.clone(),
        )?;
        Ok((session, s.client_falcon_vk))
    }
}

impl ProxyServer {
    // Library API and tests; the binary calls `with_identity`.
    #[allow(dead_code)]
    pub async fn new(config: Arc<Config>) -> Result<Self> {
        let (host_key, _) = Self::load_identity(&config.security.proxy_private_key)?;
        Self::with_identity(config, Arc::new(host_key)).await
    }

    /// Build the server around an identity the caller loaded, so the binary
    /// shares one copy of the secret keys with the audit-log signer.
    pub async fn with_identity(config: Arc<Config>, host_key: Arc<PqKeyExchange>) -> Result<Self> {
        let qkd_client = QkdClient::new(&config)?;
        let authenticator = Authenticator::new(&config)?;
        log_wire_policy(&config.proxy, &authenticator);
        // The guard must remember a hello for the whole interval in which its
        // timestamp is acceptable, which is one second more than 2 × skew:
        // `for_skew` gives the window (see replay.rs).
        let replay_guard = Arc::new(Mutex::new(ReplayGuard::for_skew(
            config.proxy.hello_max_skew_secs,
            config.proxy.hello_replay_cache_entries,
        )));
        Ok(Self {
            config,
            qkd_client: Arc::new(qkd_client),
            authenticator: Arc::new(authenticator),
            host_key,
            replay_guard,
        })
    }

    /// Load the persisted identity file if present (`true`); otherwise
    /// generate a fresh ephemeral identity and warn loudly (`false`).
    /// Production deployments MUST run `--generate-keys` once to create a
    /// stable identity, since regenerating on every start invalidates
    /// client-side vk pinning (issue #2) and leaves the audit log unsigned.
    pub fn load_identity(path: &str) -> Result<(PqKeyExchange, bool)> {
        match PqKeyExchange::load_if_present(path)? {
            Some(identity) => {
                info!("Loaded persisted PQTG identity from {}", path);
                Ok((identity, true))
            }
            None => {
                warn!(
                    "No persisted identity at {}; generating ephemeral identity. \
                     This is acceptable for development but MUST NOT be used \
                     in production — restart-stable identity is required for \
                     client vk pinning. Run `--generate-keys` to fix.",
                    path
                );
                Ok((PqKeyExchange::new()?, false))
            }
        }
    }

    pub async fn check_vendor_api(&self) -> Result<()> {
        info!("Checking vendor QKD API connectivity...");
        match self.qkd_client.check_connectivity().await {
            Ok(()) => {
                info!("Successfully connected to vendor QKD API");
                Ok(())
            }
            Err(e) => {
                error!("Failed to connect to vendor QKD API: {}", e);
                Err(e)
            }
        }
    }

    pub async fn handle_connection(
        &self,
        mut stream: TcpStream,
        peer_addr: SocketAddr,
    ) -> Result<()> {
        disable_nagle(&stream, &peer_addr);
        audit::log_connection(&peer_addr);
        let timeout = tokio::time::Duration::from_secs(self.config.proxy.connection_timeout);
        let (session, client_falcon_vk) =
            tokio::time::timeout(timeout, self.perform_handshake(&mut stream, &peer_addr))
                .await
                .context("Handshake timeout")?
                .context("Handshake failed")?;
        info!("Established PQ session with {}", peer_addr);
        let _ = client_falcon_vk; // currently unused; reserved for inner auth
        self.handle_session(stream, session, peer_addr).await
    }

    async fn perform_handshake(
        &self,
        stream: &mut TcpStream,
        peer_addr: &SocketAddr,
    ) -> Result<(PqSession, Vec<u8>)> {
        // Read the hello frame ONCE as raw bytes. bincode is not
        // self-describing, so peek the leading `version` string to pick the
        // struct shape (PROTOCOL-V3-QKD-KEYID.md §8), then branch on major.
        let hello_bytes = read_frame_bytes(stream, MAX_HELLO_BYTES).await?;
        let peek: VersionPeek = bincode::deserialize(&hello_bytes)
            .map_err(|_| anyhow!("Malformed hello: cannot read protocol version"))?;
        let version = handshake_for_version(&peek.version).inspect_err(|e| {
            warn!("Refused hello from {}: {}", peer_addr, e);
        })?;
        check_wire_enabled(&self.config.proxy, version).inspect_err(|e| {
            warn!("Refused hello from {}: {}", peer_addr, e);
        })?;
        match version {
            HandshakeVersion::V3 => self.handshake_v3(stream, peer_addr, &hello_bytes).await,
            HandshakeVersion::V2 => self.handshake_v2(stream, peer_addr, &hello_bytes).await,
        }
    }

    /// Shared ClientHello validation (issue #5) + authorization (issue #1).
    /// Authorization is fail-closed and runs before any encapsulation so an
    /// unauthorized peer cannot exhaust crypto budget — or, in v3, consume
    /// KMS keys (spec §7, DoS note).
    fn validate_and_authorize(
        &self,
        version: HandshakeVersion,
        kem_ek: &[u8],
        falcon_vk: &[u8],
        slh_dsa_vk: &[u8],
        peer_addr: &SocketAddr,
    ) -> Result<()> {
        if kem_ek.len() != ML_KEM_768_EK_LEN {
            return Err(anyhow!(
                "ClientHello.kem_ek wrong size: expected {} bytes, got {}",
                ML_KEM_768_EK_LEN,
                kem_ek.len()
            ));
        }
        if falcon_vk.len() != FALCON_512_VK_LEN {
            return Err(anyhow!(
                "ClientHello.falcon_vk wrong size: expected {} bytes, got {}",
                FALCON_512_VK_LEN,
                falcon_vk.len()
            ));
        }
        if slh_dsa_vk.len() != SLH_DSA_SHAKE128F_VK_LEN {
            return Err(anyhow!(
                "ClientHello.slh_dsa_vk wrong size: expected {} bytes, got {}",
                SLH_DSA_SHAKE128F_VK_LEN,
                slh_dsa_vk.len()
            ));
        }
        match self.authenticator.verify_client(falcon_vk, slh_dsa_vk) {
            Ok(auth_key) => {
                // An authorized key on the wrong wire version is refused like
                // an unknown key, and recorded: it is either a client that has
                // not been moved in `authorized_keys`, or someone naming a 3.2
                // client in a 2.1 hello.
                if let Err(e) = check_key_wire(auth_key, version) {
                    audit::log_auth_failure(peer_addr, &e.to_string());
                    warn!("Rejected client {}: {}", peer_addr, e);
                    return Err(e);
                }
                debug!(
                    "Client authorized: key_id={} wire={} peer={}",
                    auth_key.key_id,
                    wire_name(version),
                    peer_addr
                );
                Ok(())
            }
            Err(e) => {
                audit::log_auth_failure(peer_addr, &e.to_string());
                warn!("Rejected unauthorized client {}: {}", peer_addr, e);
                Err(anyhow!("Client not in authorized_keys"))
            }
        }
    }

    /// Legacy v2 flow. QKD mixing is intentionally NOT performed for v2
    /// clients: v2 cannot transport the key_ID, so a mixed session could
    /// never be reproduced by an external client (the v2 interop hole,
    /// PROTOCOL-V3-QKD-KEYID.md §1). v2 is therefore PQC-only — honestly —
    /// and hybrid requires wire v3.
    async fn handshake_v2(
        &self,
        stream: &mut TcpStream,
        peer_addr: &SocketAddr,
        hello_bytes: &[u8],
    ) -> Result<(PqSession, Vec<u8>)> {
        let client_hello: ClientHello = bincode::deserialize(hello_bytes)?;
        self.validate_and_authorize(
            HandshakeVersion::V2,
            &client_hello.kem_ek,
            &client_hello.falcon_vk,
            &client_hello.slh_dsa_vk,
            peer_addr,
        )?;
        let handshake = ServerHandshake::new().respond(&client_hello, &self.host_key)?;
        write_framed(stream, handshake.server_hello()).await?;
        debug!(
            "v2 client {}: PQC-only session (hybrid requires wire protocol v3)",
            peer_addr
        );
        handshake.into_session(None)
    }

    /// v3 flow (PROTOCOL-V3-QKD-KEYID.md §5-§6): negotiate the key mode and
    /// allocate the QKD key BEFORE building the transcript, so the key_ID and
    /// mode are signed. Failure to allocate ⇒ PqcOnly, signaled and signed —
    /// the client's local policy decides whether to accept the downgrade.
    async fn handshake_v3(
        &self,
        stream: &mut TcpStream,
        peer_addr: &SocketAddr,
        hello_bytes: &[u8],
    ) -> Result<(PqSession, Vec<u8>)> {
        let client_hello: ClientHelloV3 = bincode::deserialize(hello_bytes)?;
        if client_hello.client_sae_id.len() > MAX_SAE_ID_BYTES {
            return Err(anyhow!(
                "ClientHello.client_sae_id too long: {} bytes (max {})",
                client_hello.client_sae_id.len(),
                MAX_SAE_ID_BYTES
            ));
        }
        // An empty SAE ID means "no QKD". Any other value will become a path
        // segment of the key manager URL, so a malformed one refuses the
        // hello here. It must not reach the key manager, and it must not
        // turn into a quiet PqcOnly fallback.
        if !client_hello.client_sae_id.is_empty() {
            crate::qkd_client::validate_sae_id(&client_hello.client_sae_id)
                .map_err(|e| anyhow!("ClientHello.client_sae_id refused: {e}"))?;
        }
        self.validate_and_authorize(
            HandshakeVersion::V3,
            &client_hello.kem_ek,
            &client_hello.falcon_vk,
            &client_hello.slh_dsa_vk,
            peer_addr,
        )?;

        // ── Admission: possession (B6), freshness and first sight (B8) ──────
        // After the allow-list, before any QKD allocation or encapsulation.
        // The allow-list proves the hello NAMES an authorized key; the
        // signature proves the sender HOLDS it and bound this kem_ek to it
        // (Verifpal F1); the signed timestamp plus the replay guard make a
        // recorded hello worthless, so a copy of one cannot drain QKD keys.
        if let Err(e) = admit_hello_v3(
            &client_hello,
            unix_now(),
            self.config.proxy.hello_max_skew_secs,
            &self.replay_guard,
            Instant::now(),
        ) {
            audit::log_auth_failure(peer_addr, &e.to_string());
            warn!("Rejected client {}: {}", peer_addr, e);
            return Err(anyhow!("ClientHello refused: {e}"));
        }

        // ── QKD negotiation (spec §5) — after authorization, before transcript
        let want_qkd = client_hello.qkd_capable && !client_hello.client_sae_id.is_empty();
        let qkd = if want_qkd {
            match self
                .qkd_client
                .get_key_for_sae(&client_hello.client_sae_id, 32)
                .await
            {
                Ok(key) => {
                    audit::log_qkd_key_used(peer_addr, key.key_id());
                    let kid = key.key_id().to_string();
                    // Consume the key: QKD material is one-time, used exactly once.
                    Some((kid, key.into_material()))
                }
                Err(e) => {
                    warn!(
                        "QKD unavailable for slave SAE {:?} ({e}); negotiating PqcOnly",
                        client_hello.client_sae_id
                    );
                    None
                }
            }
        } else {
            None
        };

        // The gateway's own SAE identity, announced so the client can run
        // `dec_keys(master_sae_id, [key_ID])` at its KME. Reuses the
        // `qkd.default_master_sae_id` config value as this gateway's label.
        let master_sae_id = self.config.qkd.default_master_sae_id.clone();

        let handshake = ServerHandshake::new().respond_v3(
            &client_hello,
            &self.host_key,
            qkd,
            &master_sae_id,
        )?;
        write_framed(stream, handshake.server_hello()).await?;
        info!(
            "v3 session with {}: key_mode={:?}",
            peer_addr,
            handshake.server_hello().key_mode
        );
        handshake.into_session()
    }

    async fn handle_session(
        &self,
        mut stream: TcpStream,
        mut session: PqSession,
        peer_addr: SocketAddr,
    ) -> Result<()> {
        loop {
            let mut len_buf = [0u8; 4];
            match stream.read_exact(&mut len_buf).await {
                Ok(_) => {}
                Err(e) if e.kind() == std::io::ErrorKind::UnexpectedEof => {
                    debug!("Client disconnected");
                    break;
                }
                Err(e) => return Err(e.into()),
            }
            let len = u32::from_be_bytes(len_buf) as usize;
            if len < MIN_SESSION_FRAME_BYTES {
                return Err(anyhow!(
                    "Request too small: {len} bytes (minimum {MIN_SESSION_FRAME_BYTES})"
                ));
            }
            if len > MAX_REQUEST_BYTES {
                return Err(anyhow!("Request too large: {len} bytes"));
            }
            let mut encrypted = vec![0u8; len];
            stream.read_exact(&mut encrypted).await?;

            // Opens under the client-to-server key and only at the next
            // expected counter: a replayed, reordered or reflected frame ends
            // the connection here, before any key is requested.
            let request_bytes = session.decrypt_and_verify(&encrypted)?;
            let request: KeyRequest = bincode::deserialize(&request_bytes)?;
            audit::log_key_request(&peer_addr, &request.key_id, request.size);

            let response = self.process_key_request(request).await?;
            let response_bytes = bincode::serialize(&response)?;
            let encrypted_response =
                session.sign_and_encrypt(&response_bytes, self.host_key.falcon_signing_key())?;

            write_frame(&mut stream, &encrypted_response).await?;
        }
        Ok(())
    }

    async fn process_key_request(&self, request: KeyRequest) -> Result<KeyResponse> {
        if request.size > self.config.qkd.max_key_size {
            return Err(anyhow!("Requested key size exceeds maximum"));
        }
        let qkd_key = self.qkd_client.get_key(request.size).await?;
        let key_id = qkd_key.key_id().to_string();
        Ok(KeyResponse {
            key_id,
            key_data: qkd_key.into_material().to_vec(),
            metadata: KeyMetadata {
                algorithm: "QKD-BB84".to_string(),
                created_at: chrono::Utc::now().timestamp(),
                expires_at: None,
                qkd_enhanced: true,
            },
        })
    }
}

/// Read one length-prefixed frame as raw bytes (caller picks the struct
/// shape — needed for the v2/v3 version peek).
async fn read_frame_bytes(stream: &mut TcpStream, max: usize) -> Result<Vec<u8>> {
    let mut len_buf = [0u8; 4];
    stream.read_exact(&mut len_buf).await?;
    let len = u32::from_be_bytes(len_buf) as usize;
    if len > max {
        return Err(anyhow!("Frame too large: {len} > {max}"));
    }
    let mut buf = vec![0u8; len];
    stream.read_exact(&mut buf).await?;
    Ok(buf)
}

#[allow(dead_code)]
async fn read_framed<T: for<'de> Deserialize<'de>>(
    stream: &mut TcpStream,
    max: usize,
) -> Result<T> {
    let buf = read_frame_bytes(stream, max).await?;
    Ok(bincode::deserialize(&buf)?)
}

async fn write_framed<T: Serialize>(stream: &mut TcpStream, msg: &T) -> Result<()> {
    write_frame(stream, &bincode::serialize(msg)?).await
}

/// Write one frame (`be32(len) ‖ payload`) in a single write. Written as two,
/// the payload of a small frame waited for the ACK of the length prefix, which
/// the client's delayed-ACK timer holds: about 40 ms per key request on Linux.
async fn write_frame(stream: &mut TcpStream, payload: &[u8]) -> Result<()> {
    let mut frame = Vec::with_capacity(4 + payload.len());
    frame.extend_from_slice(&(payload.len() as u32).to_be_bytes());
    frame.extend_from_slice(payload);
    stream.write_all(&frame).await?;
    stream.flush().await?;
    Ok(())
}

/// Disable Nagle's algorithm on a gateway connection, as the relay does
/// (`relay.rs::configure_socket`): every message is a small frame, and Nagle
/// can hold one back until the client acknowledges the previous segment. Best
/// effort: a socket that refuses still works, so a failure is only logged.
fn disable_nagle(stream: &TcpStream, peer: &SocketAddr) {
    if let Err(e) = stream.set_nodelay(true) {
        warn!("could not disable Nagle on the connection from {peer}: {e}");
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::crypto::EphemeralKemKey;
    use std::time::Duration;

    async fn loopback_pair() -> (TcpStream, TcpStream) {
        let listener = tokio::net::TcpListener::bind("127.0.0.1:0").await.unwrap();
        let addr = listener.local_addr().unwrap();
        let accept = tokio::spawn(async move { listener.accept().await.unwrap().0 });
        let client = TcpStream::connect(addr).await.unwrap();
        (accept.await.unwrap(), client)
    }

    #[tokio::test]
    async fn gateway_connections_disable_nagle() {
        // With Nagle on, each key request took about 44 ms on Linux (the
        // two-board kit, 2026-10-29) against about 2 ms on macOS.
        let (server, _client) = loopback_pair().await;
        disable_nagle(&server, &server.peer_addr().unwrap());
        assert!(server.nodelay().unwrap(), "Nagle must be off");
    }

    #[tokio::test]
    async fn a_frame_is_its_length_then_its_payload() {
        let (mut server, mut client) = loopback_pair().await;
        write_frame(&mut server, b"payload").await.unwrap();
        let mut got = [0u8; 11];
        client.read_exact(&mut got).await.unwrap();
        assert_eq!(&got[..4], &7u32.to_be_bytes());
        assert_eq!(&got[4..], b"payload");
    }

    /// End-to-end check of the type-state server handshake (previously the
    /// handshake path had no unit coverage). Drives the state machine the way
    /// `perform_handshake` does, then verifies a client can (a) verify the
    /// server's transcript signature and (b) derive the *same* session key and
    /// decrypt server traffic — proving key agreement.
    #[test]
    fn server_handshake_binds_transcript_and_agrees_on_session_key() {
        let host_key = PqKeyExchange::new().unwrap();

        // Client materials.
        let client_kem = EphemeralKemKey::new().unwrap();
        let client_ek = client_kem.ek_bytes.clone();
        let client_random = random_bytes::<32>();
        let client_id = PqKeyExchange::new().unwrap();
        let hello = ClientHello {
            version: PROTOCOL_VERSION.to_string(),
            client_random,
            kem_ek: client_ek.clone(),
            falcon_vk: client_id.falcon_pk_bytes().to_vec(),
            slh_dsa_vk: client_id.slh_dsa_pk_bytes().to_vec(),
            requested_key_size: 32,
        };

        // Server side: AwaitingHello -> HelloAccepted -> Established session.
        let handshake = ServerHandshake::new().respond(&hello, &host_key).unwrap();
        let server_hello = handshake.server_hello().clone();
        let (mut server_session, returned_vk) = handshake.into_session(None).unwrap();
        assert_eq!(returned_vk, hello.falcon_vk);

        // The server's transcript signature must verify under its Falcon vk.
        let transcript = transcript_hash(
            &client_random,
            &server_hello.server_random,
            &client_ek,
            &server_hello.falcon_vk,
            &server_hello.kem_ciphertext,
        );
        assert!(
            PqKeyExchange::verify_falcon(
                &transcript,
                &server_hello.transcript_sig,
                &server_hello.falcon_vk
            )
            .unwrap(),
            "server transcript signature must verify"
        );

        // Client re-derives the session key (single-use ephemeral key) and
        // exchanges a request and a response with the server, which proves
        // both sides agree on both direction keys.
        let client_ss = client_kem
            .decapsulate(&server_hello.kem_ciphertext)
            .unwrap();
        let client_session_key = derive_session_key(&client_ss, &transcript);
        let mut client_session = PqSession::new(
            &client_session_key,
            HandshakeVersion::V2,
            Role::Client,
            random_bytes::<32>(),
            server_hello.falcon_vk,
        )
        .unwrap();
        request_response(
            &mut client_session,
            &mut server_session,
            b"quantum-safe hello",
        );
    }

    /// One request from the client end and one response from the server end,
    /// each opened by the other: the session loop of `handle_session`, without
    /// the socket.
    fn request_response(client: &mut PqSession, server: &mut PqSession, msg: &[u8]) {
        let (ct, nonce) = client.encrypt(msg).unwrap();
        assert_eq!(server.decrypt(&ct, &nonce).unwrap(), msg);
        let (ct, nonce) = server.encrypt(msg).unwrap();
        assert_eq!(client.decrypt(&ct, &nonce).unwrap(), msg);
    }

    /// Exact version match. The two current versions select their handshake;
    /// every older one is refused, including the ones whose prefix the server
    /// used to accept.
    #[test]
    fn only_wire_2_1_and_3_2_are_accepted() {
        assert_eq!(handshake_for_version("2.1").unwrap(), HandshakeVersion::V2);
        assert_eq!(handshake_for_version("3.2").unwrap(), HandshakeVersion::V3);
        for old in [
            "2.0", "3.0", "3.1", "2.", "3.", "3.2.0", "4.0", "relay-4", "",
        ] {
            let err = handshake_for_version(old).unwrap_err();
            assert!(
                err.to_string().contains("Unsupported protocol version"),
                "{old:?} must be refused, got: {err}"
            );
        }
        assert_eq!(PROTOCOL_VERSION, "2.1");
        assert_eq!(PROTOCOL_VERSION_V3, "3.2");
    }

    // ── which of the two a gateway accepts (`proxy.versions`, `wire=`) ───────

    fn proxy_config(versions: &[&str]) -> ProxyConfig {
        let mut proxy = Config::default().proxy;
        proxy.versions = versions.iter().map(|v| v.to_string()).collect();
        proxy
    }

    fn authorized_key(wire: HandshakeVersion) -> AuthorizedKey {
        AuthorizedKey {
            key_id: "key-0".to_string(),
            falcon_public_key: vec![1u8; FALCON_512_VK_LEN],
            sphincs_public_key: vec![2u8; SLH_DSA_SHAKE128F_VK_LEN],
            permissions: vec!["read".to_string()],
            comment: String::new(),
            wire,
        }
    }

    /// With the default setting a 2.1 hello is refused on its version alone,
    /// and a 3.2 hello passes. The refusal says what to change.
    #[test]
    fn wire_2_1_is_refused_unless_the_gateway_lists_it() {
        let default = Config::default().proxy;
        check_wire_enabled(&default, HandshakeVersion::V3).expect("3.2 is on by default");
        let err =
            check_wire_enabled(&default, HandshakeVersion::V2).expect_err("2.1 is off by default");
        let text = err.to_string();
        assert!(text.contains("wire 2.1 is switched off"), "got: {text}");
        assert!(text.contains("proxy.versions"), "got: {text}");
        assert!(text.contains("wire=2.1"), "got: {text}");

        let both = proxy_config(&["3.2", "2.1"]);
        check_wire_enabled(&both, HandshakeVersion::V3).unwrap();
        check_wire_enabled(&both, HandshakeVersion::V2).unwrap();

        let legacy_only = proxy_config(&["2.1"]);
        check_wire_enabled(&legacy_only, HandshakeVersion::V2).unwrap();
        let err = check_wire_enabled(&legacy_only, HandshakeVersion::V3).unwrap_err();
        assert!(
            err.to_string().contains("wire 3.2 is switched off"),
            "{err}"
        );

        // A list set by hand to nothing, or to a version the gateway does not
        // speak, switches everything off. It never switches something on.
        for versions in [&[][..], &["3.1"][..], &["2.0", "4.0"][..]] {
            let odd = proxy_config(versions);
            assert!(check_wire_enabled(&odd, HandshakeVersion::V2).is_err());
            assert!(check_wire_enabled(&odd, HandshakeVersion::V3).is_err());
        }
    }

    /// A key speaks one wire version. A 3.2 key named in a 2.1 hello is
    /// refused, and so is a 2.1 key in a 3.2 hello.
    #[test]
    fn a_key_is_refused_on_the_wire_version_it_is_not_registered_for() {
        let modern = authorized_key(HandshakeVersion::V3);
        check_key_wire(&modern, HandshakeVersion::V3).unwrap();
        let err = check_key_wire(&modern, HandshakeVersion::V2).unwrap_err();
        assert!(
            err.to_string()
                .contains("registered for wire 3.2 and was presented in a wire 2.1 hello"),
            "got: {err}"
        );

        let legacy = authorized_key(HandshakeVersion::V2);
        check_key_wire(&legacy, HandshakeVersion::V2).unwrap();
        let err = check_key_wire(&legacy, HandshakeVersion::V3).unwrap_err();
        assert!(
            err.to_string()
                .contains("registered for wire 2.1 and was presented in a wire 3.2 hello"),
            "got: {err}"
        );
    }

    /// The version strings of the setting, of the `wire=` option and of the
    /// hello are the same strings.
    #[test]
    fn the_setting_and_the_hello_name_versions_the_same_way() {
        assert_eq!(wire_name(HandshakeVersion::V2), WIRE_2_1);
        assert_eq!(wire_name(HandshakeVersion::V3), WIRE_3_2);
        for version in [HandshakeVersion::V2, HandshakeVersion::V3] {
            assert_eq!(handshake_for_version(wire_name(version)).unwrap(), version);
        }
    }

    // ── v3 (PROTOCOL-V3-QKD-KEYID.md) ────────────────────────────────────────

    fn v3_hello(client_kem: &EphemeralKemKey, client_id: &PqKeyExchange) -> ClientHelloV3 {
        let mut hello = ClientHelloV3 {
            version: PROTOCOL_VERSION_V3.to_string(),
            client_random: random_bytes::<32>(),
            kem_ek: client_kem.ek_bytes.clone(),
            falcon_vk: client_id.falcon_pk_bytes().to_vec(),
            slh_dsa_vk: client_id.slh_dsa_pk_bytes().to_vec(),
            requested_key_size: 32,
            client_sae_id: "sae-102".to_string(),
            qkd_capable: true,
            timestamp: unix_now(),
            hello_sig: Vec::new(),
        };
        hello.sign(client_id).expect("sign hello");
        hello
    }

    /// A small guard, built the way the gateway builds its own, for the
    /// 120 s default skew.
    fn guard(max_entries: usize) -> Mutex<ReplayGuard> {
        guard_for_skew(120, max_entries)
    }

    /// A guard built the way the gateway builds its own, for `skew`.
    fn guard_for_skew(skew: u64, max_entries: usize) -> Mutex<ReplayGuard> {
        Mutex::new(ReplayGuard::for_skew(skew, max_entries))
    }

    /// Client-side v3 transcript reconstruction from wire data — what a real
    /// external client computes from its own hello + the ServerHelloV3.
    fn client_transcript_v3(hello: &ClientHelloV3, sh: &ServerHelloV3) -> [u8; 32] {
        transcript_hash_v3(
            &hello.client_random,
            &sh.server_random,
            &hello.kem_ek,
            &sh.falcon_vk,
            &sh.kem_ciphertext,
            sh.key_mode.wire_byte(),
            sh.qkd_key_id.as_deref().unwrap_or("").as_bytes(),
            sh.master_sae_id.as_bytes(),
            sh.qkd_key_len,
        )
    }

    /// THE v3 fix, end to end: in Hybrid mode an external client — holding
    /// only wire data plus the QKD bytes its own KME returns for the signed
    /// key_ID — derives the SAME session key as the server. (This is exactly
    /// what v2 could not do: its mixed sessions were server-only secrets.)
    #[test]
    fn v3_hybrid_handshake_interoperates_end_to_end() {
        let host_key = PqKeyExchange::new().unwrap();
        let client_kem = EphemeralKemKey::new().unwrap();
        let client_id = PqKeyExchange::new().unwrap();
        let hello = v3_hello(&client_kem, &client_id);

        // The QKD key the server's KME allocated for slave SAE "sae-102";
        // the client's KME will return the same bytes for this key_ID.
        let qkd_bytes = vec![0x5Au8; 32];
        let kid = "1e4d1e4d-aaaa-bbbb-cccc-0123456789ab".to_string();

        let handshake = ServerHandshake::new()
            .respond_v3(
                &hello,
                &host_key,
                Some((kid.clone(), Zeroizing::new(qkd_bytes.clone()))),
                "sae-101",
            )
            .unwrap();
        let sh = handshake.server_hello().clone();
        assert_eq!(sh.key_mode, KeyMode::Hybrid);
        assert_eq!(sh.qkd_key_id.as_deref(), Some(kid.as_str()));
        assert_eq!(sh.qkd_key_len, 32);
        let (mut server_session, _) = handshake.into_session().unwrap();

        // Client side: verify the signed transcript, then reproduce the key.
        let transcript = client_transcript_v3(&hello, &sh);
        assert!(
            PqKeyExchange::verify_falcon(&transcript, &sh.transcript_sig, &sh.falcon_vk).unwrap(),
            "v3 transcript signature must verify"
        );
        let client_ss = client_kem.decapsulate(&sh.kem_ciphertext).unwrap();
        let client_key = derive_v3_session_key(&client_ss, Some(&qkd_bytes), &transcript);
        let mut client_session = PqSession::new(
            &client_key,
            HandshakeVersion::V3,
            Role::Client,
            random_bytes::<32>(),
            sh.falcon_vk.clone(),
        )
        .unwrap();
        request_response(
            &mut client_session,
            &mut server_session,
            b"hybrid interop at last",
        );
    }

    /// PqcOnly negotiation: no QKD → key_mode signed as PqcOnly, sessions agree.
    #[test]
    fn v3_pqconly_handshake_interoperates() {
        let host_key = PqKeyExchange::new().unwrap();
        let client_kem = EphemeralKemKey::new().unwrap();
        let client_id = PqKeyExchange::new().unwrap();
        let hello = v3_hello(&client_kem, &client_id);

        let handshake = ServerHandshake::new()
            .respond_v3(&hello, &host_key, None, "sae-101")
            .unwrap();
        let sh = handshake.server_hello().clone();
        assert_eq!(sh.key_mode, KeyMode::PqcOnly);
        assert!(sh.qkd_key_id.is_none());
        assert_eq!(sh.qkd_key_len, 0);
        let (mut server_session, _) = handshake.into_session().unwrap();

        let transcript = client_transcript_v3(&hello, &sh);
        assert!(
            PqKeyExchange::verify_falcon(&transcript, &sh.transcript_sig, &sh.falcon_vk).unwrap()
        );
        let client_ss = client_kem.decapsulate(&sh.kem_ciphertext).unwrap();
        let client_key = derive_v3_session_key(&client_ss, None, &transcript);
        let mut client_session = PqSession::new(
            &client_key,
            HandshakeVersion::V3,
            Role::Client,
            random_bytes::<32>(),
            sh.falcon_vk.clone(),
        )
        .unwrap();
        request_response(&mut client_session, &mut server_session, b"pqc-only ok");
    }

    /// Downgrade attack: a MITM flips Hybrid→PqcOnly in flight. The client's
    /// recomputed transcript no longer matches ⇒ signature verification FAILS.
    #[test]
    fn v3_downgrade_tampering_breaks_signature() {
        let host_key = PqKeyExchange::new().unwrap();
        let client_kem = EphemeralKemKey::new().unwrap();
        let client_id = PqKeyExchange::new().unwrap();
        let hello = v3_hello(&client_kem, &client_id);

        let handshake = ServerHandshake::new()
            .respond_v3(
                &hello,
                &host_key,
                Some(("uuid-x".to_string(), Zeroizing::new(vec![0x5A; 32]))),
                "sae-101",
            )
            .unwrap();
        let mut sh = handshake.server_hello().clone();

        // MITM strips the QKD parameters to force PQC-only.
        sh.key_mode = KeyMode::PqcOnly;
        sh.qkd_key_id = None;
        sh.qkd_key_len = 0;

        let tampered_transcript = client_transcript_v3(&hello, &sh);
        assert!(
            !PqKeyExchange::verify_falcon(&tampered_transcript, &sh.transcript_sig, &sh.falcon_vk)
                .unwrap(),
            "downgrade tampering MUST break the transcript signature"
        );
    }

    /// Key-ID substitution: a MITM swaps in a key_ID it can fetch ⇒ FAILS.
    #[test]
    fn v3_key_id_substitution_breaks_signature() {
        let host_key = PqKeyExchange::new().unwrap();
        let client_kem = EphemeralKemKey::new().unwrap();
        let client_id = PqKeyExchange::new().unwrap();
        let hello = v3_hello(&client_kem, &client_id);

        let handshake = ServerHandshake::new()
            .respond_v3(
                &hello,
                &host_key,
                Some(("uuid-legit".to_string(), Zeroizing::new(vec![0x5A; 32]))),
                "sae-101",
            )
            .unwrap();
        let mut sh = handshake.server_hello().clone();
        sh.qkd_key_id = Some("uuid-attacker".to_string());

        let tampered_transcript = client_transcript_v3(&hello, &sh);
        assert!(
            !PqKeyExchange::verify_falcon(&tampered_transcript, &sh.transcript_sig, &sh.falcon_vk)
                .unwrap(),
            "key_ID substitution MUST break the transcript signature"
        );
    }

    // ── client proof of possession (Verifpal F1 / backlog B6) ───────────────

    /// The F1 attack, end to end: an on-path attacker takes an honest client's
    /// hello and swaps in its own KEM key, hoping the server encapsulates to
    /// it. Before hello_sig the server did exactly that
    /// (formal/verifpal-output-leak-qkd.txt); now it refuses before
    /// encapsulating (formal/verifpal-output-clientauth-leak-qkd.txt).
    #[test]
    fn v3_substituted_kem_ek_is_refused_before_encapsulation() {
        let host_key = PqKeyExchange::new().unwrap();
        let client_kem = EphemeralKemKey::new().unwrap();
        let client_id = PqKeyExchange::new().unwrap();
        let mut hello = v3_hello(&client_kem, &client_id);
        assert!(
            hello.verify_hello_sig().unwrap(),
            "an honest hello verifies"
        );

        let attacker_kem = EphemeralKemKey::new().unwrap();
        hello.kem_ek = attacker_kem.ek_bytes.clone();
        assert!(
            !hello.verify_hello_sig().unwrap(),
            "a substituted kem_ek must break hello_sig"
        );
        assert!(
            ServerHandshake::new()
                .respond_v3(&hello, &host_key, None, "sae-101")
                .is_err(),
            "the server must not encapsulate to a KEM key the client did not sign"
        );
    }

    #[test]
    fn v3_unsigned_hello_is_refused() {
        let host_key = PqKeyExchange::new().unwrap();
        let client_kem = EphemeralKemKey::new().unwrap();
        let client_id = PqKeyExchange::new().unwrap();
        let mut hello = v3_hello(&client_kem, &client_id);
        hello.hello_sig.clear();
        assert!(!hello.verify_hello_sig().unwrap());
        assert!(ServerHandshake::new()
            .respond_v3(&hello, &host_key, None, "sae-101")
            .is_err());
    }

    /// An attacker who knows an authorized client's PUBLIC keys but holds a
    /// different private key: the hello names the authorized vk, the
    /// signature is by the attacker's key. This is exactly what passes the
    /// allow-list and must fail here.
    #[test]
    fn v3_hello_signed_by_another_identity_is_refused() {
        let host_key = PqKeyExchange::new().unwrap();
        let client_kem = EphemeralKemKey::new().unwrap();
        let victim = PqKeyExchange::new().unwrap();
        let attacker = PqKeyExchange::new().unwrap();
        let mut hello = v3_hello(&client_kem, &victim);
        hello.hello_sig = attacker.sign_transcript(&hello.digest()).unwrap();
        assert!(!hello.verify_hello_sig().unwrap());
        assert!(ServerHandshake::new()
            .respond_v3(&hello, &host_key, None, "sae-101")
            .is_err());
        // The client-side helper also refuses to sign for a vk it does not hold.
        assert!(hello.sign(&attacker).is_err());
    }

    /// Every hello field is under the signature, so none can be altered in
    /// flight (the KEM key is the one that matters for F1; the SAE-ID and
    /// capability flag are what a downgrade-minded attacker would touch).
    #[test]
    fn v3_hello_signature_covers_every_field() {
        let client_kem = EphemeralKemKey::new().unwrap();
        let client_id = PqKeyExchange::new().unwrap();
        let honest = v3_hello(&client_kem, &client_id);
        assert!(honest.verify_hello_sig().unwrap());

        type Mutation = (&'static str, Box<dyn Fn(&mut ClientHelloV3)>);
        let mutations: Vec<Mutation> = vec![
            ("client_random", Box::new(|h| h.client_random[0] ^= 1)),
            ("timestamp", Box::new(|h| h.timestamp += 1)),
            ("kem_ek", Box::new(|h| h.kem_ek[0] ^= 1)),
            ("slh_dsa_vk", Box::new(|h| h.slh_dsa_vk[0] ^= 1)),
            (
                "requested_key_size",
                Box::new(|h| h.requested_key_size += 1),
            ),
            ("client_sae_id", Box::new(|h| h.client_sae_id.push('x'))),
            ("qkd_capable", Box::new(|h| h.qkd_capable = !h.qkd_capable)),
        ];
        for (field, mutate) in mutations {
            let mut h = honest.clone();
            mutate(&mut h);
            assert!(
                !h.verify_hello_sig().unwrap(),
                "{field} must be covered by hello_sig"
            );
        }
    }

    // ── freshness and replay (backlog B8) ────────────────────────────────────

    /// The replay Verifpal reported: the same honest hello presented twice.
    /// First sight is admitted, the second is refused inside the window, and
    /// once the window has passed the timestamp check refuses it even though
    /// the guard has forgotten it.
    #[test]
    fn v3_replayed_hello_is_refused_inside_and_beyond_the_window() {
        let client_kem = EphemeralKemKey::new().unwrap();
        let client_id = PqKeyExchange::new().unwrap();
        let hello = v3_hello(&client_kem, &client_id);
        let g = guard(16);
        let t0 = Instant::now();

        admit_hello_v3(&hello, hello.timestamp, 120, &g, t0).expect("first sight is admitted");
        let err = admit_hello_v3(&hello, hello.timestamp, 120, &g, t0).unwrap_err();
        assert!(err.to_string().contains("replayed"), "got: {err}");
        let err = admit_hello_v3(
            &hello,
            hello.timestamp + 60,
            120,
            &g,
            t0 + Duration::from_secs(60),
        )
        .unwrap_err();
        assert!(
            err.to_string().contains("replayed"),
            "still inside the window: {err}"
        );

        // Beyond the window the guard has forgotten it; the timestamp check
        // is what keeps the recording worthless.
        let err = admit_hello_v3(
            &hello,
            hello.timestamp + 121,
            120,
            &g,
            t0 + Duration::from_secs(300),
        )
        .unwrap_err();
        assert!(err.to_string().contains("timestamp"), "got: {err}");
    }

    /// The timestamp is compared in whole seconds, so a hello stamped `t` is
    /// acceptable while the server's clock reads `t - skew ..= t + skew`: an
    /// interval of `2 * skew + 1` seconds of real time, not `2 * skew`. A
    /// hello first seen at the very start of that interval (dated `skew`
    /// seconds ahead of the server) is still acceptable `2 * skew` seconds
    /// later, and must still be remembered then.
    #[test]
    fn v3_hello_first_seen_at_the_early_edge_is_still_refused_at_the_late_edge() {
        let client_kem = EphemeralKemKey::new().unwrap();
        let client_id = PqKeyExchange::new().unwrap();
        let hello = v3_hello(&client_kem, &client_id);
        let skew = 120u64;
        let g = guard_for_skew(skew, 16);
        let t0 = Instant::now();

        // Server clock reads t - skew: the hello is dated `skew` seconds ahead.
        admit_hello_v3(&hello, hello.timestamp - skew, skew, &g, t0)
            .expect("first sight, at the early edge, is admitted");

        // 2 * skew seconds later the server clock reads t + skew, the last
        // second in which the timestamp check accepts this hello.
        let later = t0 + Duration::from_secs(2 * skew);
        let err = admit_hello_v3(&hello, hello.timestamp + skew, skew, &g, later)
            .expect_err("a second sight inside the acceptance interval must be refused");
        assert!(err.to_string().contains("replayed"), "got: {err}");

        // And at any later instant of that last second.
        let later = t0 + Duration::from_secs(2 * skew) + Duration::from_millis(999);
        let err = admit_hello_v3(&hello, hello.timestamp + skew, skew, &g, later)
            .expect_err("still inside the acceptance interval");
        assert!(err.to_string().contains("replayed"), "got: {err}");
    }

    #[test]
    fn v3_stale_or_future_dated_hello_is_refused_before_the_guard() {
        let client_kem = EphemeralKemKey::new().unwrap();
        let client_id = PqKeyExchange::new().unwrap();
        let hello = v3_hello(&client_kem, &client_id);
        let g = guard(16);
        let t0 = Instant::now();

        for server_clock in [hello.timestamp - 121, hello.timestamp + 121] {
            let err = admit_hello_v3(&hello, server_clock, 120, &g, t0).unwrap_err();
            assert!(err.to_string().contains("timestamp"), "got: {err}");
        }
        assert!(
            g.lock().unwrap().is_empty(),
            "a refused hello must not occupy a slot"
        );
        // Exactly at the skew boundary is still acceptable.
        admit_hello_v3(&hello, hello.timestamp + 120, 120, &g, t0).expect("boundary");
    }

    #[test]
    fn v3_invalid_signature_is_refused_before_the_timestamp_and_the_guard() {
        let client_kem = EphemeralKemKey::new().unwrap();
        let client_id = PqKeyExchange::new().unwrap();
        let mut hello = v3_hello(&client_kem, &client_id);
        hello.hello_sig.clear();
        let g = guard(16);
        let err = admit_hello_v3(&hello, hello.timestamp, 120, &g, Instant::now()).unwrap_err();
        assert!(err.to_string().contains("signature"), "got: {err}");
        assert!(
            g.lock().unwrap().is_empty(),
            "unauthenticated hellos never reach the cache"
        );
    }

    #[test]
    fn v3_replay_cache_full_fails_closed() {
        let client_id = PqKeyExchange::new().unwrap();
        let g = guard(2);
        let t0 = Instant::now();
        let mut hellos = Vec::new();
        for _ in 0..3 {
            let kem = EphemeralKemKey::new().unwrap();
            hellos.push(v3_hello(&kem, &client_id));
        }
        admit_hello_v3(&hellos[0], hellos[0].timestamp, 120, &g, t0).expect("1");
        admit_hello_v3(&hellos[1], hellos[1].timestamp, 120, &g, t0).expect("2");
        let err = admit_hello_v3(&hellos[2], hellos[2].timestamp, 120, &g, t0).unwrap_err();
        assert!(err.to_string().contains("cache full"), "got: {err}");
        // A replay of an admitted hello is still named as a replay, not as Full.
        let err = admit_hello_v3(&hellos[0], hellos[0].timestamp, 120, &g, t0).unwrap_err();
        assert!(err.to_string().contains("replayed"), "got: {err}");
    }

    /// The signed hello still round-trips the wire and keeps the version
    /// peek working (the signature is the last field; bincode encodes the
    /// version string first).
    #[test]
    fn v3_signed_hello_round_trips_and_still_peeks() {
        let client_kem = EphemeralKemKey::new().unwrap();
        let client_id = PqKeyExchange::new().unwrap();
        let hello = v3_hello(&client_kem, &client_id);
        let bytes = bincode::serialize(&hello).unwrap();
        let back: ClientHelloV3 = bincode::deserialize(&bytes).unwrap();
        assert!(back.verify_hello_sig().unwrap());
        let peek: VersionPeek = bincode::deserialize(&bytes).unwrap();
        assert!(peek.version.starts_with("3."));
    }

    /// The version peek picks the right struct shape for both wire versions.
    #[test]
    fn version_peek_distinguishes_v2_and_v3() {
        let client_kem = EphemeralKemKey::new().unwrap();
        let client_id = PqKeyExchange::new().unwrap();

        let v2 = ClientHello {
            version: PROTOCOL_VERSION.to_string(),
            client_random: random_bytes::<32>(),
            kem_ek: client_kem.ek_bytes.clone(),
            falcon_vk: client_id.falcon_pk_bytes().to_vec(),
            slh_dsa_vk: client_id.slh_dsa_pk_bytes().to_vec(),
            requested_key_size: 32,
        };
        let v3 = v3_hello(&client_kem, &client_id);

        let v2_bytes = bincode::serialize(&v2).unwrap();
        let v3_bytes = bincode::serialize(&v3).unwrap();

        let p2: VersionPeek = bincode::deserialize(&v2_bytes).unwrap();
        let p3: VersionPeek = bincode::deserialize(&v3_bytes).unwrap();
        assert!(p2.version.starts_with("2."));
        assert!(p3.version.starts_with("3."));
    }
}
