//! Post-quantum TCP relay.
//!
//! PQTG's original mode is an ETSI GS QKD 014 *application gateway*: it parses
//! what it carries. This module adds a second mode where it parses nothing. It
//! accepts a TCP connection, performs the same post-quantum handshake, dials a
//! backend, and splices raw bytes in both directions with AES-256-GCM in
//! between. Because it never interprets the payload, it can carry any TCP
//! protocol, including libp2p validator traffic.
//!
//! # Why a per-connection relay and not a tunnel
//!
//! The earlier attempt at post-quantum validator transport multiplexed several
//! forwards over one qssh connection. Every forward terminated on the peer's
//! loopback, so a node asked to accept two inbound forwards failed the second,
//! and a full mesh at N >= 4 always asks some node to do exactly that.
//!
//! Here each connection is an independent socket, task and key schedule. There
//! is no shared transport, no channel registry, and no channel-accept
//! round-trip, so the failure mode does not exist and the design scales to any
//! N.
//!
//! # Directional keys, not a shared cipher
//!
//! Full duplex means two tasks touching the session at once. Rather than put
//! one cipher behind a mutex on the hot path, the handshake derives **two**
//! keys from the shared secret, one per direction. Each task owns its cipher
//! outright. That removes the lock, and it removes any possibility of the two
//! directions colliding on a nonce, which a shared counter would risk.
//!
//! # Record format
//!
//! ```text
//! [u32 BE length][12-byte nonce][AES-256-GCM ciphertext + tag]
//! ```
//!
//! Falcon signs the handshake transcript only. It is deliberately **not**
//! applied per record: measured on this machine, a Falcon-512 signature costs
//! about 326 microseconds against 250 nanoseconds for the symmetric path, which
//! would cap a single-threaded relay near 3,000 records per second. See
//! `docs/BENCHMARKS-2026-09-08.md`.
//!
//! # Server identity pinning
//!
//! The client verifies the server's transcript signature under the Falcon key
//! the server just sent. On its own that authenticates nobody: an on-path
//! attacker sends its own key and signs with it (Verifpal finding F2,
//! `formal/VERIFICATION-RESULTS-2026-09-12.md`). The relay client therefore
//! **requires a pin**, the server's identity fingerprint obtained out of band
//! (`--print-fingerprint`, or `relay_wan fingerprint`), and refuses any server
//! that presents a different one, before the signature is even checked.
//! Running unpinned is an explicit choice (`PinPolicy::Unpinned`) and is logged
//! at WARN on every handshake. The relay carries no QKD key, so without the pin
//! there is no second leg to fall back on.
//!
//! # Client authentication
//!
//! Until `relay-2` the server accepted any `RelayHello`: the client's
//! `falcon_vk` was bound into the transcript but checked against nothing, and
//! the hello was signed by nobody, so anyone who could reach a relay server
//! port could open a post-quantum tunnel to its backend (Verifpal finding R1,
//! `formal/RELAY-RESULTS-2026-09-12.md`). Now the server holds an allow-list
//! of client fingerprints (`ClientPolicy::Authorized`, the mirror of the
//! client's pin) and the client signs a time-stamped hello with its identity
//! key; the server checks allow-list, signature, freshness and a replay guard
//! before it encapsulates. `ClientPolicy::AnyClient` is the explicit,
//! WARN-logged opt-out for a backend that gates its own peers (QuantumHarmony
//! validators do, via libp2p `--reserved-only`). The authenticated model
//! (`formal/pqtg-relay-handshake-clientauth.vp`) passes every confidentiality
//! and server-authentication query; the replay guard is a stateful measure the
//! symbolic model does not express.

use anyhow::{anyhow, Context, Result};
use serde::{Deserialize, Serialize};
use sha3::{Digest, Sha3_256};
use socket2::{SockRef, TcpKeepalive};
use std::collections::HashMap;
use std::net::{IpAddr, SocketAddr};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};
use tokio::io::{AsyncReadExt, AsyncWriteExt};
use tokio::net::{TcpListener, TcpStream};
use tracing::{debug, info, warn};

use crate::crypto::{
    compute_identity_fingerprint, encapsulate_to, format_fingerprint, random_bytes,
    EphemeralKemKey, PqKeyExchange, FALCON_512_VK_LEN, ML_KEM_768_CT_LEN, ML_KEM_768_EK_LEN,
    SLH_DSA_SHAKE128F_VK_LEN,
};
use crate::replay::{ReplayGuard, Verdict};

/// Relay wire version. Distinct from the gateway protocol's "2.0" so the two
/// can never be confused by a peer that speaks only one of them. `relay-2`
/// added the signed, time-stamped hello (client authentication, finding R1);
/// a `relay-1` peer is refused with a version mismatch rather than accepted
/// unauthenticated. `relay-3` added the KEM re-injection into the record-layer
/// ratchet (typed records); a `relay-2` peer would misparse records, so it is
/// refused at the version check too.
pub const RELAY_VERSION: &str = "relay-3";

/// Domain separator for the relay transcript. Keeps relay handshake signatures
/// disjoint from gateway handshake signatures made with the same Falcon key.
const RELAY_TRANSCRIPT_LABEL: &[u8] = b"PQTG-RELAY-TRANSCRIPT-v1\x00";

/// Domain separator for the client's hello signature. Disjoint from the
/// transcript label and from the gateway's `pqtg-client-hello-v3`.
const RELAY_HELLO_LABEL: &[u8] = b"PQTG-RELAY-HELLO-v2\x00";

/// Freshness window for the signed hello timestamp, either direction. A
/// recorded hello is worthless once the window has passed; inside it the
/// replay guard refuses a second sight. Relay peers are infrastructure with
/// synchronised clocks, so two minutes is generous.
const HELLO_MAX_SKEW_SECS: u64 = 120;

/// The replay guard must remember a hello for the whole interval in which its
/// timestamp is acceptable: twice the skew after first sight (see replay.rs).
const HELLO_REPLAY_WINDOW: Duration = Duration::from_secs(2 * HELLO_MAX_SKEW_SECS);

/// Replay cache capacity. Only signature-valid, in-window hellos from
/// allow-listed clients are ever inserted, so it cannot be filled by a
/// stranger; sized for a few hundred handshakes per second over the window.
const HELLO_REPLAY_CACHE_ENTRIES: usize = 65_536;

/// Domain separators for the two directional keys.
const KDF_LABEL_C2S: &[u8] = b"PQTG-RELAY-KEY-c2s-v1\x00";
const KDF_LABEL_S2C: &[u8] = b"PQTG-RELAY-KEY-s2c-v1\x00";

/// Largest handshake message accepted. A hello is about 2.2 KB; this leaves
/// headroom without letting a peer force a large allocation before it has
/// authenticated.
const MAX_HELLO_BYTES: usize = 16 * 1024;

/// Largest relay record. Bounds the allocation a peer can force per frame.
pub const MAX_RECORD_BYTES: usize = 1024 * 1024;

/// Plaintext chunk size read from a socket before encryption. Kept below
/// `MAX_RECORD_BYTES` with room for nonce and tag.
const CHUNK_BYTES: usize = 64 * 1024;

/// Records sealed under one epoch key before the ratchet advances.
///
/// At 64 KiB records this is a rekey roughly every 4 GiB in one direction,
/// which on a validator link is hours rather than seconds. The point is not
/// nonce exhaustion, which a 64-bit counter makes unreachable, but bounding how
/// much traffic a compromised epoch key exposes. The ratchet is one-way, so
/// epoch N's key does not yield the epochs before it, and since `relay-3` each
/// step also absorbs fresh ML-KEM material offered by the peer, so epoch N's
/// key does not yield the epochs after it either (post-compromise security,
/// backlog B11; `formal/RATCHET-RESULTS-2026-09-12.md`). Without an offer in
/// hand the step is hash-only and the second guarantee lapses for that epoch.
const REKEY_EVERY_RECORDS: u64 = 65_536;

/// Domain separator for the ratchet step. v2: the step also absorbs fresh
/// ML-KEM material when the peer offered a key (backlog B11).
const RATCHET_LABEL: &[u8] = b"PQTG-RELAY-RATCHET-v2\x00";

/// Record types, the first byte of every AEAD plaintext. Control material rides
/// inside ordinary sequenced records, so there is nothing to race and no
/// extra nonce slots are consumed.
const REC_DATA: u8 = 0x00;
/// Followed by an ML-KEM-768 encapsulation key: "when you next ratchet the
/// direction you send to me, encapsulate to this", then the data.
const REC_OFFER: u8 = 0x01;
/// Followed by an ML-KEM-768 ciphertext against the peer's last offer, then the
/// data. Last record of its epoch: both sides ratchet with the shared secret
/// right after it.
const REC_COMMIT_KEM: u8 = 0x02;
/// Last record of its epoch with no fresh material (the peer never offered a
/// key). Both sides ratchet hash-only, as in `relay-2`; logged at WARN.
const REC_COMMIT_HASH_ONLY: u8 = 0x03;

/// TCP keepalive, so a peer that dies without sending a FIN is noticed.
///
/// Without this a spliced connection whose far end vanished (a machine losing
/// power, a NAT dropping the mapping, a cable pulled) leaves one direction
/// blocked on a read that will never return and never error. The socket, the
/// task and the entry in the live-connection count all leak, and libp2p is
/// never told the peer is gone, so it does not redial.
///
/// Idle 30 s, then a probe every 10 s, giving up after 3. A dead peer is
/// detected in about a minute, which is well inside a validator's tolerance and
/// far cheaper than the alternative of an application-level ping.
const KEEPALIVE_IDLE: Duration = Duration::from_secs(30);
const KEEPALIVE_INTERVAL: Duration = Duration::from_secs(10);
const KEEPALIVE_RETRIES: u32 = 3;

/// Reap a connection on which nothing has moved in either direction.
///
/// Keepalive catches a dead peer. This catches a live peer that has stopped
/// speaking, which keepalive cannot see because the socket is healthy. Ten
/// minutes is deliberately far longer than libp2p's own ping interval, so a
/// working validator link never trips it.
const IDLE_TIMEOUT: Duration = Duration::from_secs(600);

/// Longest a connection may take to complete its post-quantum handshake before
/// the relay drops it. Without this bound, a client can connect and simply never
/// send its hello: the accept task blocks on the read forever, the slot is held,
/// and enough such connections fill `max_connections` and deny service to real
/// clients. That is a trivial slowloris (verified 2026-09-10: 300 connect-and-
/// hang sockets took every slot and a legitimate client got no response). The
/// handshake is ~8 ms of real work, so 10 s is orders of magnitude of slack for
/// an honest peer and a hard cap for a hung one.
const HANDSHAKE_TIMEOUT: Duration = Duration::from_secs(10);

/// Most concurrent connections allowed from a single source IP. The global
/// `max_connections` cap bounds total memory, but on its own it does not stop a
/// single host from taking every slot: with the handshake timeout in place an
/// attacker can no longer HOLD slots with hung handshakes, but a sustained
/// attacker that recycles connections fast enough can still churn through the
/// global cap and crowd out real clients (the documented residual from the
/// 2026-09-10 load test). Capping per source IP well below the global limit
/// closes that: one host can occupy at most this many slots, so it can never
/// deny service to the rest, however fast it recycles.
///
/// 32 is generous for an honest client (even a connection-pooling one) and a
/// small fraction of a 256-slot relay. Note: deployments where many legitimate
/// users share one public IP (large NAT) may need this raised; it is a
/// conservative default for validator/RPC front-ends where sources are few.
const MAX_CONNECTIONS_PER_IP: u32 = 32;

/// Decrements the live counter and the per-source counter when a connection
/// ends, no matter how it ends (normal close, error, or panic in the task).
/// Doing this in Drop rather than by hand is what makes the accounting exact:
/// an early return or panic can never leak a slot or a per-IP count.
struct ConnGuard {
    live: Arc<AtomicU64>,
    per_ip: Arc<Mutex<HashMap<IpAddr, u32>>>,
    ip: IpAddr,
}

impl Drop for ConnGuard {
    fn drop(&mut self) {
        self.live.fetch_sub(1, Ordering::Relaxed);
        if let Ok(mut map) = self.per_ip.lock() {
            if let Some(n) = map.get_mut(&self.ip) {
                *n -= 1;
                if *n == 0 {
                    map.remove(&self.ip);
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Handshake messages
// ---------------------------------------------------------------------------

#[derive(Serialize, Deserialize)]
struct RelayHello {
    version: String,
    client_random: [u8; 32],
    /// ML-KEM-768 encapsulation key.
    kem_ek: Vec<u8>,
    /// Falcon-512 verification key, the client's identity.
    falcon_vk: Vec<u8>,
    /// SLH-DSA-Shake128f verification key, hash-based identity.
    slh_dsa_vk: Vec<u8>,
    /// Client clock, seconds since the Unix epoch, under the signature. The
    /// server refuses a hello more than `HELLO_MAX_SKEW_SECS` from its own.
    timestamp: u64,
    /// Falcon-512 signature by the client's identity key (the one `falcon_vk`
    /// names) over `relay_hello_digest` of every field above. Proves the
    /// sender holds the allow-listed key and binds THIS `kem_ek` to it, so an
    /// on-path attacker cannot present an allow-listed client's public keys
    /// with its own KEM key (Verifpal finding R1, backlog B10;
    /// `formal/pqtg-relay-handshake-clientauth.vp`).
    hello_sig: Vec<u8>,
}

/// Seconds since the Unix epoch. A clock before 1970 reads as 0, which fails
/// the freshness check rather than passing it.
fn unix_now() -> u64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_secs())
        .unwrap_or(0)
}

/// What `RelayHello::hello_sig` signs: every hello field except the signature,
/// variable-length fields length-prefixed, under the relay hello label.
fn relay_hello_digest(
    client_random: &[u8; 32],
    timestamp: u64,
    kem_ek: &[u8],
    falcon_vk: &[u8],
    slh_dsa_vk: &[u8],
) -> [u8; 32] {
    let mut h = Sha3_256::new();
    h.update(RELAY_HELLO_LABEL);
    h.update(client_random);
    h.update(timestamp.to_be_bytes());
    for field in [kem_ek, falcon_vk, slh_dsa_vk] {
        h.update((field.len() as u32).to_be_bytes());
        h.update(field);
    }
    let mut out = [0u8; 32];
    out.copy_from_slice(&h.finalize());
    out
}

impl RelayHello {
    fn digest(&self) -> [u8; 32] {
        relay_hello_digest(
            &self.client_random,
            self.timestamp,
            &self.kem_ek,
            &self.falcon_vk,
            &self.slh_dsa_vk,
        )
    }

    /// Client side: sign with the identity whose keys the hello carries.
    fn sign(&mut self, identity: &PqKeyExchange) -> Result<()> {
        if identity.falcon_pk_bytes() != self.falcon_vk.as_slice() {
            return Err(anyhow!(
                "relay hello falcon_vk does not match the signing identity"
            ));
        }
        self.hello_sig = identity.sign_transcript(&self.digest())?;
        Ok(())
    }

    /// Server side: does `hello_sig` verify under the hello's own `falcon_vk`?
    /// Meaningful only after the allow-list has accepted that key.
    fn verify_sig(&self) -> Result<bool> {
        if self.hello_sig.is_empty() {
            return Ok(false);
        }
        PqKeyExchange::verify_falcon(&self.digest(), &self.hello_sig, &self.falcon_vk)
    }
}

#[derive(Serialize, Deserialize)]
struct RelayServerHello {
    version: String,
    server_random: [u8; 32],
    falcon_vk: Vec<u8>,
    slh_dsa_vk: Vec<u8>,
    /// ML-KEM-768 ciphertext, encapsulated against the client's key.
    kem_ciphertext: Vec<u8>,
    /// Falcon-512 signature over the transcript hash.
    transcript_sig: Vec<u8>,
}

/// Hash everything both sides have seen, in a fixed order, under a relay
/// specific label. Every variable-length field is length-prefixed so two
/// different handshakes cannot produce the same transcript.
fn relay_transcript(
    client_random: &[u8; 32],
    server_random: &[u8; 32],
    kem_ek: &[u8],
    kem_ct: &[u8],
    client_falcon_vk: &[u8],
    server_falcon_vk: &[u8],
) -> [u8; 32] {
    let mut h = Sha3_256::new();
    h.update(RELAY_TRANSCRIPT_LABEL);
    h.update(client_random);
    h.update(server_random);
    for field in [kem_ek, kem_ct, client_falcon_vk, server_falcon_vk] {
        h.update((field.len() as u32).to_be_bytes());
        h.update(field);
    }
    let mut out = [0u8; 32];
    out.copy_from_slice(&h.finalize());
    out
}

/// Derive one directional key from the shared secret and the transcript.
fn derive_directional_key(secret: &[u8; 32], transcript: &[u8; 32], label: &[u8]) -> [u8; 32] {
    let mut h = Sha3_256::new();
    h.update(label);
    h.update(secret);
    h.update(transcript);
    let mut out = [0u8; 32];
    out.copy_from_slice(&h.finalize());
    out
}

// ---------------------------------------------------------------------------
// Framed record I/O
// ---------------------------------------------------------------------------

/// Disable Nagle's algorithm on a relay socket.
///
/// Each record is written as a length prefix followed by a payload. With Nagle
/// enabled, the second write waits for an ACK that the peer's delayed-ACK timer
/// is holding, which stalls small records by tens of milliseconds. Measured on a
/// 16 ms link: p50 round trip fell from 137 ms to the numbers in
/// `docs/BENCHMARKS-2026-09-08.md` once this was set.
///
/// A relay carrying consensus votes moves many small records, so this matters
/// more here than raw throughput does.
/// Keepalive is applied here too, for the reason given at [`KEEPALIVE_IDLE`].
/// Both settings are best effort: a socket that refuses them still works, it
/// is just slower or slower to notice a death, so a failure is logged and not
/// propagated.
fn configure_socket(stream: &TcpStream, who: &str) {
    if let Err(e) = stream.set_nodelay(true) {
        warn!("relay: could not disable Nagle on the {who} socket: {e}");
    }

    let keepalive = TcpKeepalive::new()
        .with_time(KEEPALIVE_IDLE)
        .with_interval(KEEPALIVE_INTERVAL)
        .with_retries(KEEPALIVE_RETRIES);
    if let Err(e) = SockRef::from(stream).set_tcp_keepalive(&keepalive) {
        warn!("relay: could not enable TCP keepalive on the {who} socket: {e}");
    }
}

async fn write_len_prefixed<W>(w: &mut W, payload: &[u8]) -> Result<()>
where
    W: AsyncWriteExt + Unpin,
{
    w.write_all(&(payload.len() as u32).to_be_bytes()).await?;
    w.write_all(payload).await?;
    w.flush().await?;
    Ok(())
}

async fn read_len_prefixed<R>(r: &mut R, max: usize) -> Result<Vec<u8>>
where
    R: AsyncReadExt + Unpin,
{
    let mut len_buf = [0u8; 4];
    r.read_exact(&mut len_buf).await?;
    let len = u32::from_be_bytes(len_buf) as usize;
    if len > max {
        return Err(anyhow!("frame of {len} bytes exceeds the {max} byte limit"));
    }
    let mut buf = vec![0u8; len];
    r.read_exact(&mut buf).await?;
    Ok(buf)
}

// ---------------------------------------------------------------------------
// Directional cipher
// ---------------------------------------------------------------------------

/// What one endpoint's two directions share so the ratchet can take fresh
/// key material (backlog B11): the peer's last offered ML-KEM key (used by
/// `send` at its next epoch boundary), the decapsulation key behind our own
/// last offer (used by `recv` when the peer commits), and whether `send`
/// owes the peer a new offer. Touched only on control records and at epoch
/// boundaries, never per data byte.
#[derive(Default)]
pub struct RekeyLink {
    peer_ek: Option<Vec<u8>>,
    my_dk: Option<EphemeralKemKey>,
    offer_pending: bool,
}

impl RekeyLink {
    /// A fresh link owes the peer an offer immediately, so the first data
    /// record on each direction carries one.
    pub fn new() -> Arc<Mutex<Self>> {
        Arc::new(Mutex::new(Self {
            peer_ek: None,
            my_dk: None,
            offer_pending: true,
        }))
    }
}

/// One direction of a relay session: its own AES-256-GCM key and its own nonce
/// counter, owned outright by whichever task uses it.
///
/// # Rekey without a round trip
///
/// qssh's in-band rekey injects a negotiation into the same stream the
/// forwarder is reading. Its own source says so: "in-band rekey races the
/// forwarding reader and desyncs" (`client.rs:120`). That race is why 508 of
/// 508 production rekeys failed, and why their fallback was to drop the
/// connection and reconnect instead.
///
/// This ratchets instead. Every `REKEY_EVERY_RECORDS` records the sender marks
/// the last record of the epoch as a COMMIT and both ends derive the next epoch
/// key right after it, deterministically. There is no negotiation and no
/// acknowledgement: the marker is a type byte inside an ordinary, sequenced,
/// authenticated record, so there is nothing to race and nothing that can
/// desynchronise. Since `relay-3` the commit also carries an ML-KEM
/// encapsulation against a key the peer offered earlier in the stream, and
/// the shared secret enters the next epoch key: a key recovered in epoch N
/// then yields neither the epochs before N (one-way hash) nor the epochs after
/// it (fresh material). If no offer is in hand at the boundary the step is
/// hash-only, logged at WARN, and only the backward guarantee holds for that
/// epoch. Nonces carry the epoch in their top four bytes, so a counter that
/// restarts each epoch can never repeat a nonce under the same key.
pub struct DirectionalCipher {
    cipher: aes_gcm::Aes256Gcm,
    /// Current epoch key, retained to derive the next one; zeroized on ratchet.
    key: [u8; 32],
    /// Records sealed or opened in this epoch.
    nonce_counter: u64,
    /// Ratchet generation, carried in the nonce.
    epoch: u32,
    /// Sender policy: records per epoch. The receiver follows the COMMIT
    /// markers instead, so only the sender's value matters on the wire.
    records_per_epoch: u64,
    /// Shared with the opposite direction of the same endpoint.
    link: Arc<Mutex<RekeyLink>>,
    /// Telemetry: how the epochs so far were entered.
    kem_ratchets: u32,
    hash_only_ratchets: u32,
    last_ratchet_fresh: bool,
}

impl DirectionalCipher {
    fn new(key: &[u8; 32], link: Arc<Mutex<RekeyLink>>) -> Self {
        use aes_gcm::{Aes256Gcm, KeyInit};
        let cipher = Aes256Gcm::new(key.into());
        Self {
            cipher,
            key: *key,
            nonce_counter: 0,
            epoch: 0,
            records_per_epoch: REKEY_EVERY_RECORDS,
            link,
            kem_ratchets: 0,
            hash_only_ratchets: 0,
            last_ratchet_fresh: false,
        }
    }

    /// Current ratchet generation. Exposed for tests and telemetry.
    pub fn epoch(&self) -> u32 {
        self.epoch
    }

    /// Epochs entered with fresh ML-KEM material, and without. Telemetry and
    /// tests; the binary logs `last_ratchet_fresh` instead, hence the bin-side
    /// allow.
    #[allow(dead_code)]
    pub fn ratchet_counts(&self) -> (u32, u32) {
        (self.kem_ratchets, self.hash_only_ratchets)
    }

    /// Whether the most recent ratchet absorbed fresh material.
    pub fn last_ratchet_fresh(&self) -> bool {
        self.last_ratchet_fresh
    }

    /// Nonce for the record at this position: `epoch(4) || counter(8)`.
    fn nonce_bytes(&self) -> [u8; 12] {
        let mut n = [0u8; 12];
        n[..4].copy_from_slice(&self.epoch.to_be_bytes());
        n[4..].copy_from_slice(&self.nonce_counter.to_be_bytes());
        n
    }

    fn lock_link(&self) -> std::sync::MutexGuard<'_, RekeyLink> {
        self.link.lock().unwrap_or_else(|p| p.into_inner())
    }

    /// Advance to the next epoch, absorbing `fresh` (an ML-KEM shared secret,
    /// or nothing). Called identically on both sides right after the COMMIT
    /// record, so the two stay in step. The previous key is zeroized.
    fn ratchet(&mut self, fresh: &[u8]) -> Result<()> {
        use aes_gcm::{Aes256Gcm, KeyInit};
        use zeroize::Zeroize;

        let next_epoch = self.epoch.checked_add(1).ok_or_else(|| {
            anyhow!("ratchet epoch exhausted; the session must be re-established")
        })?;

        let mut h = Sha3_256::new();
        h.update(RATCHET_LABEL);
        h.update(self.key);
        h.update(next_epoch.to_be_bytes());
        h.update((fresh.len() as u32).to_be_bytes());
        h.update(fresh);
        let mut next = [0u8; 32];
        next.copy_from_slice(&h.finalize());

        self.cipher = Aes256Gcm::new(&next.into());
        self.key.zeroize();
        self.key = next;
        next.zeroize();
        self.epoch = next_epoch;
        self.nonce_counter = 0;
        if fresh.is_empty() {
            self.hash_only_ratchets += 1;
            self.last_ratchet_fresh = false;
            warn!(
                "relay: ratcheted to epoch {next_epoch} WITHOUT fresh key material (the peer \
                 offered none); this epoch has backward secrecy only"
            );
        } else {
            self.kem_ratchets += 1;
            self.last_ratchet_fresh = true;
            debug!("relay: ratcheted to epoch {next_epoch} with fresh ML-KEM material");
        }
        Ok(())
    }

    /// Seal one record. Wire form: `nonce(12) || AEAD(type || control || data)`.
    ///
    /// Control material is decided here: an OFFER if this endpoint owes the
    /// peer one, or, on the last record of the epoch, a COMMIT (with an
    /// encapsulation against the peer's last offer when there is one). Never
    /// both in one record: an offer due at a boundary waits for the next
    /// record.
    pub fn seal(&mut self, plaintext: &[u8]) -> Result<Vec<u8>> {
        use aes_gcm::aead::Aead;
        use aes_gcm::Nonce;
        use zeroize::Zeroize;

        let last_of_epoch = self.nonce_counter + 1 >= self.records_per_epoch;
        let mut body = Vec::with_capacity(1 + ML_KEM_768_EK_LEN + plaintext.len());
        // Fresh material to absorb after this record is on the wire.
        let mut fresh: Option<[u8; 32]> = None;

        if last_of_epoch {
            let peer_ek = self.lock_link().peer_ek.take();
            match peer_ek {
                Some(ek) => {
                    let (ct, ss) = encapsulate_to(&ek)?;
                    body.push(REC_COMMIT_KEM);
                    body.extend_from_slice(&ct);
                    fresh = Some(ss);
                }
                None => body.push(REC_COMMIT_HASH_ONLY),
            }
        } else {
            let owes_offer = {
                let mut link = self.lock_link();
                if link.offer_pending {
                    link.offer_pending = false;
                    true
                } else {
                    false
                }
            };
            if owes_offer {
                let kem = EphemeralKemKey::new().context("relay: ML-KEM keygen for offer")?;
                body.push(REC_OFFER);
                body.extend_from_slice(&kem.ek_bytes);
                self.lock_link().my_dk = Some(kem);
            } else {
                body.push(REC_DATA);
            }
        }
        body.extend_from_slice(plaintext);

        let nonce_bytes = self.nonce_bytes();
        let ct = self
            .cipher
            .encrypt(Nonce::from_slice(&nonce_bytes), body.as_slice())
            .map_err(|_| anyhow!("relay record encryption failed"))?;
        self.nonce_counter += 1;

        if last_of_epoch {
            match fresh.as_mut() {
                Some(ss) => {
                    self.ratchet(&ss[..])?;
                    ss.zeroize();
                }
                None => self.ratchet(&[])?,
            }
        }

        let mut out = Vec::with_capacity(12 + ct.len());
        out.extend_from_slice(&nonce_bytes);
        out.extend_from_slice(&ct);
        Ok(out)
    }

    /// Open one record and return its data. Rejects a nonce that is not the one
    /// expected next, so a reordered or replayed record fails rather than
    /// being silently accepted. Control material is consumed here: an OFFER is
    /// stored for this endpoint's opposite direction, a COMMIT ratchets this
    /// direction (with the peer's material decapsulated under the key behind
    /// our last offer) and makes a new offer due.
    pub fn open(&mut self, record: &[u8]) -> Result<Vec<u8>> {
        use aes_gcm::aead::Aead;
        use aes_gcm::Nonce;
        use zeroize::Zeroize;

        if record.len() < 12 + 16 + 1 {
            return Err(anyhow!("relay record too short: {} bytes", record.len()));
        }
        let (nonce_bytes, ct) = record.split_at(12);

        let expected = self.nonce_bytes();
        if nonce_bytes != expected {
            return Err(anyhow!(
                "relay record out of sequence: replay or reordering rejected"
            ));
        }

        let body = self
            .cipher
            .decrypt(Nonce::from_slice(nonce_bytes), ct)
            .map_err(|_| anyhow!("relay record authentication failed"))?;
        let (kind, rest) = body
            .split_first()
            .ok_or_else(|| anyhow!("relay record has no type byte"))?;

        // Decide what to do BEFORE advancing, so a malformed record leaves the
        // session exactly where it was.
        let (data, action): (&[u8], Option<Option<[u8; 32]>>) = match *kind {
            REC_DATA => (rest, None),
            REC_OFFER => {
                if rest.len() < ML_KEM_768_EK_LEN {
                    return Err(anyhow!("relay OFFER record is truncated"));
                }
                let (ek, data) = rest.split_at(ML_KEM_768_EK_LEN);
                self.lock_link().peer_ek = Some(ek.to_vec());
                (data, None)
            }
            REC_COMMIT_KEM => {
                if rest.len() < ML_KEM_768_CT_LEN {
                    return Err(anyhow!("relay COMMIT record is truncated"));
                }
                let (ct, data) = rest.split_at(ML_KEM_768_CT_LEN);
                let dk = self.lock_link().my_dk.take().ok_or_else(|| {
                    anyhow!(
                        "relay COMMIT carries an encapsulation but this endpoint offered no \
                         key; refusing rather than guessing"
                    )
                })?;
                let ss = dk.decapsulate(ct)?;
                (data, Some(Some(ss)))
            }
            REC_COMMIT_HASH_ONLY => (rest, Some(None)),
            other => return Err(anyhow!("relay record has unknown type {other:#04x}")),
        };
        let data = data.to_vec();

        // Advance only on success, so a rejected record does not desynchronise
        // the session or push the ratchet forward.
        self.nonce_counter += 1;
        if let Some(fresh) = action {
            match fresh {
                Some(mut ss) => {
                    self.ratchet(&ss[..])?;
                    ss.zeroize();
                }
                None => self.ratchet(&[])?,
            }
            // The peer consumed our offer (or had none): owe it a new one.
            self.lock_link().offer_pending = true;
        }
        Ok(data)
    }
}

/// A completed relay handshake: one cipher per direction.
pub struct RelaySession {
    /// Seals what this end sends.
    pub send: DirectionalCipher,
    /// Opens what this end receives.
    pub recv: DirectionalCipher,
    /// The peer's Falcon verification key. Exposed for logging and for the
    /// server-side client allow-list that does not exist yet (finding R1,
    /// backlog B10); until then nothing in the binary reads it, hence the
    /// bin-side allow (the library API keeps it).
    #[allow(dead_code)]
    pub peer_falcon_vk: Vec<u8>,
}

// Debug without the ciphers: lets a `Result<RelaySession>` be unwrapped in
// tests and logged, and never prints key material.
impl std::fmt::Debug for RelaySession {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("RelaySession")
            .field("peer_falcon_vk_len", &self.peer_falcon_vk.len())
            .finish_non_exhaustive()
    }
}

// ---------------------------------------------------------------------------
// Server identity pinning
// ---------------------------------------------------------------------------

/// The fingerprint a relay client expects the relay server to present:
/// `SHA3-256("pqtg-identity-fingerprint-v1" ‖ len ‖ falcon_vk ‖ len ‖ slh_dsa_vk)`,
/// exactly `crypto::compute_identity_fingerprint`, so one pin covers an
/// appliance on both its gateway and relay paths.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct ServerPin([u8; 32]);

impl ServerPin {
    /// Parse the operator-facing form printed by `--print-fingerprint`:
    /// `SHA3-256:<base64>`, padding optional.
    pub fn parse(s: &str) -> Result<Self> {
        use base64::engine::general_purpose::STANDARD_NO_PAD;
        use base64::Engine as _;
        let s = s.trim();
        let b64 = s
            .strip_prefix("SHA3-256:")
            .ok_or_else(|| anyhow!("pin must look like SHA3-256:<base64>, got {s:?}"))?
            .trim_end_matches('=');
        let bytes = STANDARD_NO_PAD
            .decode(b64)
            .map_err(|e| anyhow!("pin is not valid base64: {e}"))?;
        if bytes.len() != 32 {
            return Err(anyhow!("pin decodes to {} bytes, expected 32", bytes.len()));
        }
        let mut out = [0u8; 32];
        out.copy_from_slice(&bytes);
        Ok(Self(out))
    }

    /// The pin of an identity whose key is in hand (tooling, tests).
    pub fn of(identity: &PqKeyExchange) -> Self {
        Self(identity.identity_fingerprint())
    }

    pub fn as_bytes(&self) -> &[u8; 32] {
        &self.0
    }
}

impl std::fmt::Display for ServerPin {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&format_fingerprint(&self.0))
    }
}

/// What a relay client does with the identity the server presents.
#[derive(Clone, Copy, Debug)]
pub enum PinPolicy {
    /// Refuse any server whose fingerprint is not this one. The only mode in
    /// which the handshake authenticates the server.
    Require(ServerPin),
    /// Accept whatever key the server sends, and say so at WARN on every
    /// handshake. For a bench on a link you already trust. Never for a
    /// validator.
    Unpinned,
}

/// What a relay server does with the identity a client presents: the mirror
/// image of `PinPolicy`. The allow-list entries are the same fingerprint type
/// as the pin (`compute_identity_fingerprint` of the client's two keys, the
/// value `--print-fingerprint` prints on the client).
#[derive(Clone, Debug)]
pub enum ClientPolicy {
    /// Accept only clients whose fingerprint is in this list, and only with a
    /// hello they signed. The only mode in which the backend is not exposed
    /// to anyone who can reach the relay port (finding R1).
    Authorized(Vec<ServerPin>),
    /// Accept any client that signs its hello, and say so at WARN on every
    /// handshake. For a backend that authenticates its peers itself, or a
    /// bench. Never in front of a service that trusts the relay to gate it.
    AnyClient,
}

// ---------------------------------------------------------------------------
// Handshake
// ---------------------------------------------------------------------------

/// Client side of the relay handshake. PQTG previously had no client half at
/// all; libp2p needs every node to dial out as well as accept.
pub async fn client_handshake(
    stream: &mut TcpStream,
    identity: &PqKeyExchange,
    policy: PinPolicy,
) -> Result<RelaySession> {
    let kem = EphemeralKemKey::new().context("relay client: ML-KEM keygen")?;
    let client_random = random_bytes::<32>();

    let mut hello = RelayHello {
        version: RELAY_VERSION.to_string(),
        client_random,
        kem_ek: kem.ek_bytes.clone(),
        falcon_vk: identity.falcon_pk_bytes().to_vec(),
        slh_dsa_vk: identity.slh_dsa_pk_bytes().to_vec(),
        timestamp: unix_now(),
        hello_sig: Vec::new(),
    };
    hello.sign(identity)?;
    write_len_prefixed(stream, &bincode::serialize(&hello)?).await?;

    let raw = read_len_prefixed(stream, MAX_HELLO_BYTES).await?;
    let server_hello: RelayServerHello = bincode::deserialize(&raw)?;

    if server_hello.version != RELAY_VERSION {
        return Err(anyhow!(
            "relay version mismatch: peer offered {}, expected {}",
            server_hello.version,
            RELAY_VERSION
        ));
    }
    if server_hello.falcon_vk.len() != FALCON_512_VK_LEN {
        return Err(anyhow!("relay server Falcon vk has the wrong length"));
    }
    if server_hello.slh_dsa_vk.len() != SLH_DSA_SHAKE128F_VK_LEN {
        return Err(anyhow!("relay server SLH-DSA vk has the wrong length"));
    }
    if server_hello.kem_ciphertext.len() != ML_KEM_768_CT_LEN {
        return Err(anyhow!("relay server KEM ciphertext has the wrong length"));
    }

    // Pin check BEFORE the signature check. The signature below is verified
    // under the key the server just sent; only the pin says that key is the
    // right one. Public values, so a plain comparison is fine.
    let presented = compute_identity_fingerprint(&server_hello.falcon_vk, &server_hello.slh_dsa_vk);
    match policy {
        PinPolicy::Require(pin) => {
            if &presented != pin.as_bytes() {
                return Err(anyhow!(
                    "relay server identity mismatch: pinned {pin}, peer presented {}; \
                     refusing the session (possible on-path impersonation)",
                    format_fingerprint(&presented)
                ));
            }
        }
        PinPolicy::Unpinned => {
            warn!(
                "relay client is UNPINNED: accepting server identity {} without verifying it",
                format_fingerprint(&presented)
            );
        }
    }

    let transcript = relay_transcript(
        &client_random,
        &server_hello.server_random,
        &kem.ek_bytes,
        &server_hello.kem_ciphertext,
        identity.falcon_pk_bytes(),
        &server_hello.falcon_vk,
    );

    // Authenticate the server before deriving anything from the exchange.
    let ok = PqKeyExchange::verify_falcon(
        &transcript,
        &server_hello.transcript_sig,
        &server_hello.falcon_vk,
    )?;
    if !ok {
        return Err(anyhow!(
            "relay server transcript signature did not verify; refusing the session"
        ));
    }

    let secret = kem.decapsulate(&server_hello.kem_ciphertext)?;

    // The client sends on c2s and receives on s2c.
    let link = RekeyLink::new();
    Ok(RelaySession {
        send: DirectionalCipher::new(
            &derive_directional_key(&secret, &transcript, KDF_LABEL_C2S),
            link.clone(),
        ),
        recv: DirectionalCipher::new(
            &derive_directional_key(&secret, &transcript, KDF_LABEL_S2C),
            link,
        ),
        peer_falcon_vk: server_hello.falcon_vk,
    })
}

/// Server side of the relay handshake. Admission runs in this order, all of it
/// before anything is spent on the peer: wire version and field lengths, the
/// client allow-list (finding R1), the hello signature (proof of possession,
/// which binds this `kem_ek` to the presented identity), freshness of the
/// signed timestamp, and first sight in the replay guard. Only then does the
/// server encapsulate.
pub async fn server_handshake(
    stream: &mut TcpStream,
    identity: &PqKeyExchange,
    clients: &ClientPolicy,
    guard: &Mutex<ReplayGuard>,
) -> Result<RelaySession> {
    let raw = read_len_prefixed(stream, MAX_HELLO_BYTES).await?;
    let hello: RelayHello = bincode::deserialize(&raw)?;

    if hello.version != RELAY_VERSION {
        return Err(anyhow!(
            "relay version mismatch: peer offered {}, expected {}",
            hello.version,
            RELAY_VERSION
        ));
    }
    if hello.kem_ek.len() != ML_KEM_768_EK_LEN {
        return Err(anyhow!("relay client KEM key has the wrong length"));
    }
    if hello.falcon_vk.len() != FALCON_512_VK_LEN {
        return Err(anyhow!("relay client Falcon vk has the wrong length"));
    }
    if hello.slh_dsa_vk.len() != SLH_DSA_SHAKE128F_VK_LEN {
        return Err(anyhow!("relay client SLH-DSA vk has the wrong length"));
    }

    // Allow-list first: a stranger costs one fingerprint hash, nothing more.
    let presented = compute_identity_fingerprint(&hello.falcon_vk, &hello.slh_dsa_vk);
    match clients {
        ClientPolicy::Authorized(list) => {
            if !list.iter().any(|p| p.as_bytes() == &presented) {
                return Err(anyhow!(
                    "relay client {} is not in the allow-list; refusing before encapsulation",
                    format_fingerprint(&presented)
                ));
            }
        }
        ClientPolicy::AnyClient => warn!(
            "relay server is OPEN to any client: accepting {} with no allow-list",
            format_fingerprint(&presented)
        ),
    }
    // Then proof of possession: the allow-list only proves the hello NAMES an
    // allowed key; the signature proves the sender HOLDS it and chose this
    // kem_ek.
    if !hello.verify_sig()? {
        return Err(anyhow!(
            "relay hello signature does not verify under the presented falcon_vk"
        ));
    }
    // Then freshness and first sight, so a recording is worthless.
    let skew = hello.timestamp.abs_diff(unix_now());
    if skew > HELLO_MAX_SKEW_SECS {
        return Err(anyhow!(
            "relay hello timestamp is {skew} s from server time (max {HELLO_MAX_SKEW_SECS} s): \
             stale, future-dated, or a replay"
        ));
    }
    {
        let mut guard = guard.lock().unwrap_or_else(|p| p.into_inner());
        match guard.check_and_insert(hello.client_random, Instant::now()) {
            Verdict::Fresh => {}
            Verdict::Replay => {
                return Err(anyhow!(
                "replayed relay hello: this client_random was already admitted inside the window"
            ))
            }
            Verdict::Full => {
                return Err(anyhow!(
                    "relay hello replay cache full at {} entries; refusing rather than reopening \
                     the replay window",
                    guard.len()
                ))
            }
        }
    }

    let (kem_ct, secret) = encapsulate_to(&hello.kem_ek)?;
    let server_random = random_bytes::<32>();

    let transcript = relay_transcript(
        &hello.client_random,
        &server_random,
        &hello.kem_ek,
        &kem_ct,
        &hello.falcon_vk,
        identity.falcon_pk_bytes(),
    );
    let transcript_sig = identity.sign_transcript(&transcript)?;

    let server_hello = RelayServerHello {
        version: RELAY_VERSION.to_string(),
        server_random,
        falcon_vk: identity.falcon_pk_bytes().to_vec(),
        slh_dsa_vk: identity.slh_dsa_pk_bytes().to_vec(),
        kem_ciphertext: kem_ct,
        transcript_sig,
    };
    write_len_prefixed(stream, &bincode::serialize(&server_hello)?).await?;

    // The server sends on s2c and receives on c2s: the mirror of the client.
    let link = RekeyLink::new();
    Ok(RelaySession {
        send: DirectionalCipher::new(
            &derive_directional_key(&secret, &transcript, KDF_LABEL_S2C),
            link.clone(),
        ),
        recv: DirectionalCipher::new(
            &derive_directional_key(&secret, &transcript, KDF_LABEL_C2S),
            link,
        ),
        peer_falcon_vk: hello.falcon_vk,
    })
}

// ---------------------------------------------------------------------------
// Full-duplex splice
// ---------------------------------------------------------------------------

/// Carry bytes both ways between a plaintext socket and an encrypted peer
/// socket until either side closes.
///
/// Runs two independent tasks. Neither holds a lock, because each owns one
/// directional cipher. When either direction ends, both are dropped, which
/// closes the sockets and unblocks the other task.
pub async fn splice(
    plain: TcpStream,
    encrypted: TcpStream,
    session: RelaySession,
) -> Result<(u64, u64)> {
    splice_with_idle_timeout(plain, encrypted, session, IDLE_TIMEOUT).await
}

/// [`splice`] with the idle timeout given explicitly.
///
/// Exists so the reaper can be tested in milliseconds rather than ten minutes.
/// Prefer [`splice`] everywhere else, so every connection in the fleet shares
/// one policy.
pub async fn splice_with_idle_timeout(
    plain: TcpStream,
    encrypted: TcpStream,
    session: RelaySession,
    idle: Duration,
) -> Result<(u64, u64)> {
    let (mut plain_r, mut plain_w) = plain.into_split();
    let (mut enc_r, mut enc_w) = encrypted.into_split();
    let RelaySession {
        mut send, mut recv, ..
    } = session;

    // plaintext in, sealed out
    let outbound = tokio::spawn(async move {
        let mut buf = vec![0u8; CHUNK_BYTES];
        let mut total = 0u64;
        let mut records = 0u64;
        loop {
            let n = match tokio::time::timeout(idle, plain_r.read(&mut buf)).await {
                Err(_) => {
                    debug!("relay: plaintext side idle for {idle:?}, reaping");
                    break;
                }
                Ok(Ok(0)) => break,
                Ok(Ok(n)) => n,
                Ok(Err(e)) => {
                    debug!("relay: plaintext read ended: {e}");
                    break;
                }
            };
            let epoch_before = send.epoch();
            let record = match send.seal(&buf[..n]) {
                Ok(r) => r,
                Err(e) => {
                    warn!("relay: seal failed: {e}");
                    break;
                }
            };
            records += 1;
            // The rekey is silent by design, so say so out loud. This is the
            // path qssh failed at 508 times out of 508, and a soak that cannot
            // show it happening has not tested it.
            if send.epoch() != epoch_before {
                info!(
                    "relay: RATCHET send epoch {} -> {} after {records} records, {}",
                    epoch_before,
                    send.epoch(),
                    if send.last_ratchet_fresh() {
                        "with fresh ML-KEM material, no round trip"
                    } else {
                        "HASH-ONLY (peer offered no key)"
                    }
                );
            }
            if write_len_prefixed(&mut enc_w, &record).await.is_err() {
                break;
            }
            total += n as u64;
        }
        let _ = enc_w.shutdown().await;
        total
    });

    // sealed in, plaintext out
    let inbound = tokio::spawn(async move {
        let mut total = 0u64;
        let mut records = 0u64;
        loop {
            let record =
                match tokio::time::timeout(idle, read_len_prefixed(&mut enc_r, MAX_RECORD_BYTES))
                    .await
                {
                    Err(_) => {
                        debug!("relay: encrypted side idle for {idle:?}, reaping");
                        break;
                    }
                    Ok(Ok(r)) => r,
                    Ok(Err(_)) => break,
                };
            let epoch_before = recv.epoch();
            let plaintext = match recv.open(&record) {
                Ok(p) => p,
                Err(e) => {
                    // A failure here is authentication failing, not a hiccup.
                    warn!("relay: rejecting record: {e}");
                    break;
                }
            };
            records += 1;
            if recv.epoch() != epoch_before {
                info!(
                    "relay: RATCHET recv epoch {} -> {} after {records} records, {}",
                    epoch_before,
                    recv.epoch(),
                    if recv.last_ratchet_fresh() {
                        "with fresh ML-KEM material, in step with the peer"
                    } else {
                        "HASH-ONLY (we had offered no key)"
                    }
                );
            }
            if !plaintext.is_empty() && plain_w.write_all(&plaintext).await.is_err() {
                break;
            }
            total += plaintext.len() as u64;
        }
        let _ = plain_w.shutdown().await;
        total
    });

    let sent = outbound.await.unwrap_or(0);
    let received = inbound.await.unwrap_or(0);
    Ok((sent, received))
}

// ---------------------------------------------------------------------------
// Server and client entry points
// ---------------------------------------------------------------------------

/// Relay server: accept encrypted connections, dial a plaintext backend.
///
/// One socket, one task, one key schedule per connection. Nothing is shared
/// between connections, which is what lets this scale past the point where the
/// old tunnel design failed.
pub struct RelayServer {
    identity: Arc<PqKeyExchange>,
    backend: SocketAddr,
    max_connections: usize,
    live: Arc<AtomicU64>,
    per_ip: Arc<Mutex<HashMap<IpAddr, u32>>>,
    /// Which clients may open a tunnel (finding R1).
    clients: Arc<ClientPolicy>,
    /// Admitted hello identifiers inside the freshness window (replay guard).
    guard: Arc<Mutex<ReplayGuard>>,
}

impl RelayServer {
    pub fn new(
        identity: Arc<PqKeyExchange>,
        backend: SocketAddr,
        max_connections: usize,
        clients: ClientPolicy,
    ) -> Self {
        Self {
            identity,
            backend,
            max_connections,
            live: Arc::new(AtomicU64::new(0)),
            per_ip: Arc::new(Mutex::new(HashMap::new())),
            clients: Arc::new(clients),
            guard: Arc::new(Mutex::new(ReplayGuard::new(
                HELLO_REPLAY_WINDOW,
                HELLO_REPLAY_CACHE_ENTRIES,
            ))),
        }
    }

    /// Number of connections currently being relayed. Library API (tests and
    /// operators' tooling); the binary itself never asks, hence the bin-side
    /// allow.
    #[allow(dead_code)]
    pub fn live_connections(&self) -> u64 {
        self.live.load(Ordering::Relaxed)
    }

    pub async fn serve(&self, listener: TcpListener) -> Result<()> {
        info!(
            "relay listening on {}, forwarding to {}, identity {} (clients pin this)",
            listener.local_addr()?,
            self.backend,
            ServerPin::of(&self.identity)
        );
        match self.clients.as_ref() {
            ClientPolicy::Authorized(list) => {
                info!("relay accepts {} allow-listed client(s)", list.len())
            }
            ClientPolicy::AnyClient => warn!(
                "relay accepts ANY client that signs its hello: the backend is reachable by \
                 anyone who can reach this port"
            ),
        }
        loop {
            let (stream, peer) = match listener.accept().await {
                Ok(v) => v,
                Err(e) => {
                    warn!("relay accept failed: {e}");
                    tokio::time::sleep(std::time::Duration::from_millis(100)).await;
                    continue;
                }
            };

            if self.live.load(Ordering::Relaxed) >= self.max_connections as u64 {
                warn!(
                    "relay at capacity ({}), dropping {peer}",
                    self.max_connections
                );
                continue;
            }

            // Per-source cap: check without inserting, so a rejected IP does not
            // leave a zero entry behind (which a flood of one-shot sources could
            // otherwise use to grow the map).
            let ip = peer.ip();
            {
                let mut map = self.per_ip.lock().unwrap();
                let current = *map.get(&ip).unwrap_or(&0);
                if current >= MAX_CONNECTIONS_PER_IP {
                    warn!("relay: {ip} at per-source limit ({MAX_CONNECTIONS_PER_IP}), dropping {peer}");
                    continue;
                }
                *map.entry(ip).or_insert(0) += 1;
            }

            let identity = self.identity.clone();
            let backend = self.backend;
            let clients = self.clients.clone();
            let replay = self.guard.clone();
            self.live.fetch_add(1, Ordering::Relaxed);
            // The guard decrements both counters on drop, so the accounting is
            // correct even if the task below returns early or panics.
            let guard = ConnGuard {
                live: self.live.clone(),
                per_ip: self.per_ip.clone(),
                ip,
            };

            tokio::spawn(async move {
                let _guard = guard;
                if let Err(e) =
                    handle_inbound(stream, peer, identity, backend, clients, replay).await
                {
                    debug!("relay connection from {peer} ended: {e}");
                }
            });
        }
    }
}

async fn handle_inbound(
    mut stream: TcpStream,
    peer: SocketAddr,
    identity: Arc<PqKeyExchange>,
    backend: SocketAddr,
    clients: Arc<ClientPolicy>,
    guard: Arc<Mutex<ReplayGuard>>,
) -> Result<()> {
    configure_socket(&stream, "inbound");
    let session = match tokio::time::timeout(
        HANDSHAKE_TIMEOUT,
        server_handshake(&mut stream, &identity, &clients, &guard),
    )
    .await
    {
        Ok(r) => r?,
        Err(_) => {
            debug!(
                "relay: {peer} did not complete the handshake in {HANDSHAKE_TIMEOUT:?}, dropping"
            );
            return Ok(());
        }
    };
    let upstream = TcpStream::connect(backend)
        .await
        .with_context(|| format!("relay could not reach backend {backend}"))?;
    configure_socket(&upstream, "backend");
    debug!("relay: {peer} handshake complete, spliced to {backend}");
    let (sent, received) = splice(upstream, stream, session).await?;
    debug!("relay: {peer} closed after {sent} bytes out, {received} bytes in");
    Ok(())
}

/// Relay client: accept plaintext locally, carry it to a remote relay server.
pub struct RelayClient {
    identity: Arc<PqKeyExchange>,
    remote: SocketAddr,
    policy: PinPolicy,
}

impl RelayClient {
    pub fn new(identity: Arc<PqKeyExchange>, remote: SocketAddr, policy: PinPolicy) -> Self {
        Self {
            identity,
            remote,
            policy,
        }
    }

    pub async fn serve(&self, listener: TcpListener) -> Result<()> {
        match self.policy {
            PinPolicy::Require(pin) => info!(
                "relay client listening on {}, tunnelling to {}, server pinned to {pin}",
                listener.local_addr()?,
                self.remote
            ),
            PinPolicy::Unpinned => warn!(
                "relay client listening on {}, tunnelling to {}, server identity UNPINNED: \
                 this client cannot tell the real server from an on-path impostor",
                listener.local_addr()?,
                self.remote
            ),
        }
        loop {
            let (local, peer) = match listener.accept().await {
                Ok(v) => v,
                Err(e) => {
                    warn!("relay client accept failed: {e}");
                    tokio::time::sleep(std::time::Duration::from_millis(100)).await;
                    continue;
                }
            };
            let identity = self.identity.clone();
            let remote = self.remote;
            let policy = self.policy;
            tokio::spawn(async move {
                if let Err(e) = handle_outbound(local, identity, remote, policy).await {
                    debug!("relay client connection from {peer} ended: {e}");
                }
            });
        }
    }
}

async fn handle_outbound(
    local: TcpStream,
    identity: Arc<PqKeyExchange>,
    remote: SocketAddr,
    policy: PinPolicy,
) -> Result<()> {
    configure_socket(&local, "local");
    let mut upstream = TcpStream::connect(remote)
        .await
        .with_context(|| format!("relay client could not reach {remote}"))?;
    configure_socket(&upstream, "upstream");
    let session = client_handshake(&mut upstream, &identity, policy).await?;
    splice(local, upstream, session).await?;
    Ok(())
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use tokio::io::{AsyncReadExt, AsyncWriteExt};

    /// A plaintext TCP echo service, standing in for whatever the relay fronts.
    async fn spawn_echo() -> Result<SocketAddr> {
        let listener = TcpListener::bind("127.0.0.1:0").await?;
        let addr = listener.local_addr()?;
        tokio::spawn(async move {
            loop {
                let Ok((mut s, _)) = listener.accept().await else {
                    break;
                };
                tokio::spawn(async move {
                    let mut buf = vec![0u8; 8192];
                    loop {
                        match s.read(&mut buf).await {
                            Ok(0) | Err(_) => break,
                            Ok(n) => {
                                if s.write_all(&buf[..n]).await.is_err() {
                                    break;
                                }
                            }
                        }
                    }
                });
            }
        });
        Ok(addr)
    }

    /// Stand up echo backend, relay server and relay client. Returns the
    /// address a caller should connect to, and the relay server's listen
    /// address so a test can inspect the encrypted leg directly.
    async fn spawn_relay_pair() -> Result<(SocketAddr, SocketAddr)> {
        let backend = spawn_echo().await?;

        // Every end-to-end test runs pinned AND allow-listed: the client
        // authenticates the server by its pin, the server authenticates the
        // client by its fingerprint and signed hello. Nothing else is the
        // configuration the relay is meant to run in.
        let client_identity = Arc::new(PqKeyExchange::new()?);
        let server_identity = Arc::new(PqKeyExchange::new()?);
        let server_pin = ServerPin::of(&server_identity);
        let server_listener = TcpListener::bind("127.0.0.1:0").await?;
        let server_addr = server_listener.local_addr()?;
        let server = RelayServer::new(
            server_identity,
            backend,
            64,
            ClientPolicy::Authorized(vec![ServerPin::of(&client_identity)]),
        );
        tokio::spawn(async move {
            let _ = server.serve(server_listener).await;
        });

        let client_listener = TcpListener::bind("127.0.0.1:0").await?;
        let client_addr = client_listener.local_addr()?;
        let client = RelayClient::new(client_identity, server_addr, PinPolicy::Require(server_pin));
        tokio::spawn(async move {
            let _ = client.serve(client_listener).await;
        });

        // Let both listeners come up.
        tokio::time::sleep(std::time::Duration::from_millis(60)).await;
        Ok((client_addr, server_addr))
    }

    #[tokio::test]
    async fn bytes_traverse_the_relay_end_to_end() {
        let (entry, _) = spawn_relay_pair().await.expect("relay pair");
        let mut c = TcpStream::connect(entry).await.expect("connect");

        let payload = b"quantumharmony block announce, or anything else over TCP";
        c.write_all(payload).await.expect("write");

        let mut got = vec![0u8; payload.len()];
        c.read_exact(&mut got).await.expect("read");
        assert_eq!(&got, payload, "payload must survive the round trip intact");
    }

    #[tokio::test]
    async fn the_wire_between_relays_is_not_plaintext() {
        // The property that matters. Connect straight to the relay server,
        // perform the handshake as a legitimate client would, then confirm
        // that what actually crosses the socket is not the payload.
        let backend = spawn_echo().await.expect("echo");
        let server_identity = Arc::new(PqKeyExchange::new().expect("id"));
        let server_pin = ServerPin::of(&server_identity);
        let listener = TcpListener::bind("127.0.0.1:0").await.expect("bind");
        let server_addr = listener.local_addr().expect("addr");
        let server = RelayServer::new(server_identity, backend, 8, ClientPolicy::AnyClient);
        tokio::spawn(async move {
            let _ = server.serve(listener).await;
        });
        tokio::time::sleep(std::time::Duration::from_millis(60)).await;

        let client_identity = PqKeyExchange::new().expect("id");
        let mut sock = TcpStream::connect(server_addr).await.expect("connect");
        let mut session =
            client_handshake(&mut sock, &client_identity, PinPolicy::Require(server_pin))
                .await
                .expect("handshake");

        let secret = b"SECRETMARKER-do-not-let-this-appear-on-the-wire";
        let record = session.send.seal(secret).expect("seal");

        assert!(
            !record.windows(secret.len()).any(|w| w == secret),
            "the sealed record must not contain the plaintext"
        );
        assert!(
            record.len() > secret.len(),
            "a sealed record carries nonce and tag"
        );
    }

    #[tokio::test]
    async fn a_tampered_record_is_rejected() {
        let a = PqKeyExchange::new().expect("id");
        let (mut c2s_send, mut c2s_recv) = paired_ciphers();
        let _ = a;

        let mut record = c2s_send.seal(b"authentic payload").expect("seal");
        let last = record.len() - 1;
        record[last] ^= 0x01;

        assert!(
            c2s_recv.open(&record).is_err(),
            "flipping one bit in the tag must fail authentication"
        );
    }

    #[tokio::test]
    async fn a_replayed_record_is_rejected() {
        let (mut send, mut recv) = paired_ciphers();
        let first = send.seal(b"record one").expect("seal");
        let second = send.seal(b"record two").expect("seal");

        recv.open(&first).expect("first record opens");
        assert!(
            recv.open(&first).is_err(),
            "replaying a record must be rejected, the counter has moved on"
        );
        // A rejected record must NOT desynchronise the session. `open` advances
        // the counter only on success, so an injected replay costs an attacker
        // nothing and costs the honest stream nothing either: the next genuine
        // record still opens.
        assert_eq!(
            recv.open(&second)
                .expect("the stream survives a rejected replay"),
            b"record two",
            "a rejected replay must not break the legitimate stream"
        );
    }

    #[tokio::test]
    async fn records_delivered_out_of_order_are_rejected() {
        let (mut send, mut recv) = paired_ciphers();
        let first = send.seal(b"one").expect("seal");
        let second = send.seal(b"two").expect("seal");

        assert!(
            recv.open(&second).is_err(),
            "a record arriving before its predecessor must be rejected"
        );
        let _ = first;
    }

    #[tokio::test]
    async fn the_two_directions_use_different_keys() {
        // If both directions shared a key and a counter, a record sealed by one
        // side could be opened by the other, and the nonce spaces would collide.
        let (mut c2s, _s2c_peer) = paired_ciphers();
        let (_c2s_peer, mut s2c) = paired_ciphers_from_same_secret();

        let record = c2s.seal(b"client to server").expect("seal");
        assert!(
            s2c.open(&record).is_err(),
            "a record sealed on c2s must not open with the s2c key"
        );
    }

    #[tokio::test]
    async fn an_oversized_frame_is_refused_before_allocation() {
        let (mut a, mut b) = tokio::io::duplex(64);
        // Claim a frame far larger than the cap.
        let huge = (MAX_RECORD_BYTES as u32 + 1).to_be_bytes();
        tokio::spawn(async move {
            let _ = a.write_all(&huge).await;
        });
        let err = read_len_prefixed(&mut b, MAX_RECORD_BYTES)
            .await
            .unwrap_err();
        assert!(
            err.to_string().contains("exceeds"),
            "the length cap must reject before allocating, got: {err}"
        );
    }

    #[tokio::test]
    async fn a_version_mismatch_is_refused() {
        // A peer speaking the gateway protocol must not be accepted as a relay
        // peer, and vice versa.
        let backend = spawn_echo().await.expect("echo");
        let identity = Arc::new(PqKeyExchange::new().expect("id"));
        let listener = TcpListener::bind("127.0.0.1:0").await.expect("bind");
        let addr = listener.local_addr().expect("addr");
        let server = RelayServer::new(identity, backend, 8, ClientPolicy::AnyClient);
        tokio::spawn(async move {
            let _ = server.serve(listener).await;
        });
        tokio::time::sleep(std::time::Duration::from_millis(60)).await;

        let mut sock = TcpStream::connect(addr).await.expect("connect");
        let bogus = RelayHello {
            version: "2.0".to_string(), // the gateway version, not the relay one
            client_random: [0u8; 32],
            kem_ek: vec![0u8; ML_KEM_768_EK_LEN],
            falcon_vk: vec![0u8; FALCON_512_VK_LEN],
            slh_dsa_vk: vec![0u8; SLH_DSA_SHAKE128F_VK_LEN],
            timestamp: 0,
            hello_sig: Vec::new(),
        };
        write_len_prefixed(&mut sock, &bincode::serialize(&bogus).unwrap())
            .await
            .expect("write");

        // The server must close rather than answer.
        let mut buf = [0u8; 4];
        let r = tokio::time::timeout(
            std::time::Duration::from_millis(500),
            sock.read_exact(&mut buf),
        )
        .await;
        assert!(
            matches!(r, Ok(Err(_)) | Err(_)),
            "a version mismatch must not receive a server hello"
        );
    }

    // ---- server identity pinning (Verifpal F2) --------------------------

    #[test]
    fn a_pin_round_trips_through_its_printed_form() {
        let id = PqKeyExchange::new().expect("id");
        let printed = format_fingerprint(&id.identity_fingerprint());
        let pin = ServerPin::parse(&printed).expect("parse");
        assert_eq!(pin, ServerPin::of(&id));
        assert_eq!(pin.to_string(), printed);
        // Padded base64 and surrounding whitespace are tolerated.
        let padded = format!("  {printed}=\n");
        assert_eq!(ServerPin::parse(&padded).expect("padded"), pin);
    }

    #[test]
    fn malformed_pins_are_refused() {
        for bad in [
            "",
            "SHA3-256:",
            "SHA3-256:not*base64",
            "SHA3-256:AAAA", // valid base64, wrong length
            "sha256:AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA",
            "deadbeef",
        ] {
            assert!(ServerPin::parse(bad).is_err(), "{bad:?} must be refused");
        }
    }

    #[tokio::test]
    async fn a_pinned_client_refuses_an_impostor_server() {
        // The impostor is genuine as far as the wire is concerned: its
        // transcript signature verifies under the key it sends. It is simply
        // not the server the client was told to expect. Before the pin this
        // handshake completed (Verifpal F2).
        let backend = spawn_echo().await.expect("echo");
        let impostor = Arc::new(PqKeyExchange::new().expect("impostor"));
        let listener = TcpListener::bind("127.0.0.1:0").await.expect("bind");
        let addr = listener.local_addr().expect("addr");
        let server = RelayServer::new(impostor, backend, 8, ClientPolicy::AnyClient);
        tokio::spawn(async move {
            let _ = server.serve(listener).await;
        });
        tokio::time::sleep(Duration::from_millis(60)).await;

        let expected = PqKeyExchange::new().expect("expected");
        let client_identity = PqKeyExchange::new().expect("client");
        let mut upstream = TcpStream::connect(addr).await.expect("connect");
        let err = match client_handshake(
            &mut upstream,
            &client_identity,
            PinPolicy::Require(ServerPin::of(&expected)),
        )
        .await
        {
            Ok(_) => panic!("an impostor must be refused"),
            Err(e) => e,
        };
        assert!(
            err.to_string().contains("identity mismatch"),
            "refusal must name the pin violation, got: {err}"
        );
    }

    #[tokio::test]
    async fn a_mispinned_relay_client_carries_nothing() {
        // Same failure through the full RelayClient path: bytes written into
        // the local plaintext side must never come back, because no session
        // is ever established with the wrong server.
        let backend = spawn_echo().await.expect("echo");
        let server_identity = Arc::new(PqKeyExchange::new().expect("server"));
        let server_listener = TcpListener::bind("127.0.0.1:0").await.expect("bind");
        let server_addr = server_listener.local_addr().expect("addr");
        let server = RelayServer::new(server_identity, backend, 8, ClientPolicy::AnyClient);
        tokio::spawn(async move {
            let _ = server.serve(server_listener).await;
        });

        let wrong_pin = ServerPin::of(&PqKeyExchange::new().expect("other"));
        let client_identity = Arc::new(PqKeyExchange::new().expect("client"));
        let client_listener = TcpListener::bind("127.0.0.1:0").await.expect("bind");
        let client_addr = client_listener.local_addr().expect("addr");
        let client = RelayClient::new(client_identity, server_addr, PinPolicy::Require(wrong_pin));
        tokio::spawn(async move {
            let _ = client.serve(client_listener).await;
        });
        tokio::time::sleep(Duration::from_millis(60)).await;

        let mut c = TcpStream::connect(client_addr).await.expect("connect");
        c.write_all(b"ping").await.expect("write");
        let mut back = [0u8; 4];
        let r = tokio::time::timeout(Duration::from_millis(500), c.read_exact(&mut back)).await;
        assert!(
            matches!(r, Ok(Err(_)) | Err(_)),
            "a mispinned client must close, not echo"
        );
    }

    #[tokio::test]
    async fn an_unpinned_client_still_connects_but_is_an_explicit_choice() {
        // The escape hatch exists for benches on trusted links. It must work,
        // and it must be the caller's explicit decision (there is no default).
        let backend = spawn_echo().await.expect("echo");
        let server_identity = Arc::new(PqKeyExchange::new().expect("server"));
        let listener = TcpListener::bind("127.0.0.1:0").await.expect("bind");
        let addr = listener.local_addr().expect("addr");
        let server = RelayServer::new(server_identity, backend, 8, ClientPolicy::AnyClient);
        tokio::spawn(async move {
            let _ = server.serve(listener).await;
        });
        tokio::time::sleep(Duration::from_millis(60)).await;

        let client_identity = PqKeyExchange::new().expect("client");
        let mut upstream = TcpStream::connect(addr).await.expect("connect");
        client_handshake(&mut upstream, &client_identity, PinPolicy::Unpinned)
            .await
            .expect("unpinned handshake completes");
    }

    // ---- client authentication (Verifpal R1, backlog B10) ----------------

    /// Accept exactly one connection and run the server handshake on it with
    /// the given client policy and replay guard. Returns the address to dial
    /// and the handshake's outcome, so a test can assert on the server's
    /// reason for refusing.
    async fn accept_one(
        identity: Arc<PqKeyExchange>,
        clients: ClientPolicy,
        guard: Arc<Mutex<ReplayGuard>>,
    ) -> (SocketAddr, tokio::task::JoinHandle<Result<RelaySession>>) {
        let listener = TcpListener::bind("127.0.0.1:0").await.expect("bind");
        let addr = listener.local_addr().expect("addr");
        let handle = tokio::spawn(async move {
            let (mut s, _) = listener.accept().await?;
            server_handshake(&mut s, &identity, &clients, &guard).await
        });
        (addr, handle)
    }

    fn fresh_guard() -> Arc<Mutex<ReplayGuard>> {
        Arc::new(Mutex::new(ReplayGuard::new(HELLO_REPLAY_WINDOW, 16)))
    }

    /// A hello exactly as `client_handshake` would build it, for tests that
    /// need to tamper with one before sending it.
    fn signed_hello(identity: &PqKeyExchange, timestamp: u64) -> RelayHello {
        let kem = EphemeralKemKey::new().expect("kem");
        let mut hello = RelayHello {
            version: RELAY_VERSION.to_string(),
            client_random: random_bytes::<32>(),
            kem_ek: kem.ek_bytes.clone(),
            falcon_vk: identity.falcon_pk_bytes().to_vec(),
            slh_dsa_vk: identity.slh_dsa_pk_bytes().to_vec(),
            timestamp,
            hello_sig: Vec::new(),
        };
        hello.sign(identity).expect("sign hello");
        hello
    }

    async fn send_raw_hello(addr: SocketAddr, hello: &RelayHello) -> TcpStream {
        let mut sock = TcpStream::connect(addr).await.expect("connect");
        write_len_prefixed(&mut sock, &bincode::serialize(hello).unwrap())
            .await
            .expect("write hello");
        sock
    }

    /// The R1 attack, refused at the door: a client the server was not told
    /// about, presenting a perfectly well-formed, self-signed hello.
    #[tokio::test]
    async fn an_unauthorized_client_is_refused_before_encapsulation() {
        let server_identity = Arc::new(PqKeyExchange::new().expect("server"));
        let server_pin = ServerPin::of(&server_identity);
        let allowed = PqKeyExchange::new().expect("allowed client");
        let stranger = PqKeyExchange::new().expect("stranger");
        let (addr, outcome) = accept_one(
            server_identity,
            ClientPolicy::Authorized(vec![ServerPin::of(&allowed)]),
            fresh_guard(),
        )
        .await;

        let mut sock = TcpStream::connect(addr).await.expect("connect");
        // The stranger's own handshake fails (the server closes on it); what
        // matters is the server's stated reason.
        let _ = client_handshake(&mut sock, &stranger, PinPolicy::Require(server_pin)).await;
        let err = outcome
            .await
            .expect("join")
            .expect_err("stranger must be refused");
        assert!(err.to_string().contains("allow-list"), "got: {err}");
    }

    #[tokio::test]
    async fn an_allow_listed_client_completes_the_handshake() {
        let server_identity = Arc::new(PqKeyExchange::new().expect("server"));
        let server_pin = ServerPin::of(&server_identity);
        let client = PqKeyExchange::new().expect("client");
        let (addr, outcome) = accept_one(
            server_identity,
            ClientPolicy::Authorized(vec![ServerPin::of(&client)]),
            fresh_guard(),
        )
        .await;
        let mut sock = TcpStream::connect(addr).await.expect("connect");
        client_handshake(&mut sock, &client, PinPolicy::Require(server_pin))
            .await
            .expect("allow-listed client completes");
        outcome.await.expect("join").expect("server side completes");
    }

    /// An attacker who knows an allow-listed client's PUBLIC keys presents them
    /// with a hello signed by its own key: passes the allow-list, fails the
    /// signature. (Without the signature this was the F1-shaped attack on the
    /// relay: the server would have encapsulated to the attacker's KEM key.)
    #[tokio::test]
    async fn a_hello_signed_by_another_identity_is_refused() {
        let server_identity = Arc::new(PqKeyExchange::new().expect("server"));
        let victim = PqKeyExchange::new().expect("victim");
        let attacker = PqKeyExchange::new().expect("attacker");
        let (addr, outcome) = accept_one(
            server_identity,
            ClientPolicy::Authorized(vec![ServerPin::of(&victim)]),
            fresh_guard(),
        )
        .await;

        let mut hello = signed_hello(&victim, unix_now());
        let attacker_kem = EphemeralKemKey::new().expect("kem");
        hello.kem_ek = attacker_kem.ek_bytes.clone();
        hello.hello_sig = attacker.sign_transcript(&hello.digest()).expect("sig");
        let _sock = send_raw_hello(addr, &hello).await;
        let err = outcome
            .await
            .expect("join")
            .expect_err("forged hello must be refused");
        assert!(err.to_string().contains("signature"), "got: {err}");
    }

    #[tokio::test]
    async fn a_stale_or_future_dated_hello_is_refused() {
        for offset in [
            -(HELLO_MAX_SKEW_SECS as i64) - 1,
            HELLO_MAX_SKEW_SECS as i64 + 1,
        ] {
            let server_identity = Arc::new(PqKeyExchange::new().expect("server"));
            let client = PqKeyExchange::new().expect("client");
            let (addr, outcome) = accept_one(
                server_identity,
                ClientPolicy::Authorized(vec![ServerPin::of(&client)]),
                fresh_guard(),
            )
            .await;
            let ts = (unix_now() as i64 + offset) as u64;
            let hello = signed_hello(&client, ts);
            let _sock = send_raw_hello(addr, &hello).await;
            let err = outcome
                .await
                .expect("join")
                .expect_err("stale hello must be refused");
            assert!(
                err.to_string().contains("timestamp"),
                "offset {offset}: got: {err}"
            );
        }
    }

    /// The replay Verifpal reported on the authenticated model: the same honest
    /// hello presented twice. First sight is admitted, the recording is refused.
    #[tokio::test]
    async fn a_replayed_hello_is_refused() {
        let server_identity = Arc::new(PqKeyExchange::new().expect("server"));
        let client = PqKeyExchange::new().expect("client");
        let guard = fresh_guard();
        let policy = ClientPolicy::Authorized(vec![ServerPin::of(&client)]);
        let hello = signed_hello(&client, unix_now());

        let (addr, first) =
            accept_one(server_identity.clone(), policy.clone(), guard.clone()).await;
        let _s1 = send_raw_hello(addr, &hello).await;
        first.await.expect("join").expect("first sight is admitted");

        let (addr, second) = accept_one(server_identity, policy, guard).await;
        let _s2 = send_raw_hello(addr, &hello).await;
        let err = second
            .await
            .expect("join")
            .expect_err("the recording must be refused");
        assert!(err.to_string().contains("replayed"), "got: {err}");
    }

    #[tokio::test]
    async fn many_concurrent_connections_are_independent() {
        // The property the old tunnel design could not provide: several
        // simultaneous inbound connections, each with its own key schedule.
        let (entry, _) = spawn_relay_pair().await.expect("relay pair");

        let mut handles = Vec::new();
        for i in 0..16u8 {
            handles.push(tokio::spawn(async move {
                let mut c = TcpStream::connect(entry).await.expect("connect");
                let payload = vec![i; 512];
                c.write_all(&payload).await.expect("write");
                let mut got = vec![0u8; payload.len()];
                c.read_exact(&mut got).await.expect("read");
                assert_eq!(
                    got, payload,
                    "connection {i} got another connection's bytes"
                );
            }));
        }
        for h in handles {
            h.await.expect("connection task");
        }
    }

    // ---- ratchet -----------------------------------------------------------

    #[tokio::test]
    async fn the_two_ends_ratchet_in_step_without_exchanging_anything() {
        // The whole point. qssh's in-band rekey races the forwarding reader and
        // desyncs (their client.rs:120); 508 of 508 production rekeys failed.
        // Here nothing crosses the wire, so there is nothing to race.
        let (mut send, mut recv) = paired_ciphers();
        assert_eq!(send.epoch(), 0);

        // Push past one full epoch and well into the next.
        let total = REKEY_EVERY_RECORDS + 1_000;
        for i in 0..total {
            let record = send.seal(b"x").expect("seal");
            let out = recv.open(&record).unwrap_or_else(|e| {
                panic!("record {i} failed after ratchet at {REKEY_EVERY_RECORDS}: {e}")
            });
            assert_eq!(out, b"x");
        }

        assert_eq!(send.epoch(), 1, "sender should have advanced one epoch");
        assert_eq!(
            recv.epoch(),
            send.epoch(),
            "both ends must sit in the same epoch, with no message between them"
        );
    }

    #[tokio::test]
    async fn the_ratchet_actually_changes_the_key() {
        let (mut a, _) = paired_ciphers();
        let (mut b, _) = paired_ciphers();

        // Advance `a` one epoch; leave `b` in epoch 0.
        for _ in 0..REKEY_EVERY_RECORDS {
            a.seal(b"x").expect("seal");
        }
        assert_eq!(a.epoch(), 1);
        assert_eq!(b.epoch(), 0);

        let after = a.seal(b"same plaintext").expect("seal");
        let before = b.seal(b"same plaintext").expect("seal");
        assert_ne!(
            after[12..],
            before[12..],
            "the same plaintext must not encrypt identically across epochs"
        );
    }

    #[tokio::test]
    async fn nonces_never_repeat_across_an_epoch_boundary() {
        // The counter restarts each epoch, so the epoch must be inside the
        // nonce or a nonce would repeat under a new key.
        let (mut send, _) = paired_ciphers();
        let first_ever = send.seal(b"first").expect("seal")[..12].to_vec();
        for _ in 1..REKEY_EVERY_RECORDS {
            send.seal(b"x").expect("seal");
        }
        assert_eq!(send.epoch(), 1, "should have just ratcheted");
        let first_of_epoch_one = send.seal(b"first again").expect("seal")[..12].to_vec();

        assert_ne!(
            first_ever, first_of_epoch_one,
            "the first nonce of a new epoch must differ from the first of the last"
        );
        assert_eq!(
            &first_ever[..4],
            &[0, 0, 0, 0],
            "epoch 0 in the top four bytes"
        );
        assert_eq!(
            &first_of_epoch_one[..4],
            &[0, 0, 0, 1],
            "epoch 1 in the top four bytes"
        );
    }

    #[tokio::test]
    async fn a_rejected_record_does_not_advance_the_ratchet() {
        // If a rejected record moved the counter, an attacker could push one
        // side into a different epoch and break the session for free.
        let (mut send, mut recv) = paired_ciphers();
        let good = send.seal(b"legitimate").expect("seal");

        let mut tampered = good.clone();
        let last = tampered.len() - 1;
        tampered[last] ^= 0xff;
        assert!(recv.open(&tampered).is_err());

        assert_eq!(
            recv.open(&good).expect("the genuine record still opens"),
            b"legitimate",
            "a rejected record must leave the session usable"
        );
        assert_eq!(recv.epoch(), 0, "a rejected record must not move the epoch");
    }

    #[tokio::test]
    async fn a_long_lived_connection_survives_several_ratchets() {
        // A validator link lives for days. Prove several epochs in a row rather
        // than only the first boundary.
        let (mut send, mut recv) = paired_ciphers();
        let total = REKEY_EVERY_RECORDS * 3 + 5;
        for i in 0..total {
            let r = send.seal(&i.to_be_bytes()).expect("seal");
            let out = recv.open(&r).unwrap_or_else(|e| panic!("record {i}: {e}"));
            assert_eq!(out, i.to_be_bytes());
        }
        assert_eq!(send.epoch(), 3);
        assert_eq!(recv.epoch(), 3);
    }

    // -- helpers -------------------------------------------------------------

    /// Two ciphers sharing one key: a send half and the matching receive half.
    fn paired_ciphers() -> (DirectionalCipher, DirectionalCipher) {
        // Two endpoints, one direction: the sender's link and the receiver's
        // link are different endpoints' links. The receiver never sends, so it
        // never offers a key and every ratchet on this pair is hash-only.
        let key = [7u8; 32];
        (
            DirectionalCipher::new(&key, RekeyLink::new()),
            DirectionalCipher::new(&key, RekeyLink::new()),
        )
    }

    /// Two full endpoints A and B, both directions wired, small epochs, so the
    /// KEM re-injection can be exercised in a handful of records.
    #[allow(clippy::type_complexity)]
    fn full_duplex_pair(
        records_per_epoch: u64,
    ) -> (
        (DirectionalCipher, DirectionalCipher),
        (DirectionalCipher, DirectionalCipher),
    ) {
        let k_ab = [1u8; 32];
        let k_ba = [2u8; 32];
        let link_a = RekeyLink::new();
        let link_b = RekeyLink::new();
        let mut a_send = DirectionalCipher::new(&k_ab, link_a.clone());
        let mut a_recv = DirectionalCipher::new(&k_ba, link_a);
        let mut b_send = DirectionalCipher::new(&k_ba, link_b.clone());
        let mut b_recv = DirectionalCipher::new(&k_ab, link_b);
        for c in [&mut a_send, &mut a_recv, &mut b_send, &mut b_recv] {
            c.records_per_epoch = records_per_epoch;
        }
        ((a_send, a_recv), (b_send, b_recv))
    }

    /// Hash-only next key, computed the way `ratchet(&[])` does, to check that
    /// a real ratchet did NOT take this path.
    fn hash_only_next(key: &[u8; 32], next_epoch: u32) -> [u8; 32] {
        let mut h = Sha3_256::new();
        h.update(RATCHET_LABEL);
        h.update(key);
        h.update(next_epoch.to_be_bytes());
        h.update(0u32.to_be_bytes());
        let mut out = [0u8; 32];
        out.copy_from_slice(&h.finalize());
        out
    }

    // ---- KEM re-injection (backlog B11) ------------------------------------

    /// Both directions flowing: A's first record offers a key to B, B's first
    /// record offers one to A, and at A's epoch boundary the COMMIT carries an
    /// encapsulation to B's offer. Both sides enter epoch 1 with fresh
    /// material, and B immediately owes A a new offer.
    #[tokio::test]
    async fn a_full_duplex_pair_rekeys_with_fresh_kem_material() {
        let ((mut a_send, mut a_recv), (mut b_send, mut b_recv)) = full_duplex_pair(4);

        // B -> A first, so A holds B's offer before A's boundary.
        let r = b_send.seal(b"hello from b").expect("seal");
        assert_eq!(a_recv.open(&r).expect("open"), b"hello from b");

        let k0 = a_send.key;
        for i in 0..4u8 {
            let r = a_send.seal(&[i]).expect("seal");
            assert_eq!(b_recv.open(&r).expect("open"), [i]);
        }
        assert_eq!(a_send.epoch(), 1);
        assert_eq!(b_recv.epoch(), 1);
        assert_eq!(
            a_send.ratchet_counts(),
            (1, 0),
            "A ratcheted with fresh material"
        );
        assert_eq!(
            b_recv.ratchet_counts(),
            (1, 0),
            "B followed with the same material"
        );
        assert_eq!(
            a_send.key, b_recv.key,
            "both sides hold the same epoch-1 key"
        );
        assert_ne!(
            a_send.key,
            hash_only_next(&k0, 1),
            "post-compromise security: epoch 1 is not a function of epoch 0 alone"
        );

        // B now owes A a fresh offer; it rides on B's next record.
        let r = b_send.seal(b"again").expect("seal");
        assert_eq!(a_recv.open(&r).expect("open"), b"again");
        assert!(
            a_send.lock_link().peer_ek.is_some(),
            "A must hold a new offer from B for its next boundary"
        );
    }

    /// The property in the model (`pqtg-relay-ratchet-kem-leak-k0.vp`): an
    /// attacker holding epoch 0's key cannot derive epoch 1 when a KEM step
    /// happened, because the shared secret never crossed the wire in clear.
    #[tokio::test]
    async fn an_early_epoch_key_does_not_yield_a_kem_ratcheted_epoch() {
        let ((mut a_send, mut a_recv), (mut b_send, mut b_recv)) = full_duplex_pair(2);
        let r = b_send.seal(b"offer").expect("seal");
        a_recv.open(&r).expect("open");
        let leaked_k0 = a_send.key;
        for i in 0..2u8 {
            let r = a_send.seal(&[i]).expect("seal");
            b_recv.open(&r).expect("open");
        }
        assert_eq!(a_send.epoch(), 1);
        // Everything an attacker with k0 could compute on its own:
        let guess = hash_only_next(&leaked_k0, 1);
        assert_ne!(a_send.key, guess);
        assert_ne!(b_recv.key, guess);
    }

    /// Without the reverse direction there is no offer, so the boundary is a
    /// hash-only step: the relay-2 behaviour, still in step, and counted.
    #[tokio::test]
    async fn without_an_offer_the_ratchet_is_hash_only_and_still_in_step() {
        let (mut send, mut recv) = paired_ciphers();
        send.records_per_epoch = 3;
        let k0 = send.key;
        for i in 0..3u8 {
            let r = send.seal(&[i]).expect("seal");
            assert_eq!(recv.open(&r).expect("open"), [i]);
        }
        assert_eq!(send.epoch(), 1);
        assert_eq!(recv.epoch(), 1);
        assert_eq!(send.ratchet_counts(), (0, 1));
        assert_eq!(recv.ratchet_counts(), (0, 1));
        assert_eq!(
            send.key,
            hash_only_next(&k0, 1),
            "hash-only step, as documented"
        );
        assert_eq!(send.key, recv.key);
    }

    /// A COMMIT carrying an encapsulation to a key this endpoint never offered
    /// is refused, not guessed at, and leaves the session where it was.
    #[tokio::test]
    async fn a_commit_against_no_offer_is_refused() {
        let ((mut a_send, _a_recv), (_b_send, mut b_recv)) = full_duplex_pair(2);
        // Give A an offer from a THIRD party, not from B.
        let stray = EphemeralKemKey::new().expect("kem");
        a_send.lock_link().peer_ek = Some(stray.ek_bytes.clone());
        let r0 = a_send.seal(b"x").expect("seal");
        b_recv.open(&r0).expect("first record opens");
        let r1 = a_send.seal(b"y").expect("seal (commit)");
        let err = b_recv.open(&r1).unwrap_err();
        assert!(err.to_string().contains("offered no key"), "got: {err}");
        assert_eq!(
            b_recv.epoch(),
            0,
            "a refused commit must not move the epoch"
        );
    }

    #[test]
    fn the_previous_epoch_key_is_zeroized_on_ratchet() {
        // Not a memory-forensics test, only that the field no longer holds the
        // old value once the epoch has moved.
        let (mut send, _) = paired_ciphers();
        send.records_per_epoch = 1;
        let k0 = send.key;
        send.seal(b"x").expect("seal");
        assert_eq!(send.epoch(), 1);
        assert_ne!(send.key, k0);
    }

    #[tokio::test]
    async fn a_connection_where_nothing_moves_is_reaped() {
        // A peer that stops speaking without closing the socket used to hold a
        // task, two file descriptors and a slot in the live-connection count
        // forever, because both directions were blocked on reads that would
        // never return and never error.
        let listener = TcpListener::bind("127.0.0.1:0")
            .await
            .expect("bind encrypted");
        let addr = listener.local_addr().expect("encrypted addr");
        let server_identity = Arc::new(PqKeyExchange::new().expect("server identity"));
        let server_pin = ServerPin::of(&server_identity);
        let accepted = tokio::spawn(async move {
            let (mut s, _) = listener.accept().await.expect("accept encrypted");
            let guard = Mutex::new(ReplayGuard::new(HELLO_REPLAY_WINDOW, 16));
            let session =
                server_handshake(&mut s, &server_identity, &ClientPolicy::AnyClient, &guard)
                    .await
                    .expect("server handshake");
            (s, session)
        });

        let client_identity = PqKeyExchange::new().expect("client identity");
        let mut client = TcpStream::connect(addr).await.expect("connect encrypted");
        let client_session = client_handshake(
            &mut client,
            &client_identity,
            PinPolicy::Require(server_pin),
        )
        .await
        .expect("client handshake");
        // Held open deliberately: the far end is alive, it has simply gone quiet.
        let (_server_stream, _server_session) = accepted.await.expect("join server");

        let plain_listener = TcpListener::bind("127.0.0.1:0").await.expect("bind plain");
        let plain_addr = plain_listener.local_addr().expect("plain addr");
        let plain_accept =
            tokio::spawn(async move { plain_listener.accept().await.expect("accept plain").0 });
        let plain = TcpStream::connect(plain_addr).await.expect("connect plain");
        let _plain_peer = plain_accept.await.expect("join plain");

        let outcome = tokio::time::timeout(
            Duration::from_secs(5),
            splice_with_idle_timeout(plain, client, client_session, Duration::from_millis(200)),
        )
        .await;

        let (sent, received) = outcome
            .expect("splice hung on an idle connection instead of reaping it")
            .expect("splice returned an error");
        assert_eq!(
            (sent, received),
            (0, 0),
            "nothing crossed either direction, so nothing should be counted"
        );
    }

    #[tokio::test]
    async fn every_relay_socket_gets_keepalive_and_no_nagle() {
        // Both are set for a specific measured reason: Nagle cost 120 ms per
        // connection on a 16 ms link, and without keepalive a peer that dies
        // without a FIN is never noticed, so libp2p is never told to redial.
        let listener = TcpListener::bind("127.0.0.1:0").await.expect("bind");
        let addr = listener.local_addr().expect("addr");
        let accept = tokio::spawn(async move { listener.accept().await.expect("accept").0 });
        let stream = TcpStream::connect(addr).await.expect("connect");
        let _peer = accept.await.expect("join");

        configure_socket(&stream, "test");

        assert!(stream.nodelay().expect("read nodelay"), "Nagle must be off");
        assert!(
            SockRef::from(&stream).keepalive().expect("read keepalive"),
            "TCP keepalive must be on"
        );
    }

    /// The opposite direction derived from the same secret and transcript,
    /// which must produce a different key.
    fn paired_ciphers_from_same_secret() -> (DirectionalCipher, DirectionalCipher) {
        let secret = [9u8; 32];
        let transcript = [3u8; 32];
        let c2s = derive_directional_key(&secret, &transcript, KDF_LABEL_C2S);
        let s2c = derive_directional_key(&secret, &transcript, KDF_LABEL_S2C);
        assert_ne!(c2s, s2c, "directional keys must differ");
        (
            DirectionalCipher::new(&c2s, RekeyLink::new()),
            DirectionalCipher::new(&s2c, RekeyLink::new()),
        )
    }
}
