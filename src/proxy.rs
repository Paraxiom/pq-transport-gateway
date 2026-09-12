//! Main proxy server implementation.
//!
//! Wire protocol (v2, KEM-based):
//!   ClientHello { version, client_random, kem_ek, falcon_vk, slh_dsa_vk, requested_key_size }
//!   ServerHello { version, server_random, falcon_vk, slh_dsa_vk, kem_ciphertext, transcript_sig }
//!
//! Both sides derive `transcript = SHA3(client_random ‖ server_random ‖ kem_ek
//! ‖ server_falcon_vk ‖ kem_ciphertext)` and `session_key = SHA3("pqtg-session-v2"
//! ‖ kem_ss ‖ transcript)`. If the optional QKD key is available, the PQC
//! session key is mixed with it via `mix_keys`.

use crate::{
    audit,
    auth::Authenticator,
    config::Config,
    crypto::{
        derive_session_key, derive_session_key_v3, encapsulate_to, mix_keys, mix_keys_v3,
        random_bytes, transcript_hash, transcript_hash_v3, PqKeyExchange, PqSession,
        FALCON_512_VK_LEN, MIN_SESSION_FRAME_BYTES, ML_KEM_768_EK_LEN, SLH_DSA_SHAKE128F_VK_LEN,
    },
    qkd_client::QkdClient,
    replay::{ReplayGuard, Verdict},
};
use anyhow::{anyhow, Context, Result};
use serde::{Deserialize, Serialize};
use std::net::SocketAddr;
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};
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
    let mut guard = guard.lock().unwrap_or_else(|poisoned| poisoned.into_inner());
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
    /// SLH-DSA-Shake128f verification key (audit-grade hash-based identity).
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

const PROTOCOL_VERSION: &str = "2.0";
const PROTOCOL_VERSION_V3: &str = "3.0";
const MAX_HELLO_BYTES: usize = 16 * 1024;
const MAX_REQUEST_BYTES: usize = 1024 * 1024;
/// Sanity cap on the client-supplied SAE-ID (ETSI 014 SAE_IDs are short
/// logical labels; anything longer is malformed or hostile).
const MAX_SAE_ID_BYTES: usize = 256;

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
    /// ```compile_fail
    /// use pq_transport_gateway::proxy::ServerHandshake;
    /// use pq_transport_gateway::{ClientHello, PqKeyExchange};
    /// let host = PqKeyExchange::new().unwrap();
    /// let hello: ClientHello = unimplemented!();
    /// let hs = ServerHandshake::new().respond(&hello, &host).unwrap();
    /// let _session = hs.into_session(None);  // consumes the handshake
    /// let _ = hs.server_hello();             // error[E0382]: use of moved value
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

    /// Derive the v3 session. Hybrid: `mix_keys_v3(qkd, pqc, transcript)` —
    /// the combiner's context input is the v3 transcript, which commits the
    /// key_ID, mode, SAE-ID and length (CatKDF-style context binding; see
    /// docs/audit-vs-eprint-2025-1671.md). PqcOnly: the KEM secret directly.
    /// Consumes `self`; the only constructor of a live v3 session.
    pub fn into_session(self) -> Result<(PqSession, Vec<u8>)> {
        let s = self.state;
        let secret = match &s.qkd_material {
            Some(m) => mix_keys_v3(m, &s.pqc_secret, &s.transcript),
            None => s.pqc_secret,
        };
        let session_key = derive_session_key_v3(&secret, &s.transcript);
        let session = PqSession::new(
            &session_key,
            random_bytes::<32>(),
            s.client_falcon_vk.clone(),
        )?;
        Ok((session, s.client_falcon_vk))
    }
}

impl ProxyServer {
    pub async fn new(config: Arc<Config>) -> Result<Self> {
        let qkd_client = QkdClient::new(&config)?;
        let host_key = Self::load_or_generate_identity(&config.security.proxy_private_key)?;
        let authenticator = Authenticator::new(&config)?;
        // The guard must remember a hello for the whole interval in which its
        // timestamp is acceptable: 2 × skew after first sight (see replay.rs).
        let replay_guard = Arc::new(Mutex::new(ReplayGuard::new(
            Duration::from_secs(2 * config.proxy.hello_max_skew_secs),
            config.proxy.hello_replay_cache_entries,
        )));
        Ok(Self {
            config,
            qkd_client: Arc::new(qkd_client),
            authenticator: Arc::new(authenticator),
            host_key: Arc::new(host_key),
            replay_guard,
        })
    }

    /// Load the persisted identity file if present; otherwise generate a
    /// fresh ephemeral identity and warn loudly. Production deployments
    /// MUST run `--generate-keys` once to create a stable identity, since
    /// regenerating on every start invalidates client-side vk pinning
    /// (issue #2).
    fn load_or_generate_identity(path: &str) -> Result<PqKeyExchange> {
        match PqKeyExchange::load_if_present(path)? {
            Some(identity) => {
                info!("Loaded persisted PQTG identity from {}", path);
                Ok(identity)
            }
            None => {
                warn!(
                    "No persisted identity at {}; generating ephemeral identity. \
                     This is acceptable for development but MUST NOT be used \
                     in production — restart-stable identity is required for \
                     client vk pinning. Run `--generate-keys` to fix.",
                    path
                );
                PqKeyExchange::new()
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
        if peek.version.starts_with("3.") {
            self.handshake_v3(stream, peer_addr, &hello_bytes).await
        } else if peek.version.starts_with("2.") {
            self.handshake_v2(stream, peer_addr, &hello_bytes).await
        } else {
            Err(anyhow!("Unsupported protocol version: {}", peek.version))
        }
    }

    /// Shared ClientHello validation (issue #5) + authorization (issue #1).
    /// Authorization is fail-closed and runs before any encapsulation so an
    /// unauthorized peer cannot exhaust crypto budget — or, in v3, consume
    /// KMS keys (spec §7, DoS note).
    fn validate_and_authorize(
        &self,
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
                debug!(
                    "Client authorized: key_id={} peer={}",
                    auth_key.key_id, peer_addr
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
        self.validate_and_authorize(
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

        let handshake =
            ServerHandshake::new().respond_v3(&client_hello, &self.host_key, qkd, &master_sae_id)?;
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
                    "Request too small: {len} bytes (minimum {})",
                    MIN_SESSION_FRAME_BYTES
                ));
            }
            if len > MAX_REQUEST_BYTES {
                return Err(anyhow!("Request too large: {len} bytes"));
            }
            let mut encrypted = vec![0u8; len];
            stream.read_exact(&mut encrypted).await?;

            let request_bytes = session.decrypt_and_verify(&encrypted)?;
            let request: KeyRequest = bincode::deserialize(&request_bytes)?;
            audit::log_key_request(&peer_addr, &request.key_id, request.size);

            let response = self.process_key_request(request).await?;
            let response_bytes = bincode::serialize(&response)?;
            let encrypted_response =
                session.sign_and_encrypt(&response_bytes, self.host_key.falcon_signing_key())?;

            let len_bytes = (encrypted_response.len() as u32).to_be_bytes();
            stream.write_all(&len_bytes).await?;
            stream.write_all(&encrypted_response).await?;
            stream.flush().await?;
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
    let bytes = bincode::serialize(msg)?;
    let len_bytes = (bytes.len() as u32).to_be_bytes();
    stream.write_all(&len_bytes).await?;
    stream.write_all(&bytes).await?;
    stream.flush().await?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::crypto::EphemeralKemKey;

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
        // decrypts a server-encrypted message — proving both sides agree.
        let client_ss = client_kem
            .decapsulate(&server_hello.kem_ciphertext)
            .unwrap();
        let client_session_key = derive_session_key(&client_ss, &transcript);
        let client_session = PqSession::new(
            &client_session_key,
            random_bytes::<32>(),
            server_hello.falcon_vk,
        )
        .unwrap();

        let (ct, nonce) = server_session.encrypt(b"quantum-safe hello").unwrap();
        let pt = client_session.decrypt(&ct, &nonce).unwrap();
        assert_eq!(pt, b"quantum-safe hello");
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

    /// A small guard with a 240 s window (2 × the 120 s default skew).
    fn guard(max_entries: usize) -> Mutex<ReplayGuard> {
        Mutex::new(ReplayGuard::new(Duration::from_secs(240), max_entries))
    }

    /// Client-side v3 transcript reconstruction from wire data — what a real
    /// external client computes from its own hello + the ServerHelloV3.
    fn client_transcript_v3(
        hello: &ClientHelloV3,
        sh: &ServerHelloV3,
    ) -> [u8; 32] {
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
        let secret = mix_keys_v3(&qkd_bytes, &client_ss, &transcript);
        let client_key = derive_session_key_v3(&secret, &transcript);
        let client_session =
            PqSession::new(&client_key, random_bytes::<32>(), sh.falcon_vk.clone()).unwrap();

        let (ct, nonce) = server_session.encrypt(b"hybrid interop at last").unwrap();
        let pt = client_session.decrypt(&ct, &nonce).unwrap();
        assert_eq!(pt, b"hybrid interop at last");
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
        let client_key = derive_session_key_v3(&client_ss, &transcript);
        let client_session =
            PqSession::new(&client_key, random_bytes::<32>(), sh.falcon_vk.clone()).unwrap();

        let (ct, nonce) = server_session.encrypt(b"pqc-only ok").unwrap();
        assert_eq!(client_session.decrypt(&ct, &nonce).unwrap(), b"pqc-only ok");
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
        assert!(hello.verify_hello_sig().unwrap(), "an honest hello verifies");

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

        let mutations: Vec<(&str, Box<dyn Fn(&mut ClientHelloV3)>)> = vec![
            ("client_random", Box::new(|h| h.client_random[0] ^= 1)),
            ("timestamp", Box::new(|h| h.timestamp += 1)),
            ("kem_ek", Box::new(|h| h.kem_ek[0] ^= 1)),
            ("slh_dsa_vk", Box::new(|h| h.slh_dsa_vk[0] ^= 1)),
            ("requested_key_size", Box::new(|h| h.requested_key_size += 1)),
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
        assert!(err.to_string().contains("replayed"), "still inside the window: {err}");

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
        assert!(g.lock().unwrap().is_empty(), "a refused hello must not occupy a slot");
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
        assert!(g.lock().unwrap().is_empty(), "unauthenticated hellos never reach the cache");
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
