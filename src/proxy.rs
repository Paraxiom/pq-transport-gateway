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
        derive_session_key, encapsulate_to, mix_keys, random_bytes, transcript_hash, PqKeyExchange,
        PqSession, FALCON_512_VK_LEN, MIN_SESSION_FRAME_BYTES, ML_KEM_768_EK_LEN,
        SLH_DSA_SHAKE128F_VK_LEN,
    },
    qkd_client::QkdClient,
};
use anyhow::{anyhow, Context, Result};
use serde::{Deserialize, Serialize};
use std::net::SocketAddr;
use std::sync::Arc;
use tokio::io::{AsyncReadExt, AsyncWriteExt};
use tokio::net::TcpStream;
use tracing::{debug, error, info, warn};

#[derive(Clone)]
pub struct ProxyServer {
    config: Arc<Config>,
    qkd_client: Arc<QkdClient>,
    authenticator: Arc<Authenticator>,
    host_key: Arc<PqKeyExchange>,
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
const MAX_HELLO_BYTES: usize = 16 * 1024;
const MAX_REQUEST_BYTES: usize = 1024 * 1024;

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
        let session = PqSession::new(&session_key, random_bytes::<32>(), s.client_falcon_vk.clone())?;
        Ok((session, s.client_falcon_vk))
    }
}

impl Default for ServerHandshake<AwaitingHello> {
    fn default() -> Self {
        Self::new()
    }
}

impl ProxyServer {
    pub async fn new(config: Arc<Config>) -> Result<Self> {
        let qkd_client = QkdClient::new(&config)?;
        let host_key = Self::load_or_generate_identity(&config.security.proxy_private_key)?;
        let authenticator = Authenticator::new(&config)?;
        Ok(Self {
            config,
            qkd_client: Arc::new(qkd_client),
            authenticator: Arc::new(authenticator),
            host_key: Arc::new(host_key),
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
        // ── ClientHello ─────────────────────────────────────────────────────
        let client_hello: ClientHello = read_framed(stream, MAX_HELLO_BYTES).await?;
        if !client_hello.version.starts_with("2.") {
            return Err(anyhow!(
                "Unsupported protocol version: {}",
                client_hello.version
            ));
        }

        // ── Validate ClientHello field lengths (issue #5) ───────────────────
        if client_hello.kem_ek.len() != ML_KEM_768_EK_LEN {
            return Err(anyhow!(
                "ClientHello.kem_ek wrong size: expected {} bytes, got {}",
                ML_KEM_768_EK_LEN,
                client_hello.kem_ek.len()
            ));
        }
        if client_hello.falcon_vk.len() != FALCON_512_VK_LEN {
            return Err(anyhow!(
                "ClientHello.falcon_vk wrong size: expected {} bytes, got {}",
                FALCON_512_VK_LEN,
                client_hello.falcon_vk.len()
            ));
        }
        if client_hello.slh_dsa_vk.len() != SLH_DSA_SHAKE128F_VK_LEN {
            return Err(anyhow!(
                "ClientHello.slh_dsa_vk wrong size: expected {} bytes, got {}",
                SLH_DSA_SHAKE128F_VK_LEN,
                client_hello.slh_dsa_vk.len()
            ));
        }

        // ── Authorize the client (issue #1) ─────────────────────────────────
        // Falcon-512 vk + SLH-DSA-Shake128f vk pair must appear in
        // `authorized_keys`. Empty file ⇒ no one is authorized
        // (fail-closed). Done before any keypair generation / encapsulation
        // so an unauthorized peer doesn't get to exhaust crypto budget.
        match self
            .authenticator
            .verify_client(&client_hello.falcon_vk, &client_hello.slh_dsa_vk)
        {
            Ok(auth_key) => {
                debug!(
                    "Client authorized: key_id={} peer={}",
                    auth_key.key_id, peer_addr
                );
            }
            Err(e) => {
                audit::log_auth_failure(peer_addr, &e.to_string());
                warn!("Rejected unauthorized client {}: {}", peer_addr, e);
                return Err(anyhow!("Client not in authorized_keys"));
            }
        }

        // ── Type-state handshake: encapsulate, build + sign transcript ──────
        let handshake = ServerHandshake::new().respond(&client_hello, &self.host_key)?;
        write_framed(stream, handshake.server_hello()).await?;

        // ── Optional one-time QKD mixing ────────────────────────────────────
        let qkd_material = match self.qkd_client.get_key(32).await {
            Ok(qkd_key) => {
                audit::log_qkd_key_used(peer_addr, qkd_key.key_id());
                // Consume the key: QKD material is one-time, used exactly once.
                Some(qkd_key.into_material())
            }
            Err(_) => {
                warn!("QKD not available, using PQC-only mode");
                None
            }
        };

        // `into_session` is the ONLY way to obtain a live `PqSession`, so no
        // data can flow before the handshake has completed in order.
        let qkd_ref = qkd_material.as_ref().map(|m| m.as_slice());
        handshake.into_session(qkd_ref)
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

async fn read_framed<T: for<'de> Deserialize<'de>>(
    stream: &mut TcpStream,
    max: usize,
) -> Result<T> {
    let mut len_buf = [0u8; 4];
    stream.read_exact(&mut len_buf).await?;
    let len = u32::from_be_bytes(len_buf) as usize;
    if len > max {
        return Err(anyhow!("Frame too large: {len} > {max}"));
    }
    let mut buf = vec![0u8; len];
    stream.read_exact(&mut buf).await?;
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
        let client_ss = client_kem.decapsulate(&server_hello.kem_ciphertext).unwrap();
        let client_session_key = derive_session_key(&client_ss, &transcript);
        let client_session =
            PqSession::new(&client_session_key, random_bytes::<32>(), server_hello.falcon_vk)
                .unwrap();

        let (ct, nonce) = server_session.encrypt(b"quantum-safe hello").unwrap();
        let pt = client_session.decrypt(&ct, &nonce).unwrap();
        assert_eq!(pt, b"quantum-safe hello");
    }
}
