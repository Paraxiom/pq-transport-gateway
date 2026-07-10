//! Post-quantum cryptography for PQTG.
//!
//! Built on `paraxiom-pqc` (pure-Rust post-quantum primitives). Uses:
//! - ML-KEM-768 (FIPS 203) for the actual key encapsulation / shared-secret derivation
//! - Falcon-512 (pending FIPS 206) for compact handshake signatures
//! - SLH-DSA-Shake128f (FIPS 205) for hash-based stateless signatures (audit trail)
//! - AES-256-GCM for the symmetric session
//! - SHA3-256 for transcript hashing and key mixing
//!
//! Handshake (KEM-based, no longer signature-only):
//! 1. Client generates ML-KEM-768 keypair (ek, dk). Sends ek in ClientHello.
//! 2. Server encapsulates against ek → (ct, ss). Sends ct in ServerHello, signs
//!    transcript with Falcon-512.
//! 3. Client decapsulates ct with dk → same ss. Verifies server signature.
//! 4. Both sides derive session_key = SHA3("pqtg-session-v2" || ss || transcript).
//!
//! This replaces the v0.1 "compute_shared_secret" path which did NOT actually
//! produce a shared secret (each side hashed its own pk + a probabilistic
//! Falcon signature, so outputs diverged). See git history.

use aes_gcm::aead::{Aead, OsRng};
use aes_gcm::{Aes256Gcm, Key, KeyInit, Nonce};
use anyhow::{anyhow, Result};
use paraxiom_pqc::kem::{self, EncapsulationKey, KemAlgorithm, SharedSecret};
use paraxiom_pqc::sign::{self, SignAlgorithm, Signature, SigningKey, VerificationKey};
use rand::RngCore;
use sha3::{Digest, Sha3_256};
use std::path::Path;

const KEM_ALG: KemAlgorithm = KemAlgorithm::MlKem768;
const SIG_ALG: SignAlgorithm = SignAlgorithm::Falcon512;
const HASH_ALG: SignAlgorithm = SignAlgorithm::SlhDsaShake128f;

const SESSION_KDF_LABEL: &[u8] = b"pqtg-session-v2";
const KEY_MIXING_LABEL: &[u8] = b"pqtg-key-mixing-v2";

// ── Algorithm-specific byte lengths (FIPS 203/205, Falcon submission) ────────
//
// Single source of truth used by both runtime length checks and the Lean
// parameter-conformance lemmas in `lean/PQTGProofs/`. If these constants
// disagree between Rust and Lean, the Lean build will not catch it
// automatically — but every length-validating code path here pulls from
// these constants, so changes only need to happen in one Rust spot plus
// the corresponding `def …_size : ℕ := …` in the Lean module.

/// Falcon-512 verification key length. Matches `lean/PQTGProofs/Falcon.lean::pk_size`.
pub const FALCON_512_VK_LEN: usize = 897;

/// SLH-DSA-Shake128f verification key length. Matches `lean/PQTGProofs/Sphincs.lean::pk_size`.
pub const SLH_DSA_SHAKE128F_VK_LEN: usize = 32;

/// ML-KEM-768 encapsulation key length. Matches `lean/PQTGProofs/MLKem.lean::pk_size`.
pub const ML_KEM_768_EK_LEN: usize = 1184;

/// ML-KEM-768 ciphertext length. Matches `lean/PQTGProofs/MLKem.lean::ct_size`.
/// Used inside `EphemeralKemKey::decapsulate`, which is itself
/// `#[allow(dead_code)]` because the bin doesn't decapsulate.
#[allow(dead_code)]
pub const ML_KEM_768_CT_LEN: usize = 1088;

/// ML-KEM-768 shared secret length (also = SHA3-256 output).
pub const ML_KEM_768_SS_LEN: usize = 32;

/// Minimum size for an encrypted session frame: 12-byte AES-GCM nonce +
/// 4-byte length prefix + 16-byte GCM tag. Anything smaller cannot
/// possibly carry a valid signed-and-encrypted payload.
pub const MIN_SESSION_FRAME_BYTES: usize = 12 + 4 + 16;

/// Long-lived host identity: signing keys plus a fresh KEM keypair for this
/// instance. KEM keypairs are ephemeral per handshake in the wire protocol;
/// the one held here is used for handshakes initiated by this side.
pub struct PqKeyExchange {
    sig_sk: SigningKey,
    pub sig_vk: VerificationKey,
    hash_sk: SigningKey,
    pub hash_vk: VerificationKey,
}

// Manual Debug that intentionally omits secret-key material — only emits
// VK fingerprints (first 8 bytes hex) suitable for log lines.
impl std::fmt::Debug for PqKeyExchange {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let falcon_fp: String = self
            .sig_vk
            .bytes
            .iter()
            .take(8)
            .map(|b| format!("{b:02x}"))
            .collect();
        let slh_fp: String = self
            .hash_vk
            .bytes
            .iter()
            .take(8)
            .map(|b| format!("{b:02x}"))
            .collect();
        f.debug_struct("PqKeyExchange")
            .field("falcon_vk_fp", &falcon_fp)
            .field("slh_dsa_vk_fp", &slh_fp)
            .field("sig_sk", &"<redacted>")
            .field("hash_sk", &"<redacted>")
            .finish()
    }
}

impl PqKeyExchange {
    pub fn new() -> Result<Self> {
        let sig = sign::keypair(SIG_ALG).map_err(|e| anyhow!("Falcon keygen: {e:?}"))?;
        let hash = sign::keypair(HASH_ALG).map_err(|e| anyhow!("SLH-DSA keygen: {e:?}"))?;
        Ok(Self {
            sig_sk: sig.sk,
            sig_vk: sig.vk,
            hash_sk: hash.sk,
            hash_vk: hash.vk,
        })
    }

    pub fn falcon_pk_bytes(&self) -> &[u8] {
        &self.sig_vk.bytes
    }

    pub fn slh_dsa_pk_bytes(&self) -> &[u8] {
        &self.hash_vk.bytes
    }

    pub fn sign_transcript(&self, transcript: &[u8]) -> Result<Vec<u8>> {
        let sig =
            sign::sign(&self.sig_sk, transcript).map_err(|e| anyhow!("Falcon sign: {e:?}"))?;
        Ok(sig.bytes)
    }

    /// Sign with the long-lived SLH-DSA key. Used for audit-log integrity
    /// (issue #9 / threat-model T9). Currently called only by tests + the
    /// audit subsystem; `#[allow(dead_code)]` because the bin's audit log
    /// hasn't been wired through this path yet.
    #[allow(dead_code)]
    pub fn sign_hash_based(&self, msg: &[u8]) -> Result<Vec<u8>> {
        let sig = sign::sign(&self.hash_sk, msg).map_err(|e| anyhow!("SLH-DSA sign: {e:?}"))?;
        Ok(sig.bytes)
    }

    pub fn verify_falcon(msg: &[u8], sig_bytes: &[u8], vk_bytes: &[u8]) -> Result<bool> {
        let vk = VerificationKey {
            algorithm: SIG_ALG,
            bytes: vk_bytes.to_vec(),
        };
        let sig = Signature {
            algorithm: SIG_ALG,
            bytes: sig_bytes.to_vec(),
        };
        sign::verify(&vk, msg, &sig).map_err(|e| anyhow!("Falcon verify: {e:?}"))
    }

    /// Verify an SLH-DSA signature. Used by audit-log readers (out-of-band
    /// from the proxy itself). `#[allow(dead_code)]` because the bin
    /// doesn't currently verify its own logs.
    #[allow(dead_code)]
    pub fn verify_slh_dsa(msg: &[u8], sig_bytes: &[u8], vk_bytes: &[u8]) -> Result<bool> {
        let vk = VerificationKey {
            algorithm: HASH_ALG,
            bytes: vk_bytes.to_vec(),
        };
        let sig = Signature {
            algorithm: HASH_ALG,
            bytes: sig_bytes.to_vec(),
        };
        sign::verify(&vk, msg, &sig).map_err(|e| anyhow!("SLH-DSA verify: {e:?}"))
    }
}

/// A fresh ML-KEM-768 ephemeral keypair, used by the client side of the
/// handshake. Drop this immediately after the session is established.
///
/// Intentionally part of the public lib API for client implementations
/// even though the bin (server-side proxy) does not construct one;
/// `#[allow(dead_code)]` suppresses the otherwise-noisy bin-side warning.
#[allow(dead_code)]
pub struct EphemeralKemKey {
    pub algorithm: KemAlgorithm,
    pub ek_bytes: Vec<u8>,
    dk: paraxiom_pqc::kem::DecapsulationKey,
}

#[allow(dead_code)]
impl EphemeralKemKey {
    pub fn new() -> Result<Self> {
        let kp = kem::keypair(KEM_ALG).map_err(|e| anyhow!("ML-KEM keygen: {e:?}"))?;
        Ok(Self {
            algorithm: KEM_ALG,
            ek_bytes: kp.ek.bytes,
            dk: kp.dk,
        })
    }

    pub fn decapsulate(&self, ciphertext: &[u8]) -> Result<[u8; 32]> {
        if ciphertext.len() != ML_KEM_768_CT_LEN {
            return Err(anyhow!(
                "ML-KEM-768 ciphertext wrong size: expected {} bytes, got {}",
                ML_KEM_768_CT_LEN,
                ciphertext.len()
            ));
        }
        let ct = paraxiom_pqc::kem::Ciphertext {
            algorithm: KEM_ALG,
            bytes: ciphertext.to_vec(),
        };
        let ss: SharedSecret =
            kem::decapsulate(&self.dk, &ct).map_err(|e| anyhow!("ML-KEM decapsulate: {e:?}"))?;
        if ss.bytes.len() != ML_KEM_768_SS_LEN {
            return Err(anyhow!(
                "ML-KEM shared secret wrong size: {}",
                ss.bytes.len()
            ));
        }
        let mut out = [0u8; 32];
        out.copy_from_slice(&ss.bytes);
        Ok(out)
    }
}

/// Server-side: encapsulate against the client's ML-KEM EK, returning the
/// ciphertext (for the wire) and the shared secret.
///
/// Rejects encapsulation keys of the wrong length (must be exactly
/// [`ML_KEM_768_EK_LEN`]). This is defense-in-depth — `paraxiom-pqc`'s
/// `ml_kem` will also reject malformed keys, but we want a clear error
/// at the protocol layer before the cost of attempted encapsulation.
pub fn encapsulate_to(client_ek_bytes: &[u8]) -> Result<(Vec<u8>, [u8; 32])> {
    if client_ek_bytes.len() != ML_KEM_768_EK_LEN {
        return Err(anyhow!(
            "ML-KEM-768 EK wrong size: expected {} bytes, got {}",
            ML_KEM_768_EK_LEN,
            client_ek_bytes.len()
        ));
    }
    let ek = EncapsulationKey {
        algorithm: KEM_ALG,
        bytes: client_ek_bytes.to_vec(),
    };
    let (ct, ss) = kem::encapsulate(&ek).map_err(|e| anyhow!("ML-KEM encapsulate: {e:?}"))?;
    if ss.bytes.len() != ML_KEM_768_SS_LEN {
        return Err(anyhow!(
            "ML-KEM shared secret wrong size: {}",
            ss.bytes.len()
        ));
    }
    let mut out = [0u8; 32];
    out.copy_from_slice(&ss.bytes);
    Ok((ct.bytes, out))
}

/// Hash the handshake transcript. Both sides compute this over the same bytes
/// in the same order; binds the session to identities and randoms.
pub fn transcript_hash(
    client_random: &[u8; 32],
    server_random: &[u8; 32],
    client_kem_ek: &[u8],
    server_falcon_pk: &[u8],
    kem_ciphertext: &[u8],
) -> [u8; 32] {
    let mut h = Sha3_256::new();
    h.update(b"pqtg-transcript-v2");
    h.update(client_random);
    h.update(server_random);
    h.update((client_kem_ek.len() as u32).to_be_bytes());
    h.update(client_kem_ek);
    h.update((server_falcon_pk.len() as u32).to_be_bytes());
    h.update(server_falcon_pk);
    h.update((kem_ciphertext.len() as u32).to_be_bytes());
    h.update(kem_ciphertext);
    let digest = h.finalize();
    let mut out = [0u8; 32];
    out.copy_from_slice(&digest);
    out
}

/// Derive the AES-256-GCM session key from the ML-KEM shared secret and the
/// transcript hash. Both sides arrive at the same key iff KEM agreement and
/// transcript agreement both hold.
pub fn derive_session_key(kem_secret: &[u8; 32], transcript: &[u8; 32]) -> [u8; 32] {
    let mut h = Sha3_256::new();
    h.update(SESSION_KDF_LABEL);
    h.update(kem_secret);
    h.update(transcript);
    let digest = h.finalize();
    let mut out = [0u8; 32];
    out.copy_from_slice(&digest);
    out
}

/// Mix a QKD key with the PQC shared secret. Output is unconditionally 32
/// bytes regardless of QKD key size. If either input is compromised, the
/// other still provides security (hybrid).
pub fn mix_keys(qkd_key: &[u8], pqc_key: &[u8; 32]) -> [u8; 32] {
    let mut h = Sha3_256::new();
    h.update(KEY_MIXING_LABEL);
    h.update((qkd_key.len() as u32).to_be_bytes());
    h.update(qkd_key);
    h.update(pqc_key);
    let digest = h.finalize();
    let mut out = [0u8; 32];
    out.copy_from_slice(&digest);
    out
}

pub fn random_bytes<const N: usize>() -> [u8; N] {
    let mut bytes = [0u8; N];
    OsRng.fill_bytes(&mut bytes);
    bytes
}

/// Authenticated session: AES-256-GCM with a counter-based nonce.
pub struct PqSession {
    cipher: Aes256Gcm,
    pub session_id: [u8; 32],
    nonce_counter: u64,
    /// Falcon verification key of the remote party, for verifying signed
    /// payloads inside the encrypted channel.
    pub remote_falcon_pk: Vec<u8>,
}

impl std::fmt::Debug for PqSession {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("PqSession")
            .field(
                "session_id_fp",
                &format!(
                    "{:02x}{:02x}{:02x}{:02x}",
                    self.session_id[0], self.session_id[1], self.session_id[2], self.session_id[3]
                ),
            )
            .field("nonce_counter", &self.nonce_counter)
            .field("remote_falcon_pk_len", &self.remote_falcon_pk.len())
            .finish()
    }
}

impl PqSession {
    /// Construct a session. Validates `remote_falcon_pk` length up-front
    /// so a malformed vk fails here rather than at first verify call.
    pub fn new(
        session_key: &[u8; 32],
        session_id: [u8; 32],
        remote_falcon_pk: Vec<u8>,
    ) -> Result<Self> {
        if remote_falcon_pk.len() != FALCON_512_VK_LEN {
            return Err(anyhow!(
                "Falcon-512 vk wrong size: expected {} bytes, got {}",
                FALCON_512_VK_LEN,
                remote_falcon_pk.len()
            ));
        }
        let key = Key::<Aes256Gcm>::from_slice(session_key);
        let cipher = Aes256Gcm::new(key);
        Ok(Self {
            cipher,
            session_id,
            nonce_counter: 0,
            remote_falcon_pk,
        })
    }

    pub fn encrypt(&mut self, plaintext: &[u8]) -> Result<(Vec<u8>, [u8; 12])> {
        let mut nonce_bytes = [0u8; 12];
        nonce_bytes[4..].copy_from_slice(&self.nonce_counter.to_be_bytes());
        self.nonce_counter = self
            .nonce_counter
            .checked_add(1)
            .ok_or_else(|| anyhow!("Nonce counter exhausted; rotate session"))?;
        let nonce = Nonce::from_slice(&nonce_bytes);
        let ciphertext = self
            .cipher
            .encrypt(nonce, plaintext)
            .map_err(|_| anyhow!("Encryption failed"))?;
        Ok((ciphertext, nonce_bytes))
    }

    pub fn decrypt(&self, ciphertext: &[u8], nonce: &[u8; 12]) -> Result<Vec<u8>> {
        let nonce = Nonce::from_slice(nonce);
        self.cipher
            .decrypt(nonce, ciphertext)
            .map_err(|_| anyhow!("Decryption failed"))
    }

    /// Sign with Falcon, then encrypt. Wire format: nonce(12) || E(len(4) || data || sig)
    pub fn sign_and_encrypt(&mut self, data: &[u8], signing_key: &SigningKey) -> Result<Vec<u8>> {
        let sig = sign::sign(signing_key, data).map_err(|e| anyhow!("Sign: {e:?}"))?;
        let mut payload = Vec::with_capacity(4 + data.len() + sig.bytes.len());
        payload.extend_from_slice(&(data.len() as u32).to_be_bytes());
        payload.extend_from_slice(data);
        payload.extend_from_slice(&sig.bytes);
        let (ciphertext, nonce) = self.encrypt(&payload)?;
        let mut out = Vec::with_capacity(12 + ciphertext.len());
        out.extend_from_slice(&nonce);
        out.extend_from_slice(&ciphertext);
        Ok(out)
    }

    pub fn decrypt_and_verify(&self, encrypted: &[u8]) -> Result<Vec<u8>> {
        if encrypted.len() < 12 {
            return Err(anyhow!("Invalid encrypted data: too short"));
        }
        let (nonce, ciphertext) = encrypted.split_at(12);
        let mut nonce_arr = [0u8; 12];
        nonce_arr.copy_from_slice(nonce);
        let payload = self.decrypt(ciphertext, &nonce_arr)?;
        if payload.len() < 4 {
            return Err(anyhow!("Invalid payload: missing length prefix"));
        }
        let data_len =
            u32::from_be_bytes([payload[0], payload[1], payload[2], payload[3]]) as usize;
        if payload.len() < 4 + data_len {
            return Err(anyhow!("Invalid payload length"));
        }
        let data = &payload[4..4 + data_len];
        let sig_bytes = &payload[4 + data_len..];
        let ok = PqKeyExchange::verify_falcon(data, sig_bytes, &self.remote_falcon_pk)?;
        if !ok {
            return Err(anyhow!("Signature verification failed"));
        }
        Ok(data.to_vec())
    }
}

/// Borrow the long-lived Falcon signing key. Used by the proxy server to
/// sign the handshake transcript and per-message session payloads.
impl PqKeyExchange {
    pub fn falcon_signing_key(&self) -> &SigningKey {
        &self.sig_sk
    }
}

// ── Persistence (issue #3) ───────────────────────────────────────────────────
//
// Identity file format (v1):
//
//   [MAGIC: 4 bytes "PQTG"]
//   [FORMAT_VERSION: u8 = 1]
//   For each of (Falcon-512, SLH-DSA-Shake128f):
//     [ALGO_TAG: u8]
//     [SK_LEN: u32 big-endian]
//     [SK_BYTES]
//     [VK_LEN: u32 big-endian]
//     [VK_BYTES]
//
// Algo tags are stable identifiers; do NOT renumber. New algorithms append.

const IDENTITY_MAGIC: &[u8; 4] = b"PQTG";
const IDENTITY_FORMAT_VERSION: u8 = 1;
const ALGO_TAG_FALCON_512: u8 = 0x05;
const ALGO_TAG_SLH_DSA_SHAKE128F: u8 = 0x03;

fn algo_tag(alg: SignAlgorithm) -> Result<u8> {
    match alg {
        SignAlgorithm::Falcon512 => Ok(ALGO_TAG_FALCON_512),
        SignAlgorithm::SlhDsaShake128f => Ok(ALGO_TAG_SLH_DSA_SHAKE128F),
        other => Err(anyhow!("Unsupported algorithm in identity file: {other:?}")),
    }
}

fn algo_from_tag(tag: u8) -> Result<SignAlgorithm> {
    match tag {
        ALGO_TAG_FALCON_512 => Ok(SignAlgorithm::Falcon512),
        ALGO_TAG_SLH_DSA_SHAKE128F => Ok(SignAlgorithm::SlhDsaShake128f),
        other => Err(anyhow!(
            "Unknown algorithm tag in identity file: 0x{other:02X}"
        )),
    }
}

fn write_keypair(buf: &mut Vec<u8>, sk: &SigningKey, vk: &VerificationKey) -> Result<()> {
    if sk.algorithm != vk.algorithm {
        return Err(anyhow!(
            "Identity persistence: SK and VK algorithms disagree ({:?} vs {:?})",
            sk.algorithm,
            vk.algorithm
        ));
    }
    buf.push(algo_tag(sk.algorithm)?);
    let sk_len =
        u32::try_from(sk.bytes.len()).map_err(|_| anyhow!("SK too large for u32 length prefix"))?;
    buf.extend_from_slice(&sk_len.to_be_bytes());
    buf.extend_from_slice(&sk.bytes);
    let vk_len =
        u32::try_from(vk.bytes.len()).map_err(|_| anyhow!("VK too large for u32 length prefix"))?;
    buf.extend_from_slice(&vk_len.to_be_bytes());
    buf.extend_from_slice(&vk.bytes);
    Ok(())
}

fn read_keypair(
    buf: &[u8],
    cursor: &mut usize,
    expected_alg: SignAlgorithm,
) -> Result<(SigningKey, VerificationKey)> {
    if *cursor >= buf.len() {
        return Err(anyhow!("Identity truncated reading algo tag"));
    }
    let tag = buf[*cursor];
    *cursor += 1;
    let alg = algo_from_tag(tag)?;
    if alg != expected_alg {
        return Err(anyhow!(
            "Identity algorithm mismatch: expected {:?}, got {:?}",
            expected_alg,
            alg
        ));
    }
    let sk_bytes = read_length_prefixed(buf, cursor)?;
    let vk_bytes = read_length_prefixed(buf, cursor)?;
    Ok((
        SigningKey {
            algorithm: alg,
            bytes: sk_bytes,
        },
        VerificationKey {
            algorithm: alg,
            bytes: vk_bytes,
        },
    ))
}

fn read_length_prefixed(buf: &[u8], cursor: &mut usize) -> Result<Vec<u8>> {
    if *cursor + 4 > buf.len() {
        return Err(anyhow!("Identity truncated reading length prefix"));
    }
    let len = u32::from_be_bytes([
        buf[*cursor],
        buf[*cursor + 1],
        buf[*cursor + 2],
        buf[*cursor + 3],
    ]) as usize;
    *cursor += 4;
    if *cursor + len > buf.len() {
        return Err(anyhow!(
            "Identity truncated reading {} bytes at cursor {}",
            len,
            *cursor
        ));
    }
    let bytes = buf[*cursor..*cursor + len].to_vec();
    *cursor += len;
    Ok(bytes)
}

/// SSH-style identity fingerprint for vk pinning (issue #2).
///
/// Computed as `SHA3-256(falcon_vk ‖ slh_dsa_vk)` — 32 bytes.
/// Stable across restarts iff the persisted identity is stable (issue #3).
/// Clients pin this fingerprint out-of-band (deployment manifest,
/// HSM provisioning, signed announcement, etc.) and reject any handshake
/// where `SHA3-256(server_hello.falcon_vk ‖ server_hello.slh_dsa_vk)`
/// does not match.
pub fn compute_identity_fingerprint(falcon_vk: &[u8], slh_dsa_vk: &[u8]) -> [u8; 32] {
    let mut h = Sha3_256::new();
    h.update(b"pqtg-identity-fingerprint-v1");
    h.update((falcon_vk.len() as u32).to_be_bytes());
    h.update(falcon_vk);
    h.update((slh_dsa_vk.len() as u32).to_be_bytes());
    h.update(slh_dsa_vk);
    let digest = h.finalize();
    let mut out = [0u8; 32];
    out.copy_from_slice(&digest);
    out
}

/// Render a fingerprint as `SHA3-256:<base64-no-pad>` for human display
/// and for `authorized_keys`-style configuration files. Matches the
/// shape SSH uses (`ssh-keygen -lf`).
pub fn format_fingerprint(fp: &[u8; 32]) -> String {
    use base64::engine::general_purpose;
    use base64::Engine as _;
    format!("SHA3-256:{}", general_purpose::STANDARD_NO_PAD.encode(fp))
}

impl PqKeyExchange {
    /// Identity fingerprint for this server. Distribute the result of
    /// `format_fingerprint(&this)` to clients out-of-band; clients that
    /// pin it can detect MITM substitution of the server's vk.
    pub fn identity_fingerprint(&self) -> [u8; 32] {
        compute_identity_fingerprint(self.falcon_pk_bytes(), self.slh_dsa_pk_bytes())
    }

    /// Construct from already-loaded signing keypairs. Used by `load`.
    pub fn from_signing_keys(
        sig_sk: SigningKey,
        sig_vk: VerificationKey,
        hash_sk: SigningKey,
        hash_vk: VerificationKey,
    ) -> Result<Self> {
        if sig_sk.algorithm != SIG_ALG {
            return Err(anyhow!(
                "Falcon SK algorithm {:?} does not match expected {:?}",
                sig_sk.algorithm,
                SIG_ALG
            ));
        }
        if hash_sk.algorithm != HASH_ALG {
            return Err(anyhow!(
                "SLH-DSA SK algorithm {:?} does not match expected {:?}",
                hash_sk.algorithm,
                HASH_ALG
            ));
        }
        Ok(Self {
            sig_sk,
            sig_vk,
            hash_sk,
            hash_vk,
        })
    }

    /// Encode this identity to the v1 binary format.
    pub fn encode(&self) -> Result<Vec<u8>> {
        let mut buf = Vec::new();
        buf.extend_from_slice(IDENTITY_MAGIC);
        buf.push(IDENTITY_FORMAT_VERSION);
        write_keypair(&mut buf, &self.sig_sk, &self.sig_vk)?;
        write_keypair(&mut buf, &self.hash_sk, &self.hash_vk)?;
        Ok(buf)
    }

    /// Decode an identity from the v1 binary format.
    pub fn decode(buf: &[u8]) -> Result<Self> {
        if buf.len() < 5 {
            return Err(anyhow!("Identity too short for header"));
        }
        if &buf[0..4] != IDENTITY_MAGIC {
            return Err(anyhow!(
                "Identity magic mismatch (not a PQTG identity file)"
            ));
        }
        let version = buf[4];
        if version != IDENTITY_FORMAT_VERSION {
            return Err(anyhow!(
                "Unsupported identity format version: {} (expected {})",
                version,
                IDENTITY_FORMAT_VERSION
            ));
        }
        let mut cursor = 5;
        let (sig_sk, sig_vk) = read_keypair(buf, &mut cursor, SIG_ALG)?;
        let (hash_sk, hash_vk) = read_keypair(buf, &mut cursor, HASH_ALG)?;
        if cursor != buf.len() {
            return Err(anyhow!(
                "Identity has {} trailing bytes",
                buf.len() - cursor
            ));
        }
        Self::from_signing_keys(sig_sk, sig_vk, hash_sk, hash_vk)
    }

    /// Save to disk with 0o600 permissions (POSIX). The whole file is
    /// rewritten atomically (`tmp + rename`) so a crash mid-write cannot
    /// leave a torn identity.
    pub fn save<P: AsRef<Path>>(&self, path: P) -> Result<()> {
        let path = path.as_ref();
        let bytes = self.encode()?;
        let tmp_path = match path.file_name() {
            Some(name) => {
                let mut tmp = name.to_os_string();
                tmp.push(".tmp");
                path.with_file_name(tmp)
            }
            None => return Err(anyhow!("Identity path has no file name: {path:?}")),
        };
        if let Some(parent) = path.parent() {
            std::fs::create_dir_all(parent)?;
        }
        std::fs::write(&tmp_path, &bytes)?;
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            let mut perms = std::fs::metadata(&tmp_path)?.permissions();
            perms.set_mode(0o600);
            std::fs::set_permissions(&tmp_path, perms)?;
        }
        std::fs::rename(&tmp_path, path)?;
        Ok(())
    }

    /// Load from disk if the file exists; otherwise return None so the
    /// caller can decide whether to generate a new identity (first-run
    /// behaviour) or refuse to start (production behaviour).
    pub fn load_if_present<P: AsRef<Path>>(path: P) -> Result<Option<Self>> {
        let path = path.as_ref();
        if !path.exists() {
            return Ok(None);
        }
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            let mode = std::fs::metadata(path)?.permissions().mode() & 0o777;
            if mode & 0o077 != 0 {
                return Err(anyhow!(
                    "Identity file {} has insecure permissions {:#o}; expected 0o600",
                    path.display(),
                    mode
                ));
            }
        }
        let bytes = std::fs::read(path)?;
        Ok(Some(Self::decode(&bytes)?))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The whole point: client and server arrive at the same shared secret.
    #[test]
    fn ml_kem_handshake_produces_matching_shared_secret() {
        let client_kem = EphemeralKemKey::new().unwrap();
        let (ct, server_ss) = encapsulate_to(&client_kem.ek_bytes).unwrap();
        let client_ss = client_kem.decapsulate(&ct).unwrap();
        assert_eq!(client_ss, server_ss, "ML-KEM key agreement must converge");
    }

    /// Different ephemeral keys → different shared secrets, even with same EK on the wire.
    #[test]
    fn distinct_handshakes_yield_distinct_secrets() {
        let client_kem = EphemeralKemKey::new().unwrap();
        let (_ct1, ss1) = encapsulate_to(&client_kem.ek_bytes).unwrap();
        let (_ct2, ss2) = encapsulate_to(&client_kem.ek_bytes).unwrap();
        // Server's randomness in encapsulation differs each call.
        assert_ne!(ss1, ss2);
    }

    /// Full handshake including transcript binding and session key derivation.
    #[test]
    fn full_handshake_session_keys_match() {
        let server = PqKeyExchange::new().unwrap();
        let client_kem = EphemeralKemKey::new().unwrap();

        let client_random = random_bytes::<32>();
        let server_random = random_bytes::<32>();

        // Server side: encapsulate, build transcript, sign it.
        let (ct, server_ss) = encapsulate_to(&client_kem.ek_bytes).unwrap();
        let server_transcript = transcript_hash(
            &client_random,
            &server_random,
            &client_kem.ek_bytes,
            server.falcon_pk_bytes(),
            &ct,
        );
        let server_sig = server.sign_transcript(&server_transcript).unwrap();
        let server_session_key = derive_session_key(&server_ss, &server_transcript);

        // Client side: decapsulate, rebuild transcript, verify signature.
        let client_ss = client_kem.decapsulate(&ct).unwrap();
        let client_transcript = transcript_hash(
            &client_random,
            &server_random,
            &client_kem.ek_bytes,
            server.falcon_pk_bytes(),
            &ct,
        );
        let sig_ok =
            PqKeyExchange::verify_falcon(&client_transcript, &server_sig, server.falcon_pk_bytes())
                .unwrap();
        let client_session_key = derive_session_key(&client_ss, &client_transcript);

        assert!(sig_ok, "server's transcript signature must verify");
        assert_eq!(
            client_transcript, server_transcript,
            "transcripts must agree"
        );
        assert_eq!(
            client_session_key, server_session_key,
            "session keys must agree"
        );
    }

    /// A tampered transcript breaks the signature check (handshake integrity).
    #[test]
    fn tampered_transcript_fails_verification() {
        let server = PqKeyExchange::new().unwrap();
        let transcript = [0xAAu8; 32];
        let sig = server.sign_transcript(&transcript).unwrap();
        let tampered = [0xBBu8; 32];
        let ok = PqKeyExchange::verify_falcon(&tampered, &sig, server.falcon_pk_bytes()).unwrap();
        assert!(!ok, "Falcon verify must reject mismatched message");
    }

    #[test]
    fn slh_dsa_audit_signature_roundtrip() {
        let server = PqKeyExchange::new().unwrap();
        let log_line = b"2026-05-05T18:00:00Z key_request peer=1.2.3.4 size=32";
        let sig = server.sign_hash_based(log_line).unwrap();
        let ok = PqKeyExchange::verify_slh_dsa(log_line, &sig, server.slh_dsa_pk_bytes()).unwrap();
        assert!(ok);
        let bad = PqKeyExchange::verify_slh_dsa(b"different line", &sig, server.slh_dsa_pk_bytes())
            .unwrap();
        assert!(!bad);
    }

    #[test]
    fn pq_session_encryption_roundtrip() {
        let key = random_bytes::<32>();
        let id = random_bytes::<32>();
        let server = PqKeyExchange::new().unwrap();
        let mut session = PqSession::new(&key, id, server.falcon_pk_bytes().to_vec()).unwrap();
        let plaintext = b"Quantum-safe message";
        let (ciphertext, nonce) = session.encrypt(plaintext).unwrap();
        let decrypted = session.decrypt(&ciphertext, &nonce).unwrap();
        assert_eq!(decrypted, plaintext);
    }

    /// Counter-based nonce: encrypting the same plaintext twice must produce
    /// distinct ciphertexts (i.e., distinct nonces under the hood).
    #[test]
    fn nonce_counter_advances_per_message() {
        let key = random_bytes::<32>();
        let id = random_bytes::<32>();
        let server = PqKeyExchange::new().unwrap();
        let mut session = PqSession::new(&key, id, server.falcon_pk_bytes().to_vec()).unwrap();
        let plaintext = b"same message";
        let (_, nonce_a) = session.encrypt(plaintext).unwrap();
        let (_, nonce_b) = session.encrypt(plaintext).unwrap();
        assert_ne!(nonce_a, nonce_b, "nonces must not repeat under same key");
    }

    #[test]
    fn sign_and_encrypt_roundtrip_with_real_kex() {
        // Bind two parties through a real KEM-derived session key, then send a
        // signed-encrypted payload from server to client.
        let server = PqKeyExchange::new().unwrap();
        let client_kem = EphemeralKemKey::new().unwrap();
        let (ct, server_ss) = encapsulate_to(&client_kem.ek_bytes).unwrap();
        let client_ss = client_kem.decapsulate(&ct).unwrap();
        let client_random = random_bytes::<32>();
        let server_random = random_bytes::<32>();
        let transcript = transcript_hash(
            &client_random,
            &server_random,
            &client_kem.ek_bytes,
            server.falcon_pk_bytes(),
            &ct,
        );
        let session_key = derive_session_key(&client_ss, &transcript);
        assert_eq!(session_key, derive_session_key(&server_ss, &transcript));

        // Server-side session encrypts + signs.
        let session_id = random_bytes::<32>();
        let mut server_session =
            PqSession::new(&session_key, session_id, server.falcon_pk_bytes().to_vec()).unwrap();
        let payload = b"key request response";
        let wire = server_session
            .sign_and_encrypt(payload, server.falcon_signing_key())
            .unwrap();

        // Client-side session has same key, holds server's Falcon vk for verify.
        let client_session =
            PqSession::new(&session_key, session_id, server.falcon_pk_bytes().to_vec()).unwrap();
        let recovered = client_session.decrypt_and_verify(&wire).unwrap();
        assert_eq!(recovered, payload);
    }

    #[test]
    fn key_mixing_is_deterministic_and_changes_inputs() {
        let qkd_key = vec![0x11u8; 32];
        let pqc_key = [0x22u8; 32];
        let mixed = mix_keys(&qkd_key, &pqc_key);
        assert_ne!(&mixed[..], &qkd_key[..]);
        assert_ne!(mixed, pqc_key);
        assert_eq!(mixed, mix_keys(&qkd_key, &pqc_key));
    }

    /// Hybrid security: changing only the QKD half changes the mixed key.
    #[test]
    fn key_mixing_is_sensitive_to_qkd_key() {
        let pqc_key = [0xAAu8; 32];
        let m1 = mix_keys(&[0x01; 32], &pqc_key);
        let m2 = mix_keys(&[0x02; 32], &pqc_key);
        assert_ne!(m1, m2);
    }

    /// And to the PQC half.
    #[test]
    fn key_mixing_is_sensitive_to_pqc_key() {
        let qkd_key = vec![0x33u8; 32];
        let m1 = mix_keys(&qkd_key, &[0xAA; 32]);
        let m2 = mix_keys(&qkd_key, &[0xBB; 32]);
        assert_ne!(m1, m2);
    }

    // ── Identity persistence (issue #3) ─────────────────────────────────────

    /// Encode → decode round-trip preserves all key material and signing/verify
    /// behavior. If signing across the boundary still works, the SK survived.
    #[test]
    fn identity_encode_decode_round_trip() {
        let original = PqKeyExchange::new().unwrap();
        let encoded = original.encode().unwrap();
        let restored = PqKeyExchange::decode(&encoded).unwrap();

        // Public keys match byte-for-byte.
        assert_eq!(original.falcon_pk_bytes(), restored.falcon_pk_bytes());
        assert_eq!(original.slh_dsa_pk_bytes(), restored.slh_dsa_pk_bytes());

        // Signing with the restored SK still verifies under the original VK.
        let msg = b"identity round-trip test";
        let sig = restored.sign_transcript(msg).unwrap();
        let ok = PqKeyExchange::verify_falcon(msg, &sig, original.falcon_pk_bytes()).unwrap();
        assert!(
            ok,
            "restored Falcon SK must still produce signatures verifying under original VK"
        );

        let audit_line = b"audit roundtrip line";
        let audit_sig = restored.sign_hash_based(audit_line).unwrap();
        let audit_ok =
            PqKeyExchange::verify_slh_dsa(audit_line, &audit_sig, original.slh_dsa_pk_bytes())
                .unwrap();
        assert!(
            audit_ok,
            "restored SLH-DSA SK must still produce signatures verifying under original VK"
        );
    }

    #[test]
    fn identity_decode_rejects_bad_magic() {
        let mut bytes = PqKeyExchange::new().unwrap().encode().unwrap();
        bytes[0] = b'X'; // corrupt magic
        let err = PqKeyExchange::decode(&bytes).unwrap_err();
        assert!(err.to_string().contains("magic"));
    }

    #[test]
    fn identity_decode_rejects_unsupported_version() {
        let mut bytes = PqKeyExchange::new().unwrap().encode().unwrap();
        bytes[4] = 99; // unsupported version
        let err = PqKeyExchange::decode(&bytes).unwrap_err();
        assert!(err.to_string().contains("version"));
    }

    #[test]
    fn identity_decode_rejects_truncation() {
        let bytes = PqKeyExchange::new().unwrap().encode().unwrap();
        let err = PqKeyExchange::decode(&bytes[..bytes.len() - 5]).unwrap_err();
        assert!(err.to_string().contains("truncated") || err.to_string().contains("trailing"));
    }

    #[test]
    fn identity_save_load_round_trip() {
        let dir = std::env::temp_dir().join(format!("pqtg-identity-test-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let path = dir.join("proxy.key");

        let original = PqKeyExchange::new().unwrap();
        original.save(&path).unwrap();

        // Permissions enforced (POSIX).
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            let mode = std::fs::metadata(&path).unwrap().permissions().mode() & 0o777;
            assert_eq!(mode, 0o600, "identity file must be 0o600, got {mode:#o}");
        }

        let restored = PqKeyExchange::load_if_present(&path).unwrap().unwrap();
        assert_eq!(original.falcon_pk_bytes(), restored.falcon_pk_bytes());
        assert_eq!(original.slh_dsa_pk_bytes(), restored.slh_dsa_pk_bytes());

        std::fs::remove_dir_all(&dir).ok();
    }

    #[test]
    fn identity_load_returns_none_for_missing_file() {
        let path = std::env::temp_dir().join("pqtg-does-not-exist-xyz.key");
        let result = PqKeyExchange::load_if_present(&path).unwrap();
        assert!(result.is_none());
    }

    // ── Identity fingerprints (issue #2) ────────────────────────────────────

    /// Same identity → same fingerprint (deterministic).
    #[test]
    fn fingerprint_is_deterministic() {
        let kex = PqKeyExchange::new().unwrap();
        let fp1 = kex.identity_fingerprint();
        let fp2 = kex.identity_fingerprint();
        assert_eq!(fp1, fp2);
    }

    /// Independent identities → different fingerprints (with overwhelming
    /// probability — 2^-256 collision rate).
    #[test]
    fn fingerprint_distinguishes_independent_identities() {
        let alice = PqKeyExchange::new().unwrap();
        let bob = PqKeyExchange::new().unwrap();
        assert_ne!(alice.identity_fingerprint(), bob.identity_fingerprint());
    }

    /// Persistence preserves the fingerprint — that's the whole point of
    /// vk pinning across restarts (issue #2 + #3).
    #[test]
    fn fingerprint_survives_save_load() {
        let dir = std::env::temp_dir().join(format!("pqtg-fp-test-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let path = dir.join("proxy.key");

        let original = PqKeyExchange::new().unwrap();
        let fp_before = original.identity_fingerprint();
        original.save(&path).unwrap();

        let restored = PqKeyExchange::load_if_present(&path).unwrap().unwrap();
        let fp_after = restored.identity_fingerprint();

        assert_eq!(
            fp_before, fp_after,
            "fingerprint MUST survive save/load — this is the pinning anchor"
        );

        std::fs::remove_dir_all(&dir).ok();
    }

    /// Format produces `SHA3-256:<base64>` shape (SSH-style, no padding).
    #[test]
    fn fingerprint_format_shape() {
        let kex = PqKeyExchange::new().unwrap();
        let s = format_fingerprint(&kex.identity_fingerprint());
        assert!(
            s.starts_with("SHA3-256:"),
            "expected SHA3-256: prefix, got {s}"
        );
        assert!(!s.contains('='), "no padding expected, got {s}");
        // 32 bytes → 43 base64 chars (no pad). Plus "SHA3-256:" = 9.
        assert_eq!(s.len(), 9 + 43);
    }

    /// Permuting the (falcon_vk, slh_dsa_vk) order changes the fingerprint
    /// — verifies domain separation between halves.
    #[test]
    fn fingerprint_is_position_sensitive() {
        let a = vec![0xAAu8; 897];
        let b = vec![0xBBu8; 32];
        let fp1 = compute_identity_fingerprint(&a, &b);
        // Same bytes in opposite-length slots should not match (lengths
        // are length-prefixed in the hash input).
        let fp2 = compute_identity_fingerprint(&b, &a);
        assert_ne!(fp1, fp2);
    }

    // ── Input validation (issue #5) ─────────────────────────────────────────

    #[test]
    fn encapsulate_to_rejects_short_ek() {
        let err = encapsulate_to(&[0u8; 100]).unwrap_err();
        assert!(err.to_string().contains("EK wrong size"));
    }

    #[test]
    fn encapsulate_to_rejects_long_ek() {
        let err = encapsulate_to(&[0u8; ML_KEM_768_EK_LEN + 1]).unwrap_err();
        assert!(err.to_string().contains("EK wrong size"));
    }

    #[test]
    fn ephemeral_decapsulate_rejects_wrong_size_ct() {
        let kem = EphemeralKemKey::new().unwrap();
        let err = kem.decapsulate(&[0u8; 100]).unwrap_err();
        assert!(err.to_string().contains("ciphertext wrong size"));
    }

    #[test]
    fn pq_session_rejects_short_falcon_vk() {
        let err = PqSession::new(&[0u8; 32], [0u8; 32], vec![0u8; 100]).unwrap_err();
        assert!(err.to_string().contains("Falcon-512 vk wrong size"));
    }

    #[test]
    fn pq_session_accepts_correct_falcon_vk() {
        let ok = PqSession::new(&[0u8; 32], [0u8; 32], vec![0u8; FALCON_512_VK_LEN]);
        assert!(ok.is_ok());
    }
}
