//! Known-answer tests for the PQTG v2 handshake key schedule (backlog item B4).
//!
//! The expected values in `tests/vectors/handshake-v2.json` were generated
//! independently (Python `hashlib` SHA3-256, see the `_about` field) from the
//! constructions documented in `src/crypto.rs`. These tests assert that the
//! Rust implementation reproduces them byte for byte, so:
//!   - a third party can cross-validate an implementation against fixed values;
//!   - the formal model (`formal/`) is bound to the code it claims to describe;
//!   - any change to a label, length prefix, or chaining order is caught here.
//!
//! The KEM / signature primitives themselves are randomized and are covered by
//! their own FIPS KATs upstream; this file pins only the deterministic KDF layer:
//! `transcript_hash`, `derive_session_key`, `mix_keys`, `compute_identity_fingerprint`.
//!
//! If the key schedule is deliberately changed (e.g. the B2 tree-of-labels
//! refactor), publish a NEW vector set (v3) and keep this one for v2 interop.

use pq_qkd_proxy::crypto::{
    compute_identity_fingerprint, derive_session_key, format_fingerprint, mix_keys, transcript_hash,
};
use serde_json::Value;

const VECTORS: &str = include_str!("vectors/handshake-v2.json");

fn hex_decode(s: &str) -> Vec<u8> {
    assert!(s.len().is_multiple_of(2), "odd-length hex");
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).expect("bad hex"))
        .collect()
}

fn hex_encode(b: &[u8]) -> String {
    b.iter().map(|x| format!("{:02x}", x)).collect()
}

fn pattern(len: usize, a: usize, b: usize) -> Vec<u8> {
    (0..len).map(|i| ((i * a + b) & 0xff) as u8).collect()
}

fn arr32(v: &[u8]) -> [u8; 32] {
    let mut out = [0u8; 32];
    out.copy_from_slice(v);
    out
}

struct Kat {
    inputs: Value,
    expected: Value,
}

fn load() -> Kat {
    let v: Value = serde_json::from_str(VECTORS).expect("vectors JSON parses");
    Kat {
        inputs: v["inputs"].clone(),
        expected: v["expected"].clone(),
    }
}

impl Kat {
    fn input_bytes(&self, key: &str) -> Vec<u8> {
        hex_decode(self.inputs[key].as_str().expect(key))
    }
    fn expected_hex(&self, key: &str) -> &str {
        self.expected[key].as_str().expect(key)
    }
    fn client_kem_ek(&self) -> Vec<u8> {
        pattern(1184, 7, 3)
    }
    fn server_falcon_pk(&self) -> Vec<u8> {
        pattern(897, 13, 5)
    }
    fn kem_ciphertext(&self) -> Vec<u8> {
        pattern(1088, 11, 9)
    }
    fn transcript(&self) -> [u8; 32] {
        transcript_hash(
            &arr32(&self.input_bytes("client_random")),
            &arr32(&self.input_bytes("server_random")),
            &self.client_kem_ek(),
            &self.server_falcon_pk(),
            &self.kem_ciphertext(),
        )
    }
}

#[test]
fn vector_file_declares_the_v2_labels() {
    let v: Value = serde_json::from_str(VECTORS).unwrap();
    assert_eq!(v["labels"]["transcript"], "pqtg-transcript-v2");
    assert_eq!(v["labels"]["session_kdf"], "pqtg-session-v2");
    assert_eq!(v["labels"]["key_mixing"], "pqtg-key-mixing-v2");
    assert_eq!(
        v["labels"]["identity_fingerprint"],
        "pqtg-identity-fingerprint-v1"
    );
    // Input lengths match the ML-KEM-768 / Falcon-512 wire sizes the proxy enforces.
    assert_eq!(
        v["inputs"]["client_kem_ek"]["len"],
        pq_qkd_proxy::crypto::ML_KEM_768_EK_LEN
    );
    assert_eq!(
        v["inputs"]["server_falcon_pk"]["len"],
        pq_qkd_proxy::crypto::FALCON_512_VK_LEN
    );
    assert_eq!(
        v["inputs"]["kem_ciphertext"]["len"],
        pq_qkd_proxy::crypto::ML_KEM_768_CT_LEN
    );
}

#[test]
fn kat_transcript_hash() {
    let k = load();
    assert_eq!(
        hex_encode(&k.transcript()),
        k.expected_hex("transcript_hash")
    );
}

#[test]
fn kat_session_key_pqc_only() {
    // The no-QKD degrade path: session_key = derive_session_key(kem_secret, transcript).
    let k = load();
    let kem_secret = arr32(&k.input_bytes("kem_secret"));
    let sk = derive_session_key(&kem_secret, &k.transcript());
    assert_eq!(hex_encode(&sk), k.expected_hex("session_key_pqc_only"));
}

#[test]
fn kat_mix_keys_and_hybrid_session_key_qkd256() {
    // ETSI-014 default key size (256-bit QKD key).
    let k = load();
    let kem_secret = arr32(&k.input_bytes("kem_secret"));
    let qkd = k.input_bytes("qkd_key_256");
    let mixed = mix_keys(&qkd, &kem_secret);
    assert_eq!(hex_encode(&mixed), k.expected_hex("mix_keys_qkd256"));
    let sk = derive_session_key(&mixed, &k.transcript());
    assert_eq!(hex_encode(&sk), k.expected_hex("session_key_hybrid_qkd256"));
}

#[test]
fn kat_mix_keys_and_hybrid_session_key_qkd512() {
    // Exercises the length prefix in mix_keys with a 512-bit QKD key.
    let k = load();
    let kem_secret = arr32(&k.input_bytes("kem_secret"));
    let qkd = k.input_bytes("qkd_key_512");
    assert_eq!(qkd.len(), 64);
    let mixed = mix_keys(&qkd, &kem_secret);
    assert_eq!(hex_encode(&mixed), k.expected_hex("mix_keys_qkd512"));
    let sk = derive_session_key(&mixed, &k.transcript());
    assert_eq!(hex_encode(&sk), k.expected_hex("session_key_hybrid_qkd512"));
}

#[test]
fn kat_hybrid_differs_from_pqc_only_and_across_qkd_sizes() {
    // Sanity on the vector set itself: the three session keys must be distinct,
    // otherwise the vectors would not be testing the mix at all.
    let k = load();
    let a = k.expected_hex("session_key_pqc_only");
    let b = k.expected_hex("session_key_hybrid_qkd256");
    let c = k.expected_hex("session_key_hybrid_qkd512");
    assert_ne!(a, b);
    assert_ne!(a, c);
    assert_ne!(b, c);
}

#[test]
fn kat_identity_fingerprint() {
    let k = load();
    let fp = compute_identity_fingerprint(&k.server_falcon_pk(), &k.input_bytes("slh_dsa_vk"));
    assert_eq!(hex_encode(&fp), k.expected_hex("identity_fingerprint"));
    assert_eq!(
        format_fingerprint(&fp),
        k.expected_hex("identity_fingerprint_formatted")
    );
}
