//! `PqSession::decrypt_and_verify` on payloads that pass the record layer
//! (sealed by the real peer end under the real direction key, at the
//! expected position) but are malformed inside: the length prefix, the data
//! and signature split, and large data. Only an authenticated peer can make
//! the gateway parse such a payload, so the requirement is narrow: refuse it
//! without panicking, and accept every well-formed signed payload whatever
//! its size.
//!
//! These tests were added after cargo-mutants (2026-10-15) showed that
//! mutating the bounds checks in `decrypt_and_verify` survived the rest of
//! the suite: `payload.len() < 4` to `==`, `payload.len() < 4 + data_len` to
//! `==`, and `4 + data_len` to `4 * data_len`. Each of those panics on, or
//! wrongly refuses, a payload below. See
//! formal/GATEWAY-SESSION-RESULTS-2026-10-15.md.

use pq_qkd_proxy::crypto::{HandshakeVersion, PqKeyExchange, PqSession, Role};
use std::sync::OnceLock;

fn client_identity() -> &'static PqKeyExchange {
    static ID: OnceLock<PqKeyExchange> = OnceLock::new();
    ID.get_or_init(|| PqKeyExchange::new().unwrap())
}

fn ends(version: HandshakeVersion) -> (PqSession, PqSession) {
    let vk = client_identity().falcon_pk_bytes().to_vec();
    let client = PqSession::new(&[0x33; 32], version, Role::Client, [0; 32], vk.clone()).unwrap();
    let server = PqSession::new(&[0x33; 32], version, Role::Server, [0; 32], vk).unwrap();
    (client, server)
}

/// The server's verdict on `payload`, sealed by the genuine client end.
fn server_opens(version: HandshakeVersion, payload: &[u8]) -> Option<Vec<u8>> {
    let (mut client, mut server) = ends(version);
    let (ct, nonce) = client.encrypt(payload).unwrap();
    let mut wire = nonce.to_vec();
    wire.extend_from_slice(&ct);
    server.decrypt_and_verify(&wire).ok()
}

const VERSIONS: [HandshakeVersion; 2] = [HandshakeVersion::V2, HandshakeVersion::V3];

#[test]
fn a_payload_shorter_than_its_length_prefix_is_refused() {
    for version in VERSIONS {
        for len in 0..4 {
            assert_eq!(server_opens(version, &vec![0u8; len]), None, "len {len}");
        }
    }
}

#[test]
fn a_prefix_announcing_more_data_than_present_is_refused() {
    for version in VERSIONS {
        for (announced, present) in [(1u32, 0usize), (2, 1), (10, 5), (u32::MAX, 3)] {
            let mut p = announced.to_be_bytes().to_vec();
            p.extend(vec![0xABu8; present]);
            assert_eq!(
                server_opens(version, &p),
                None,
                "announced {announced}, present {present}"
            );
        }
    }
}

#[test]
fn a_payload_with_no_signature_bytes_is_refused() {
    for version in VERSIONS {
        for n in [0usize, 1, 7] {
            let mut p = (n as u32).to_be_bytes().to_vec();
            p.extend(vec![0x11u8; n]);
            assert_eq!(server_opens(version, &p), None, "data {n}");
        }
    }
}

/// Signed data of every size from empty to well past the signature length
/// opens and yields exactly the data.
#[test]
fn signed_payloads_of_any_size_are_accepted() {
    let id = client_identity();
    for version in VERSIONS {
        for n in [0usize, 1, 200, 300, 1000, 4096] {
            let data: Vec<u8> = (0..n).map(|i| i as u8).collect();
            let (mut client, mut server) = ends(version);
            let wire = client
                .sign_and_encrypt(&data, id.falcon_signing_key())
                .unwrap();
            assert_eq!(
                server.decrypt_and_verify(&wire).unwrap(),
                data,
                "{version:?}, {n} bytes"
            );
        }
    }
}
