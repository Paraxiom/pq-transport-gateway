//! What the gateway session (wire 2.1 / 3.2) still gives, and what it does
//! not, when ONE direction key has leaked to an attacker. The real
//! `PqSession` ends, real Falcon-512 identities; only the attacker is
//! written here.
//!
//! The inner signature of `sign_and_encrypt` covers the request data only:
//! no session id, no direction, no position. So with `k_c2s` in hand an
//! attacker can re-seal a request the client really signed, at a later
//! position of the same session or into another session that shares the
//! leak, and the server accepts it. The tests named `limit_*` pin that
//! behaviour down as it is today: they pass because the limit exists. If the
//! signature is ever bound to the session and position (a wire change),
//! they must fail and be turned around.
//!
//! The tests named `holds_*` check what the leak does not give: a request
//! the client never signed is refused, and the other direction (`k_s2c`)
//! keeps both confidentiality and authenticity. formal/
//! pqtg-gateway-session-leak-c2s.vp and -signed-leak-c2s.vp are the
//! symbolic counterparts.

use aes_gcm::aead::Aead;
use aes_gcm::{Aes256Gcm, Key, KeyInit, Nonce};
use pq_qkd_proxy::crypto::{
    derive_direction_keys, session_nonce, HandshakeVersion, PqKeyExchange, PqSession, Role,
};
use std::sync::OnceLock;

fn identities() -> &'static (PqKeyExchange, PqKeyExchange) {
    static IDS: OnceLock<(PqKeyExchange, PqKeyExchange)> = OnceLock::new();
    IDS.get_or_init(|| (PqKeyExchange::new().unwrap(), PqKeyExchange::new().unwrap()))
}

/// A client end and a server end of one session under `key`.
fn session(key: [u8; 32], version: HandshakeVersion) -> (PqSession, PqSession) {
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
    (client, server)
}

fn cipher(key: &[u8; 32]) -> Aes256Gcm {
    Aes256Gcm::new(Key::<Aes256Gcm>::from_slice(key))
}

/// The attacker opens a captured frame (nonce ‖ ciphertext) with a leaked key.
fn open(key: &[u8; 32], wire: &[u8]) -> Option<Vec<u8>> {
    cipher(key)
        .decrypt(Nonce::from_slice(&wire[..12]), &wire[12..])
        .ok()
}

/// The attacker seals `payload` at position `n` with a leaked key.
fn seal(key: &[u8; 32], n: u64, payload: &[u8]) -> Vec<u8> {
    let nonce = session_nonce(n);
    let mut wire = nonce.to_vec();
    wire.extend_from_slice(
        &cipher(key)
            .encrypt(Nonce::from_slice(&nonce), payload)
            .unwrap(),
    );
    wire
}

const VERSIONS: [HandshakeVersion; 2] = [HandshakeVersion::V2, HandshakeVersion::V3];

/// Same session: the client's signed request 0, opened with the leaked
/// `k_c2s` and re-sealed at position 1, is accepted by the server as the
/// second request. The genuine second request then no longer opens: its slot
/// is taken.
#[test]
fn limit_leaked_c2s_lets_a_signed_request_be_replayed_at_a_later_position() {
    let (client_id, _) = identities();
    for version in VERSIONS {
        let key = [0x51; 32];
        let k = derive_direction_keys(&key, version);
        let (mut client, mut server) = session(key, version);

        let q0 = client
            .sign_and_encrypt(b"GET key 1", client_id.falcon_signing_key())
            .unwrap();
        let q1 = client
            .sign_and_encrypt(b"GET key 2", client_id.falcon_signing_key())
            .unwrap();
        assert_eq!(server.decrypt_and_verify(&q0).unwrap(), b"GET key 1");

        let p0 = open(&k.c2s, &q0).expect("the leaked key opens the request");
        let replayed = seal(&k.c2s, 1, &p0);
        assert_eq!(
            server.decrypt_and_verify(&replayed).unwrap(),
            b"GET key 1",
            "{version:?}: the replayed signed request was refused (limit closed?)"
        );
        assert!(server.decrypt_and_verify(&q1).is_err());
    }
}

/// Across sessions: a request the client signed in session A, re-sealed
/// under session B's leaked `k_c2s`, is accepted by B's server.
#[test]
fn limit_leaked_c2s_lets_a_signed_request_cross_into_another_session() {
    let (client_id, _) = identities();
    for version in VERSIONS {
        let (key_a, key_b) = ([0x61; 32], [0x62; 32]);
        let ka = derive_direction_keys(&key_a, version);
        let kb = derive_direction_keys(&key_b, version);
        let (mut client_a, _server_a) = session(key_a, version);
        let (_client_b, mut server_b) = session(key_b, version);

        let qa = client_a
            .sign_and_encrypt(b"GET key from session A", client_id.falcon_signing_key())
            .unwrap();
        let pa = open(&ka.c2s, &qa).unwrap();
        let spliced = seal(&kb.c2s, 0, &pa);
        assert_eq!(
            server_b.decrypt_and_verify(&spliced).unwrap(),
            b"GET key from session A",
            "{version:?}: the spliced signed request was refused (limit closed?)"
        );
    }
}

/// What the leak does not give: data the client never signed. A payload
/// with a valid frame, a correct length prefix and a signature that is not
/// the client's over that data is refused, whether the signature is garbage,
/// the client's signature over other data, or the server's own signature.
#[test]
fn holds_leaked_c2s_does_not_let_the_attacker_make_unsigned_requests() {
    let (client_id, server_id) = identities();
    for version in VERSIONS {
        let key = [0x71; 32];
        let k = derive_direction_keys(&key, version);
        let (mut client, mut server) = session(key, version);
        let q0 = client
            .sign_and_encrypt(b"GET key 1", client_id.falcon_signing_key())
            .unwrap();
        let p0 = open(&k.c2s, &q0).unwrap();
        let real_sig = p0[4 + 9..].to_vec();

        let data = b"DELETE everything";
        let with_sig = |sig: &[u8]| {
            let mut p = (data.len() as u32).to_be_bytes().to_vec();
            p.extend_from_slice(data);
            p.extend_from_slice(sig);
            p
        };
        let server_sig = server_id.sign_transcript(data).unwrap();
        let candidates = [
            with_sig(&[0u8; 666]),
            with_sig(&real_sig),
            with_sig(&server_sig),
            with_sig(&[]),
        ];
        // Each refusal after the record layer accepted the frame is fatal for
        // the session in the gateway; here a fresh server end is used per try
        // so every candidate sits at position 0.
        for (i, payload) in candidates.iter().enumerate() {
            let (_, mut fresh_server) = session(key, version);
            let forged = seal(&k.c2s, 0, payload);
            assert!(
                fresh_server.decrypt_and_verify(&forged).is_err(),
                "{version:?}: unsigned request {i} accepted"
            );
        }
        // The honest stream is untouched by the attempts above.
        assert_eq!(server.decrypt_and_verify(&q0).unwrap(), b"GET key 1");
    }
}

/// What the leak does not give: the other direction. With `k_c2s` the
/// attacker can neither open a response nor make the client accept one:
/// a response sealed under `k_c2s`, or a request reflected back, is refused.
#[test]
fn holds_leaked_c2s_does_not_expose_or_forge_responses() {
    let (client_id, server_id) = identities();
    for version in VERSIONS {
        let key = [0x81; 32];
        let k = derive_direction_keys(&key, version);
        assert_ne!(k.c2s, k.s2c);
        let (mut client, mut server) = session(key, version);

        let q0 = client
            .sign_and_encrypt(b"GET key 1", client_id.falcon_signing_key())
            .unwrap();
        server.decrypt_and_verify(&q0).unwrap();
        let a0 = server
            .sign_and_encrypt(b"key material", server_id.falcon_signing_key())
            .unwrap();
        assert!(open(&k.c2s, &a0).is_none(), "{version:?}: response opened");

        // The attacker cannot open a0, so the best signed payload it holds is
        // the client's own request. Sealed under the key it has, or reflected
        // as captured, it is refused by the client: wrong key for the
        // server-to-client direction.
        let p0 = open(&k.c2s, &q0).unwrap();
        assert!(client.decrypt_and_verify(&seal(&k.c2s, 0, &p0)).is_err());
        assert!(client.decrypt_and_verify(&q0).is_err(), "reflection");
        assert_eq!(client.decrypt_and_verify(&a0).unwrap(), b"key material");
    }
}
