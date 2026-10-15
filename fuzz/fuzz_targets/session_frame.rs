#![no_main]
//! Fuzz the session-frame path of the gateway (wire 2.1 / 3.2):
//! `PqSession::decrypt_and_verify`, which `ProxyServer::handle_session` runs
//! on every request frame, on arbitrary bytes.
//!
//! Input: byte 0 picks the receiving end (bit 0: client or server), the
//! handshake version (bit 1: v2 or v3) and how many genuine frames that end
//! has already accepted (bits 2-3: 0 to 3, so the expected nonce is
//! `session_nonce(0..=3)`); the rest is the frame, nonce ‖ ciphertext.
//!
//! Properties, asserted (a violation is a crash):
//! - no panic, and never Ok: nobody without the session key can make a frame
//!   that opens (AES-256-GCM forgery, probability 2^-128 per try);
//! - a refused frame moves nothing: both counters, read from the public
//!   `Debug` output, are unchanged, and the genuine next frame still opens.
//!
//! Run with:
//!   cargo +nightly fuzz run session_frame -- -max_total_time=900

use libfuzzer_sys::fuzz_target;
use pq_qkd_proxy::crypto::{session_nonce, HandshakeVersion, PqSession, Role, FALCON_512_VK_LEN};
use std::sync::OnceLock;

const KEY: [u8; 32] = [0x42; 32];

/// Genuine frames, sealed once: `[version][direction][position]` as
/// (ciphertext, nonce). Direction 0 is client to server.
type Frames = [[Vec<(Vec<u8>, [u8; 12])>; 2]; 2];

fn version(v: usize) -> HandshakeVersion {
    if v == 0 {
        HandshakeVersion::V2
    } else {
        HandshakeVersion::V3
    }
}

fn end(v: usize, role: Role) -> PqSession {
    PqSession::new(
        &KEY,
        version(v),
        role,
        [0u8; 32],
        vec![0u8; FALCON_512_VK_LEN],
    )
    .unwrap()
}

fn frames() -> &'static Frames {
    static FRAMES: OnceLock<Frames> = OnceLock::new();
    FRAMES.get_or_init(|| {
        let mut out: Frames = Default::default();
        for v in 0..2 {
            for (d, role) in [(0, Role::Client), (1, Role::Server)] {
                let mut sender = end(v, role);
                for i in 0..5u8 {
                    let (ct, nonce) = sender.encrypt(&[i; 40]).unwrap();
                    assert_eq!(nonce, session_nonce(i as u64));
                    out[v][d].push((ct, nonce));
                }
            }
        }
        out
    })
}

fuzz_target!(|data: &[u8]| {
    let Some((&sel, frame)) = data.split_first() else {
        return;
    };
    let server = sel & 1 == 1;
    let v = usize::from((sel >> 1) & 1);
    let accepted = usize::from((sel >> 2) & 3);
    // The server receives client-to-server frames, the client the others.
    let (role, incoming) = if server {
        (Role::Server, 0)
    } else {
        (Role::Client, 1)
    };
    let genuine = &frames()[v][incoming];

    let mut receiver = end(v, role);
    for (ct, nonce) in &genuine[..accepted] {
        receiver.decrypt(ct, nonce).unwrap();
    }
    let before = format!("{receiver:?}");

    let result = receiver.decrypt_and_verify(frame);
    assert!(result.is_err(), "a frame nobody sealed opened");
    assert_eq!(
        format!("{receiver:?}"),
        before,
        "a refused frame moved the session"
    );

    let (ct, nonce) = &genuine[accepted];
    assert_eq!(
        receiver.decrypt(ct, nonce).unwrap(),
        vec![accepted as u8; 40],
        "the genuine next frame no longer opens"
    );
});
