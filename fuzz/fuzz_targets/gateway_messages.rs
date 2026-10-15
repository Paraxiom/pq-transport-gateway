#![no_main]
//! Fuzz the decoding of every message the gateway reads from a peer, with the
//! code the server runs: bincode 1.3's `bincode::deserialize` on the public
//! wire types, in the order `ProxyServer` uses them.
//!
//! - The hello peek: `perform_handshake` first decodes a private
//!   `VersionPeek { version: String }`; `Peek` below has the same shape, so
//!   bincode runs the same steps. Then the exact version match (2.1 or 3.2).
//! - The v2 hello `ClientHello` and the v3 hello `ClientHelloV3`, decoded for
//!   every input (the server picks one by version; both decoders are fuzzed),
//!   and for a decoded v3 hello what the server computes before any key is
//!   checked: the SAE-ID length cap and `digest()`.
//! - The session request `KeyRequest`, decoded from a frame's plaintext.
//!
//! The server reads at most 16 KiB for a hello (`MAX_HELLO_BYTES`), so run
//! with `-max_len=16384`. Properties: no panic, no allocation above
//! libFuzzer's `-malloc_limit_mb`, malformed input ends in Err.
//!
//! Run with:
//!   cargo +nightly fuzz run gateway_messages -- -max_len=16384 -malloc_limit_mb=64 -max_total_time=900

use libfuzzer_sys::fuzz_target;
use pq_qkd_proxy::proxy::{ClientHello, ClientHelloV3, KeyRequest};
use serde::Deserialize;

/// Same shape as the server's private `proxy::VersionPeek`.
#[derive(Deserialize)]
struct Peek {
    version: String,
}

fuzz_target!(|data: &[u8]| {
    if let Ok(peek) = bincode::deserialize::<Peek>(data) {
        let _known = matches!(peek.version.as_str(), "2.1" | "3.2");
    }
    if let Ok(hello) = bincode::deserialize::<ClientHello>(data) {
        let _lengths = (
            hello.kem_ek.len(),
            hello.falcon_vk.len(),
            hello.slh_dsa_vk.len(),
        );
    }
    if let Ok(hello) = bincode::deserialize::<ClientHelloV3>(data) {
        if hello.client_sae_id.len() <= 256 {
            let _ = hello.digest();
        }
    }
    let _ = bincode::deserialize::<KeyRequest>(data);
});
