#![no_main]
//! Fuzz what `PqSession::decrypt_and_verify` does after the record layer has
//! accepted a frame: the 4-byte length prefix, the data / signature split and
//! Falcon-512 verification of arbitrary signature bytes under a real key.
//! The record layer is genuine here (the payload is sealed by the real client
//! end under the session key at the expected counter), so this is what an
//! authenticated peer, and only one, can make the gateway parse.
//!
//! Input: byte 0 picks the mode.
//! - even: the rest is the payload as is;
//! - odd: a valid payload (len ‖ data ‖ signature by the client's Falcon key,
//!   built once) patched by the rest of the input, read as (offset u16 BE,
//!   byte) triples; one or two trailing bytes truncate it to that fraction.
//!
//! Properties, asserted:
//! - no panic;
//! - the receive counter moved by exactly one whatever the outcome (the frame
//!   authenticated; an Err after that is fatal for the session by contract,
//!   and the gateway closes the connection on it);
//! - Ok(data) only for a payload whose prefix announces exactly `data` and
//!   whose remaining bytes are a signature over it that verifies under the
//!   client's key.
//!
//! Run with:
//!   cargo +nightly fuzz run session_payload -- -max_total_time=900

use libfuzzer_sys::fuzz_target;
use pq_qkd_proxy::crypto::{HandshakeVersion, PqKeyExchange, PqSession, Role};
use std::sync::OnceLock;

const KEY: [u8; 32] = [0x24; 32];

struct Setup {
    client_id: PqKeyExchange,
    template: Vec<u8>,
}

fn setup() -> &'static Setup {
    static SETUP: OnceLock<Setup> = OnceLock::new();
    SETUP.get_or_init(|| {
        let client_id = PqKeyExchange::new().unwrap();
        let data = b"{\"key_id\":\"\",\"size\":32}".to_vec();
        let sig = client_id.sign_transcript(&data).unwrap();
        let mut template = (data.len() as u32).to_be_bytes().to_vec();
        template.extend_from_slice(&data);
        template.extend_from_slice(&sig);
        Setup {
            client_id,
            template,
        }
    })
}

fn recv_counter(s: &PqSession) -> u64 {
    let d = format!("{s:?}");
    let start = d.find("recv_counter: ").unwrap() + "recv_counter: ".len();
    d[start..]
        .chars()
        .take_while(|c| c.is_ascii_digit())
        .collect::<String>()
        .parse()
        .unwrap()
}

fuzz_target!(|data: &[u8]| {
    let Some((&mode, rest)) = data.split_first() else {
        return;
    };
    let s = setup();
    let payload = if mode & 1 == 0 {
        rest.to_vec()
    } else {
        let mut p = s.template.clone();
        let mut chunks = rest.chunks_exact(3);
        for c in &mut chunks {
            let at = usize::from(u16::from_be_bytes([c[0], c[1]])) % p.len();
            p[at] = c[2];
        }
        if let Some(&cut) = chunks.remainder().first() {
            p.truncate(p.len() * usize::from(cut) / 256);
        }
        p
    };
    let version = if mode & 2 == 0 {
        HandshakeVersion::V2
    } else {
        HandshakeVersion::V3
    };

    let vk = s.client_id.falcon_pk_bytes().to_vec();
    let mut client = PqSession::new(&KEY, version, Role::Client, [0; 32], vk.clone()).unwrap();
    let mut server = PqSession::new(&KEY, version, Role::Server, [0; 32], vk.clone()).unwrap();
    let (ct, nonce) = client.encrypt(&payload).unwrap();
    let mut wire = nonce.to_vec();
    wire.extend_from_slice(&ct);

    let result = server.decrypt_and_verify(&wire);
    assert_eq!(
        recv_counter(&server),
        1,
        "an authenticated frame must move the counter"
    );

    if let Ok(got) = result {
        assert!(payload.len() >= 4);
        let n = u32::from_be_bytes([payload[0], payload[1], payload[2], payload[3]]) as usize;
        assert!(payload.len() >= 4 + n);
        assert_eq!(&got[..], &payload[4..4 + n]);
        assert!(
            PqKeyExchange::verify_falcon(&got, &payload[4 + n..], &vk).unwrap_or(false),
            "accepted a payload whose signature does not verify"
        );
    }
});
