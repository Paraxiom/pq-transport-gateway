#![no_main]
//! Fuzz the gateway's handshake entry point end to end: the input reaches a
//! real `ProxyServer` over a real loopback TCP connection and goes through
//! `handle_connection` and `perform_handshake` exactly as a peer's bytes do:
//! the frame reader (16 KiB cap), the version peek, the exact version match
//! (2.1 and 3.2 only), the bincode decode of the hello, length checks, the
//! allow-list, for v3 the hello signature, freshness and replay guard, and for
//! a hello that passes all of that the encapsulation, the signed ServerHello,
//! the session set-up and the session loop, which ends when the peer closes.
//!
//! Input: byte 0 picks how the hello is built.
//! - 0: the rest is written as is, length prefix included (fuzzes the reader);
//! - 1: the rest is the hello body, behind a correct length prefix;
//! - 2: a valid v2 hello from the allow-listed client, patched by the rest as
//!   (offset u16 BE, byte) triples, one or two trailing bytes truncating it;
//! - 3: a valid v3 hello from the allow-listed client, signed for this input
//!   (fresh random and timestamp, so it is fresh and first-seen), patched
//!   likewise.
//! Modes 2 and 3 pass authorization, so unpatched or harmlessly patched
//! hellos reach encapsulation (v2, v3 PqcOnly) with whatever the patches did
//! to the fields the signature does not cover (v3) or to the KEM key (v2).
//!
//! Properties: no panic in the gateway or here; the gateway finishes every
//! connection (Ok or Err) within 60 s of the peer closing; no allocation
//! above libFuzzer's -malloc_limit_mb.
//!
//! Run with:
//!   cargo +nightly fuzz run server_hello_path -- -max_len=20000 -malloc_limit_mb=64 -max_total_time=900

use base64::engine::general_purpose::STANDARD as B64;
use base64::Engine as _;
use libfuzzer_sys::fuzz_target;
use pq_qkd_proxy::crypto::{random_bytes, EphemeralKemKey, PqKeyExchange};
use pq_qkd_proxy::proxy::{ClientHello, ClientHelloV3, ProxyServer};
use pq_qkd_proxy::ProxyConfig;
use std::net::SocketAddr;
use std::sync::{Arc, OnceLock};
use std::time::{Duration, SystemTime, UNIX_EPOCH};
use tokio::io::{AsyncReadExt, AsyncWriteExt};
use tokio::net::{TcpListener, TcpStream};
use tokio::runtime::Runtime;

struct Setup {
    rt: Runtime,
    proxy: ProxyServer,
    listener: TcpListener,
    client: PqKeyExchange,
    kem_ek: Vec<u8>,
    v2_template: Vec<u8>,
}

fn setup() -> &'static Setup {
    static SETUP: OnceLock<Setup> = OnceLock::new();
    SETUP.get_or_init(|| {
        let dir = std::env::temp_dir().join(format!("pqtg-fuzz-server-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();

        let client = PqKeyExchange::new().unwrap();
        let mut vks = client.falcon_pk_bytes().to_vec();
        vks.extend_from_slice(client.slh_dsa_pk_bytes());
        let authorized = dir.join("authorized_keys");
        std::fs::write(
            &authorized,
            format!(
                "falcon512+slh-dsa-shake128f {} perm=read fuzz@client\n",
                B64.encode(&vks)
            ),
        )
        .unwrap();

        let mut config = ProxyConfig::default();
        // Never contacted: the v3 hellos below do not ask for QKD.
        config.qkd.vendor_api = "http://127.0.0.1:9".to_string();
        config.security.authorized_keys = authorized.to_string_lossy().into_owned();
        config.security.proxy_private_key = dir.join("proxy.key").to_string_lossy().into_owned();

        let rt = tokio::runtime::Builder::new_current_thread()
            .enable_all()
            .build()
            .unwrap();
        let proxy = rt.block_on(ProxyServer::new(Arc::new(config))).unwrap();
        let listener = rt.block_on(TcpListener::bind("127.0.0.1:0")).unwrap();

        let kem_ek = EphemeralKemKey::new().unwrap().ek_bytes;
        let v2 = ClientHello {
            version: "2.1".to_string(),
            client_random: random_bytes::<32>(),
            kem_ek: kem_ek.clone(),
            falcon_vk: client.falcon_pk_bytes().to_vec(),
            slh_dsa_vk: client.slh_dsa_pk_bytes().to_vec(),
            requested_key_size: 32,
        };
        let v2_template = bincode::serialize(&v2).unwrap();
        Setup {
            rt,
            proxy,
            listener,
            client,
            kem_ek,
            v2_template,
        }
    })
}

fn signed_v3(s: &Setup) -> Vec<u8> {
    let mut hello = ClientHelloV3 {
        version: "3.2".to_string(),
        client_random: random_bytes::<32>(),
        kem_ek: s.kem_ek.clone(),
        falcon_vk: s.client.falcon_pk_bytes().to_vec(),
        slh_dsa_vk: s.client.slh_dsa_pk_bytes().to_vec(),
        requested_key_size: 32,
        client_sae_id: String::new(),
        qkd_capable: false,
        timestamp: SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs(),
        hello_sig: Vec::new(),
    };
    hello.sign(&s.client).unwrap();
    bincode::serialize(&hello).unwrap()
}

fn patched(template: &[u8], rest: &[u8]) -> Vec<u8> {
    let mut p = template.to_vec();
    let mut chunks = rest.chunks_exact(3);
    for c in &mut chunks {
        let at = usize::from(u16::from_be_bytes([c[0], c[1]])) % p.len();
        p[at] = c[2];
    }
    if let Some(&cut) = chunks.remainder().first() {
        p.truncate(p.len() * usize::from(cut) / 256);
    }
    p
}

fn framed(body: &[u8]) -> Vec<u8> {
    let mut f = (body.len() as u32).to_be_bytes().to_vec();
    f.extend_from_slice(body);
    f
}

async fn connect(addr: SocketAddr) -> TcpStream {
    // Loopback ports can run short under TIME_WAIT at high rates: wait, do not
    // report the environment as a gateway crash.
    for _ in 0..600 {
        match TcpStream::connect(addr).await {
            Ok(s) => return s,
            Err(_) => tokio::time::sleep(Duration::from_millis(50)).await,
        }
    }
    panic!("cannot connect to the gateway on loopback for 30 s");
}

async fn exchange(s: &'static Setup, frame: &[u8]) {
    let addr = s.listener.local_addr().unwrap();
    let mut client = connect(addr).await;
    let (stream, peer) = s.listener.accept().await.unwrap();
    let server = tokio::time::timeout(
        Duration::from_secs(60),
        s.proxy.handle_connection(stream, peer),
    );
    let talk = async move {
        let _ = client.write_all(frame).await;
        let _ = client.shutdown().await;
        let mut sink = Vec::new();
        let _ = client.read_to_end(&mut sink).await;
    };
    let (outcome, ()) = tokio::join!(server, talk);
    assert!(outcome.is_ok(), "the gateway did not finish the connection");
}

fuzz_target!(|data: &[u8]| {
    let Some((&mode, rest)) = data.split_first() else {
        return;
    };
    let s = setup();
    let frame = match mode % 4 {
        0 => rest.to_vec(),
        1 => framed(rest),
        2 => framed(&patched(&s.v2_template, rest)),
        _ => framed(&patched(&signed_v3(s), rest)),
    };
    s.rt.block_on(exchange(s, &frame));
});
