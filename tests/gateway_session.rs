//! End to end over TCP: a real `ProxyServer`, the session loop it runs, and a
//! client written from `docs/CLIENT-INTEGRATION.md` for wire 3.2 and 2.1 (one
//! AES-256-GCM key per direction, strict receive sequencing).
//!
//! The KME is an httpmock emulator, as in `tests/etsi014_emulator.rs`. The
//! client is allow-listed through a real `authorized_keys` file and the server
//! identity is persisted, so the client pins it exactly as an integrator
//! would. Nothing leaves the loopback interface.

use anyhow::{anyhow, ensure, Result};
use base64::engine::general_purpose::STANDARD as B64;
use base64::Engine as _;
use httpmock::prelude::*;
use pq_qkd_proxy::crypto::{
    compute_identity_fingerprint, derive_session_key, derive_v3_session_key, random_bytes,
    transcript_hash, transcript_hash_v3, EphemeralKemKey, HandshakeVersion, PqKeyExchange,
    PqSession, Role,
};
use pq_qkd_proxy::proxy::{
    ClientHello, ClientHelloV3, KeyMode, KeyRequest, KeyResponse, ProxyServer, ServerHello,
    ServerHelloV3,
};
use pq_qkd_proxy::ProxyConfig;
use serde_json::json;
use std::net::SocketAddr;
use std::path::PathBuf;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;
use std::time::{Duration, SystemTime, UNIX_EPOCH};
use tokio::io::{AsyncReadExt, AsyncWriteExt};
use tokio::net::{TcpListener, TcpStream};
use tokio::task::JoinHandle;

/// The key a session request delivers (the KME's `default-slave` SAE).
const KEY_ID: &str = "0b5e0b5e-1111-2222-3333-444455556666";
const DELIVERED: [u8; 32] = [0xD7; 32];
/// The QKD key a Hybrid v3 handshake allocates for the client's SAE; the
/// client's own KME would return the same bytes for this key_ID.
const CLIENT_SAE: &str = "sae-e2e-client";
const QKD_KEY_ID: &str = "9a9a9a9a-aaaa-bbbb-cccc-ddddeeeeffff";
const QKD_BYTES: [u8; 32] = [0x5A; 32];

const IO_TIMEOUT: Duration = Duration::from_secs(20);

struct TempDir(PathBuf);

impl Drop for TempDir {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

/// A gateway that serves exactly one connection.
struct Gateway {
    addr: SocketAddr,
    /// The server identity fingerprint, as distributed out of band.
    pin: [u8; 32],
    /// What `handle_connection` returned for that connection.
    outcome: JoinHandle<Result<()>>,
    _kme: MockServer,
    _dir: TempDir,
}

async fn start_gateway(client: &PqKeyExchange) -> Gateway {
    static NEXT: AtomicUsize = AtomicUsize::new(0);
    let dir = TempDir(std::env::temp_dir().join(format!(
        "pqtg-gateway-session-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    )));
    std::fs::create_dir_all(&dir.0).unwrap();

    let kme = MockServer::start_async().await;
    kme.mock_async(|when, then| {
        when.method(POST)
            .path("/api/v1/keys/default-slave/enc_keys");
        then.status(200).json_body(json!({
            "keys": [{ "key_ID": KEY_ID, "key": B64.encode(DELIVERED) }]
        }));
    })
    .await;
    kme.mock_async(|when, then| {
        when.method(POST)
            .path(format!("/api/v1/keys/{CLIENT_SAE}/enc_keys"));
        then.status(200).json_body(json!({
            "keys": [{ "key_ID": QKD_KEY_ID, "key": B64.encode(QKD_BYTES) }]
        }));
    })
    .await;

    let identity = PqKeyExchange::new().unwrap();
    let pin = identity.identity_fingerprint();
    let key_path = dir.0.join("proxy.key");
    identity.save(&key_path).unwrap();

    let mut vks = client.falcon_pk_bytes().to_vec();
    vks.extend_from_slice(client.slh_dsa_pk_bytes());
    let authorized = dir.0.join("authorized_keys");
    std::fs::write(
        &authorized,
        format!(
            "falcon512+slh-dsa-shake128f {} perm=read,write e2e@client\n",
            B64.encode(&vks)
        ),
    )
    .unwrap();

    let mut config = ProxyConfig::default();
    config.qkd.vendor_api = kme.url("");
    config.qkd.key_timeout = 5;
    config.security.authorized_keys = authorized.to_string_lossy().into_owned();
    config.security.proxy_private_key = key_path.to_string_lossy().into_owned();
    let proxy = ProxyServer::new(Arc::new(config)).await.unwrap();

    let listener = TcpListener::bind("127.0.0.1:0").await.unwrap();
    let addr = listener.local_addr().unwrap();
    let outcome = tokio::spawn(async move {
        let (stream, peer) = listener.accept().await?;
        proxy.handle_connection(stream, peer).await
    });
    Gateway {
        addr,
        pin,
        outcome,
        _kme: kme,
        _dir: dir,
    }
}

async fn write_frame(s: &mut TcpStream, bytes: &[u8]) -> Result<()> {
    s.write_all(&(bytes.len() as u32).to_be_bytes()).await?;
    s.write_all(bytes).await?;
    s.flush().await?;
    Ok(())
}

/// One length-prefixed frame, or `None` once the gateway has closed the
/// connection.
async fn read_frame(s: &mut TcpStream) -> Option<Vec<u8>> {
    let mut len = [0u8; 4];
    tokio::time::timeout(IO_TIMEOUT, s.read_exact(&mut len))
        .await
        .expect("the gateway neither answered nor closed")
        .ok()?;
    let mut buf = vec![0u8; u32::from_be_bytes(len) as usize];
    tokio::time::timeout(IO_TIMEOUT, s.read_exact(&mut buf))
        .await
        .expect("the gateway stalled mid-frame")
        .ok()?;
    Some(buf)
}

fn unix_now() -> u64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_secs()
}

/// Client side of the v3 handshake, CLIENT-INTEGRATION.md §2 steps 1 to 8.
/// `hybrid` asks for QKD; the bytes the client's own KME would return for the
/// signed key_ID are `QKD_BYTES`.
async fn client_v3(
    s: &mut TcpStream,
    me: &PqKeyExchange,
    pin: &[u8; 32],
    version: &str,
    hybrid: bool,
) -> Result<PqSession> {
    let kem = EphemeralKemKey::new()?;
    let mut hello = ClientHelloV3 {
        version: version.to_string(),
        client_random: random_bytes::<32>(),
        kem_ek: kem.ek_bytes.clone(),
        falcon_vk: me.falcon_pk_bytes().to_vec(),
        slh_dsa_vk: me.slh_dsa_pk_bytes().to_vec(),
        requested_key_size: 32,
        client_sae_id: if hybrid {
            CLIENT_SAE.to_string()
        } else {
            String::new()
        },
        qkd_capable: hybrid,
        timestamp: unix_now(),
        hello_sig: Vec::new(),
    };
    hello.sign(me)?;
    write_frame(s, &bincode::serialize(&hello)?).await?;

    let raw = read_frame(s)
        .await
        .ok_or_else(|| anyhow!("the gateway closed the connection after the hello"))?;
    let sh: ServerHelloV3 = bincode::deserialize(&raw)?;
    ensure!(sh.version == hello.version, "server speaks {}", sh.version);
    ensure!(
        compute_identity_fingerprint(&sh.falcon_vk, &sh.slh_dsa_vk) == *pin,
        "pin violated"
    );
    let transcript = transcript_hash_v3(
        &hello.client_random,
        &sh.server_random,
        &hello.kem_ek,
        &sh.falcon_vk,
        &sh.kem_ciphertext,
        sh.key_mode.wire_byte(),
        sh.qkd_key_id.as_deref().unwrap_or("").as_bytes(),
        sh.master_sae_id.as_bytes(),
        sh.qkd_key_len,
    );
    ensure!(
        PqKeyExchange::verify_falcon(&transcript, &sh.transcript_sig, &sh.falcon_vk)?,
        "transcript signature"
    );
    let qkd = match sh.key_mode {
        KeyMode::Hybrid => {
            ensure!(hybrid, "the server negotiated Hybrid unasked");
            ensure!(sh.qkd_key_id.as_deref() == Some(QKD_KEY_ID), "key_ID");
            Some(QKD_BYTES.to_vec())
        }
        KeyMode::PqcOnly => {
            ensure!(!hybrid, "Hybrid requested, PqcOnly negotiated");
            None
        }
    };
    let ss = kem.decapsulate(&sh.kem_ciphertext)?;
    let session_key = derive_v3_session_key(&ss, qkd.as_deref(), &transcript);
    PqSession::new(
        &session_key,
        HandshakeVersion::V3,
        Role::Client,
        random_bytes::<32>(),
        sh.falcon_vk,
    )
}

/// Client side of the v2 handshake, CLIENT-INTEGRATION.md §2 steps 1 to 8.
async fn client_v2(
    s: &mut TcpStream,
    me: &PqKeyExchange,
    pin: &[u8; 32],
    version: &str,
) -> Result<PqSession> {
    let kem = EphemeralKemKey::new()?;
    let hello = ClientHello {
        version: version.to_string(),
        client_random: random_bytes::<32>(),
        kem_ek: kem.ek_bytes.clone(),
        falcon_vk: me.falcon_pk_bytes().to_vec(),
        slh_dsa_vk: me.slh_dsa_pk_bytes().to_vec(),
        requested_key_size: 32,
    };
    write_frame(s, &bincode::serialize(&hello)?).await?;

    let raw = read_frame(s)
        .await
        .ok_or_else(|| anyhow!("the gateway closed the connection after the hello"))?;
    let sh: ServerHello = bincode::deserialize(&raw)?;
    ensure!(sh.version == hello.version, "server speaks {}", sh.version);
    ensure!(
        compute_identity_fingerprint(&sh.falcon_vk, &sh.slh_dsa_vk) == *pin,
        "pin violated"
    );
    let transcript = transcript_hash(
        &hello.client_random,
        &sh.server_random,
        &hello.kem_ek,
        &sh.falcon_vk,
        &sh.kem_ciphertext,
    );
    ensure!(
        PqKeyExchange::verify_falcon(&transcript, &sh.transcript_sig, &sh.falcon_vk)?,
        "transcript signature"
    );
    let ss = kem.decapsulate(&sh.kem_ciphertext)?;
    let session_key = derive_session_key(&ss, &transcript);
    PqSession::new(
        &session_key,
        HandshakeVersion::V2,
        Role::Client,
        random_bytes::<32>(),
        sh.falcon_vk,
    )
}

/// A key request, signed by the client and sealed in the client-to-server
/// direction at the next counter.
fn seal_request(session: &mut PqSession, me: &PqKeyExchange) -> Vec<u8> {
    let request = KeyRequest {
        key_id: String::new(),
        size: 32,
        purpose: "gateway-session e2e".to_string(),
    };
    session
        .sign_and_encrypt(
            &bincode::serialize(&request).unwrap(),
            me.falcon_signing_key(),
        )
        .unwrap()
}

/// Open a response and check it carries the key the KME handed the gateway.
fn open_response(session: &mut PqSession, frame: &[u8]) {
    let data = session.decrypt_and_verify(frame).expect("response opens");
    let response: KeyResponse = bincode::deserialize(&data).unwrap();
    assert_eq!(response.key_id, KEY_ID);
    assert_eq!(response.key_data, DELIVERED);
}

/// Send one request, read and open its response; returns the raw response.
async fn round_trip(s: &mut TcpStream, session: &mut PqSession, me: &PqKeyExchange) -> Vec<u8> {
    let request = seal_request(session, me);
    write_frame(s, &request).await.unwrap();
    let response = read_frame(s).await.expect("a response");
    open_response(session, &response);
    response
}

/// The server's error for the connection, rendered with its causes.
async fn server_error(outcome: JoinHandle<Result<()>>) -> String {
    let err = outcome
        .await
        .unwrap()
        .expect_err("the gateway must end this connection with an error");
    format!("{err:#}")
}

#[tokio::test]
async fn v3_pqc_only_handshake_then_requests_and_responses() {
    let me = PqKeyExchange::new().unwrap();
    let gw = start_gateway(&me).await;
    let mut s = TcpStream::connect(gw.addr).await.unwrap();
    let mut session = client_v3(&mut s, &me, &gw.pin, "3.2", false).await.unwrap();
    // Several exchanges: both counters advance in step on both ends.
    for _ in 0..3 {
        round_trip(&mut s, &mut session, &me).await;
    }
    drop(s);
    gw.outcome
        .await
        .unwrap()
        .expect("a clean session ends cleanly");
}

#[tokio::test]
async fn v3_hybrid_handshake_then_request_and_response() {
    let me = PqKeyExchange::new().unwrap();
    let gw = start_gateway(&me).await;
    let mut s = TcpStream::connect(gw.addr).await.unwrap();
    let mut session = client_v3(&mut s, &me, &gw.pin, "3.2", true).await.unwrap();
    round_trip(&mut s, &mut session, &me).await;
    round_trip(&mut s, &mut session, &me).await;
    drop(s);
    gw.outcome
        .await
        .unwrap()
        .expect("a clean session ends cleanly");
}

#[tokio::test]
async fn v2_handshake_then_requests_and_responses() {
    let me = PqKeyExchange::new().unwrap();
    let gw = start_gateway(&me).await;
    let mut s = TcpStream::connect(gw.addr).await.unwrap();
    let mut session = client_v2(&mut s, &me, &gw.pin, "2.1").await.unwrap();
    round_trip(&mut s, &mut session, &me).await;
    round_trip(&mut s, &mut session, &me).await;
    drop(s);
    gw.outcome
        .await
        .unwrap()
        .expect("a clean session ends cleanly");
}

/// After a full exchange the first request is sent again, byte for byte. The
/// gateway must end the connection without answering it.
#[tokio::test]
async fn the_gateway_refuses_a_replayed_request() {
    let me = PqKeyExchange::new().unwrap();
    let gw = start_gateway(&me).await;
    let mut s = TcpStream::connect(gw.addr).await.unwrap();
    let mut session = client_v3(&mut s, &me, &gw.pin, "3.2", false).await.unwrap();

    let first = seal_request(&mut session, &me);
    write_frame(&mut s, &first).await.unwrap();
    open_response(&mut session, &read_frame(&mut s).await.unwrap());

    write_frame(&mut s, &first).await.unwrap();
    assert!(
        read_frame(&mut s).await.is_none(),
        "a replayed request must get no answer"
    );
    let err = server_error(gw.outcome).await;
    assert!(err.contains("out of sequence"), "got: {err}");
}

/// Two requests sealed in order, delivered second first.
#[tokio::test]
async fn the_gateway_refuses_requests_out_of_order() {
    let me = PqKeyExchange::new().unwrap();
    let gw = start_gateway(&me).await;
    let mut s = TcpStream::connect(gw.addr).await.unwrap();
    let mut session = client_v2(&mut s, &me, &gw.pin, "2.1").await.unwrap();

    let _first = seal_request(&mut session, &me);
    let second = seal_request(&mut session, &me);
    write_frame(&mut s, &second).await.unwrap();
    assert!(
        read_frame(&mut s).await.is_none(),
        "a request ahead of its predecessor must get no answer"
    );
    let err = server_error(gw.outcome).await;
    assert!(err.contains("out of sequence"), "got: {err}");
}

/// An on-path attacker bounces frames back to the end that sealed them.
#[tokio::test]
async fn reflected_frames_are_refused_at_both_ends() {
    let me = PqKeyExchange::new().unwrap();
    let gw = start_gateway(&me).await;
    let mut s = TcpStream::connect(gw.addr).await.unwrap();
    let mut session = client_v3(&mut s, &me, &gw.pin, "3.2", false).await.unwrap();

    // The client's first request, handed back to the client as if it were the
    // server's first response: the counter is the one the client expects (0),
    // so only the direction key can refuse it. Under the old single key it
    // passed the AEAD check and only the inner Falcon signature refused it.
    let request = seal_request(&mut session, &me);
    let err = session.decrypt_and_verify(&request).unwrap_err();
    assert!(err.to_string().contains("Decryption failed"), "got: {err}");

    // The refusal moved nothing: the genuine exchange still works.
    write_frame(&mut s, &request).await.unwrap();
    let response = read_frame(&mut s).await.expect("a response");
    open_response(&mut session, &response);

    // The server's response handed back to the server. It is refused (here
    // already by sequencing, as the server has moved past counter 0; the unit
    // test `a_frame_reflected_to_its_sender_is_rejected` isolates the key).
    write_frame(&mut s, &response).await.unwrap();
    assert!(read_frame(&mut s).await.is_none());
    let err = server_error(gw.outcome).await;
    assert!(
        err.contains("out of sequence") || err.contains("Decryption failed"),
        "got: {err}"
    );
}

/// Peers on 3.1, 3.0 or 2.0 seal with one key in both directions. The gateway
/// refuses them at the hello: no ServerHello, nothing encapsulated.
#[tokio::test]
async fn older_wire_versions_are_refused_at_the_hello() {
    for (version, v3) in [("3.1", true), ("3.0", true), ("2.0", false)] {
        let me = PqKeyExchange::new().unwrap();
        let gw = start_gateway(&me).await;
        let mut s = TcpStream::connect(gw.addr).await.unwrap();
        let result = if v3 {
            client_v3(&mut s, &me, &gw.pin, version, false).await
        } else {
            client_v2(&mut s, &me, &gw.pin, version).await
        };
        let err = result.expect_err("an older client must not get a session");
        assert!(err.to_string().contains("closed"), "{version}: {err}");
        let err = server_error(gw.outcome).await;
        assert!(
            err.contains("Unsupported protocol version"),
            "{version}: {err}"
        );
    }
}
