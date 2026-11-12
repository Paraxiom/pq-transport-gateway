//! End to end over TCP: a real `ProxyServer`, the session loop it runs, and a
//! client written from `docs/CLIENT-INTEGRATION.md` for wire 3.2 and 2.1 (one
//! AES-256-GCM key per direction, strict receive sequencing).
//!
//! Wire 2.1 is off unless the gateway lists it in `proxy.versions` and the
//! client's `authorized_keys` line carries `wire=2.1`. One section plays the
//! reason: a key request a client signed once is accepted again in a 2.1
//! session opened by someone who holds none of that client's secrets.
//!
//! A client gets a QKD key only for an SAE ID its own line lists (`sae=`).
//! The last section plays that too: a client that names another client's SAE
//! is refused before the key manager is asked for anything.
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
    /// The key manager's route for `CLIENT_SAE`, to count the keys drawn for
    /// that SAE.
    client_sae_route: usize,
    kme: MockServer,
    _dir: TempDir,
}

impl Gateway {
    /// How many keys the gateway has asked the key manager for under
    /// `CLIENT_SAE`.
    async fn keys_drawn_for_client_sae(&self) -> usize {
        httpmock::Mock::new(self.client_sae_route, &self.kme)
            .hits_async()
            .await
    }
}

/// A gateway with the default setting (wire 3.2 only) and `client` as an
/// ordinary authorized key.
async fn start_gateway(client: &PqKeyExchange) -> Gateway {
    start_gateway_with(client, &["3.2"], "").await
}

/// A gateway that accepts `versions` (`proxy.versions`), with `client`
/// authorized by a line that carries `key_options` (`"wire=2.1"`, or nothing
/// for an ordinary 3.2 key).
async fn start_gateway_with(
    client: &PqKeyExchange,
    versions: &[&str],
    key_options: &str,
) -> Gateway {
    start_gateway_with_keys(
        client.falcon_pk_bytes(),
        client.slh_dsa_pk_bytes(),
        versions,
        key_options,
    )
    .await
}

/// The same, from the client's two public keys: all an operator ever has.
async fn start_gateway_with_keys(
    falcon_vk: &[u8],
    slh_dsa_vk: &[u8],
    versions: &[&str],
    key_options: &str,
) -> Gateway {
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
    let client_sae_route = kme
        .mock_async(|when, then| {
            when.method(POST)
                .path(format!("/api/v1/keys/{CLIENT_SAE}/enc_keys"));
            then.status(200).json_body(json!({
                "keys": [{ "key_ID": QKD_KEY_ID, "key": B64.encode(QKD_BYTES) }]
            }));
        })
        .await
        .id;

    let identity = PqKeyExchange::new().unwrap();
    let pin = identity.identity_fingerprint();
    let key_path = dir.0.join("proxy.key");
    identity.save(&key_path).unwrap();

    let mut vks = falcon_vk.to_vec();
    vks.extend_from_slice(slh_dsa_vk);
    let authorized = dir.0.join("authorized_keys");
    std::fs::write(
        &authorized,
        format!(
            "falcon512+slh-dsa-shake128f {} perm=read,write {key_options} e2e@client\n",
            B64.encode(&vks)
        ),
    )
    .unwrap();

    let mut config = ProxyConfig::default();
    assert_eq!(
        config.proxy.versions,
        vec!["3.2".to_string()],
        "the default must be wire 3.2 only"
    );
    config.proxy.versions = versions.iter().map(|v| v.to_string()).collect();
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
        client_sae_route,
        kme,
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
    client_v2_named(s, me.falcon_pk_bytes(), me.slh_dsa_pk_bytes(), pin, version).await
}

/// The same handshake from the two public keys alone. The v2 hello is not
/// signed, so this is all it takes to open a session in a client's name:
/// whoever runs it ends up holding the session keys.
async fn client_v2_named(
    s: &mut TcpStream,
    falcon_vk: &[u8],
    slh_dsa_vk: &[u8],
    pin: &[u8; 32],
    version: &str,
) -> Result<PqSession> {
    let kem = EphemeralKemKey::new()?;
    let hello = ClientHello {
        version: version.to_string(),
        client_random: random_bytes::<32>(),
        kem_ek: kem.ek_bytes.clone(),
        falcon_vk: falcon_vk.to_vec(),
        slh_dsa_vk: slh_dsa_vk.to_vec(),
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
    let gw = start_gateway_with(&me, &["3.2"], &format!("sae={CLIENT_SAE}")).await;
    let mut s = TcpStream::connect(gw.addr).await.unwrap();
    let mut session = client_v3(&mut s, &me, &gw.pin, "3.2", true).await.unwrap();
    round_trip(&mut s, &mut session, &me).await;
    round_trip(&mut s, &mut session, &me).await;
    drop(s);
    assert_eq!(
        gw.keys_drawn_for_client_sae().await,
        1,
        "one QKD key for the handshake, under the client's own SAE"
    );
    gw.outcome
        .await
        .unwrap()
        .expect("a clean session ends cleanly");
}

#[tokio::test]
async fn v2_handshake_then_requests_and_responses() {
    let me = PqKeyExchange::new().unwrap();
    let gw = start_gateway_with(&me, &["3.2", "2.1"], "wire=2.1").await;
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
    let gw = start_gateway_with(&me, &["3.2", "2.1"], "wire=2.1").await;
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

// ---- which wire versions a gateway accepts, and for which keys -------------

/// A 2.1 client meets a gateway and gets no session. Returns the gateway's
/// reason.
async fn refused_on_2_1(gw: Gateway, falcon_vk: &[u8], slh_dsa_vk: &[u8]) -> String {
    let mut s = TcpStream::connect(gw.addr).await.unwrap();
    let err = client_v2_named(&mut s, falcon_vk, slh_dsa_vk, &gw.pin, "2.1")
        .await
        .expect_err("a 2.1 hello must get no session here");
    assert!(err.to_string().contains("closed"), "got: {err}");
    server_error(gw.outcome).await
}

/// The default: a gateway refuses a 2.1 hello, also from a client it lists.
/// The same client is served on 3.2.
#[tokio::test]
async fn wire_2_1_is_refused_by_default() {
    let me = PqKeyExchange::new().unwrap();
    let reason = refused_on_2_1(
        start_gateway(&me).await,
        me.falcon_pk_bytes(),
        me.slh_dsa_pk_bytes(),
    )
    .await;
    assert!(reason.contains("wire 2.1 is switched off"), "got: {reason}");

    let gw = start_gateway(&me).await;
    let mut s = TcpStream::connect(gw.addr).await.unwrap();
    let mut session = client_v3(&mut s, &me, &gw.pin, "3.2", false).await.unwrap();
    round_trip(&mut s, &mut session, &me).await;
}

/// Marking a key `wire=2.1` does nothing while the gateway has 2.1 off, and
/// that key is not a 3.2 key either: the client is refused both ways until
/// the operator lists 2.1.
#[tokio::test]
async fn a_key_marked_for_2_1_needs_the_gateway_switch_too() {
    let me = PqKeyExchange::new().unwrap();
    let reason = refused_on_2_1(
        start_gateway_with(&me, &["3.2"], "wire=2.1").await,
        me.falcon_pk_bytes(),
        me.slh_dsa_pk_bytes(),
    )
    .await;
    assert!(reason.contains("wire 2.1 is switched off"), "got: {reason}");

    let gw = start_gateway_with(&me, &["3.2"], "wire=2.1").await;
    let mut s = TcpStream::connect(gw.addr).await.unwrap();
    let err = client_v3(&mut s, &me, &gw.pin, "3.2", false)
        .await
        .expect_err("a key registered for 2.1 must get no 3.2 session");
    assert!(err.to_string().contains("closed"), "got: {err}");
    let reason = server_error(gw.outcome).await;
    assert!(reason.contains("registered for wire 2.1"), "got: {reason}");
}

/// Where 2.1 is on for someone, a key that speaks 3.2 still cannot be named
/// in a 2.1 hello, and a key marked for 2.1 cannot open a 3.2 session.
#[tokio::test]
async fn where_2_1_is_on_each_key_speaks_one_version() {
    // An ordinary key, on a gateway that also serves 2.1 clients.
    let me = PqKeyExchange::new().unwrap();
    let reason = refused_on_2_1(
        start_gateway_with(&me, &["3.2", "2.1"], "").await,
        me.falcon_pk_bytes(),
        me.slh_dsa_pk_bytes(),
    )
    .await;
    assert!(
        reason.contains("registered for wire 3.2 and was presented in a wire 2.1 hello"),
        "got: {reason}"
    );
    let gw = start_gateway_with(&me, &["3.2", "2.1"], &format!("sae={CLIENT_SAE}")).await;
    let mut s = TcpStream::connect(gw.addr).await.unwrap();
    let mut session = client_v3(&mut s, &me, &gw.pin, "3.2", true).await.unwrap();
    round_trip(&mut s, &mut session, &me).await;

    // A key marked for 2.1, on the same kind of gateway.
    let legacy = PqKeyExchange::new().unwrap();
    let gw = start_gateway_with(&legacy, &["3.2", "2.1"], "wire=2.1").await;
    let mut s = TcpStream::connect(gw.addr).await.unwrap();
    let err = client_v3(&mut s, &legacy, &gw.pin, "3.2", false)
        .await
        .expect_err("a key registered for 2.1 must get no 3.2 session");
    assert!(err.to_string().contains("closed"), "got: {err}");
    let reason = server_error(gw.outcome).await;
    assert!(
        reason.contains("registered for wire 2.1 and was presented in a wire 3.2 hello"),
        "got: {reason}"
    );
}

// ---- why: a signed request is a reusable token on wire 2.1 -----------------

/// A key request as the client signs it inside a session: the request bytes
/// and a Falcon-512 signature over those bytes, nothing else. It names no
/// session, no time and no counter (THREAT-MODEL.md, L6).
struct SignedRequest {
    data: Vec<u8>,
    sig: Vec<u8>,
}

/// What a client signs when it asks for a key. This is the plaintext of a
/// request frame, which is what someone who has read one honest frame holds
/// (a leaked direction key, a second gateway the client talks to, a client
/// log). The client's signing key is used here and nowhere after.
fn a_request_the_client_once_signed(client: &PqKeyExchange) -> SignedRequest {
    let data = bincode::serialize(&KeyRequest {
        key_id: String::new(),
        size: 32,
        purpose: "gateway-session e2e".to_string(),
    })
    .unwrap();
    let sig = client.sign_transcript(&data).unwrap();
    SignedRequest { data, sig }
}

/// Seal an already signed request in a session, without any signing key:
/// nonce(12) || E(len(4) || data || sig), the layout of `sign_and_encrypt`.
fn seal_signed(session: &mut PqSession, signed: &SignedRequest) -> Vec<u8> {
    let mut payload = Vec::new();
    payload.extend_from_slice(&(signed.data.len() as u32).to_be_bytes());
    payload.extend_from_slice(&signed.data);
    payload.extend_from_slice(&signed.sig);
    let (ciphertext, nonce) = session.encrypt(&payload).unwrap();
    let mut frame = nonce.to_vec();
    frame.extend_from_slice(&ciphertext);
    frame
}

/// The residual that stays with wire 2.1, on a gateway that lists 2.1 for a
/// client marked `wire=2.1`. Someone who holds one request that client signed,
/// and its two public keys, opens a 2.1 session in its name and is served a
/// key, twice from the same signed request. No secret of the client is used
/// after the request was signed. This is why 2.1 is off by default, and why a
/// gateway that must keep it should keep it for as few keys and as short a
/// time as it can.
#[tokio::test]
async fn on_wire_2_1_a_signed_request_is_served_again_to_someone_else() {
    let client = PqKeyExchange::new().unwrap();
    let signed = a_request_the_client_once_signed(&client);
    let (falcon_vk, slh_dsa_vk) = (
        client.falcon_pk_bytes().to_vec(),
        client.slh_dsa_pk_bytes().to_vec(),
    );
    drop(client);

    for _ in 0..2 {
        let gw =
            start_gateway_with_keys(&falcon_vk, &slh_dsa_vk, &["3.2", "2.1"], "wire=2.1").await;
        let mut s = TcpStream::connect(gw.addr).await.unwrap();
        let mut session = client_v2_named(&mut s, &falcon_vk, &slh_dsa_vk, &gw.pin, "2.1")
            .await
            .expect("anyone can open a 2.1 session in a listed client's name");
        write_frame(&mut s, &seal_signed(&mut session, &signed))
            .await
            .unwrap();
        let response = read_frame(&mut s)
            .await
            .expect("the gateway answers the replayed request");
        open_response(&mut session, &response);
    }
}

/// The same holder of the same signed request, against the default gateway
/// and against a gateway that has 2.1 on for other clients: no session, so
/// nothing to replay the request in. The client here is an ordinary 3.2 key.
#[tokio::test]
async fn a_signed_request_of_a_3_2_client_finds_no_2_1_session() {
    let client = PqKeyExchange::new().unwrap();
    let _signed = a_request_the_client_once_signed(&client);
    let (falcon_vk, slh_dsa_vk) = (
        client.falcon_pk_bytes().to_vec(),
        client.slh_dsa_pk_bytes().to_vec(),
    );
    drop(client);

    let default = start_gateway_with_keys(&falcon_vk, &slh_dsa_vk, &["3.2"], "").await;
    let reason = refused_on_2_1(default, &falcon_vk, &slh_dsa_vk).await;
    assert!(reason.contains("wire 2.1 is switched off"), "got: {reason}");

    let mixed = start_gateway_with_keys(&falcon_vk, &slh_dsa_vk, &["3.2", "2.1"], "").await;
    let reason = refused_on_2_1(mixed, &falcon_vk, &slh_dsa_vk).await;
    assert!(reason.contains("registered for wire 3.2"), "got: {reason}");
}

// ---- a QKD key only for an SAE ID of the client's own line -----------------

/// A hybrid hello meets a gateway and gets no session. Returns the gateway's
/// reason, and how many keys were drawn under `CLIENT_SAE`.
async fn refused_hybrid(gw: Gateway, me: &PqKeyExchange) -> (String, usize) {
    let mut s = TcpStream::connect(gw.addr).await.unwrap();
    let err = client_v3(&mut s, me, &gw.pin, "3.2", true)
        .await
        .expect_err("this client must get no session when it names that SAE");
    assert!(err.to_string().contains("closed"), "got: {err}");
    let Gateway {
        outcome,
        client_sae_route,
        kme,
        _dir,
        ..
    } = gw;
    let reason = server_error(outcome).await;
    let drawn = httpmock::Mock::new(client_sae_route, &kme)
        .hits_async()
        .await;
    (reason, drawn)
}

/// The default for a key whose line lists no SAE: it gets no QKD key. Its
/// hello is refused when it names an SAE, with what to add, and the key
/// manager is not asked. The same client is served when it asks for none.
#[tokio::test]
async fn a_key_with_no_sae_list_gets_no_qkd_key() {
    let me = PqKeyExchange::new().unwrap();
    let (reason, drawn) = refused_hybrid(start_gateway(&me).await, &me).await;
    assert!(reason.contains("lists no SAE"), "got: {reason}");
    assert!(
        reason.contains(&format!("sae={CLIENT_SAE}")),
        "got: {reason}"
    );
    assert_eq!(drawn, 0, "no key may be drawn for a refused hello");

    let gw = start_gateway(&me).await;
    let mut s = TcpStream::connect(gw.addr).await.unwrap();
    let mut session = client_v3(&mut s, &me, &gw.pin, "3.2", false).await.unwrap();
    round_trip(&mut s, &mut session, &me).await;
    assert_eq!(gw.keys_drawn_for_client_sae().await, 0);
}

/// What the list is for. A client whose line lists its own SAE names another
/// client's SAE (`CLIENT_SAE`, which the key manager would serve). Before the
/// list existed the gateway drew a key under that SAE for it, and a client
/// could use up another client's keys that way. Now the hello is refused and
/// nothing is drawn.
#[tokio::test]
async fn a_client_cannot_draw_keys_under_another_clients_sae() {
    let me = PqKeyExchange::new().unwrap();
    let gw = start_gateway_with(&me, &["3.2"], "sae=sae-of-this-client,sae-second").await;
    let (reason, drawn) = refused_hybrid(gw, &me).await;
    assert!(reason.contains("not among the SAE IDs"), "got: {reason}");
    assert!(
        reason.contains("sae-of-this-client, sae-second"),
        "got: {reason}"
    );
    assert_eq!(drawn, 0, "the other client's SAE must not be touched");

    // A near miss is a miss: the list is matched exactly.
    for near in [
        format!("sae={CLIENT_SAE}-2"),
        format!("sae={}", CLIENT_SAE.to_uppercase()),
        format!("sae={}", &CLIENT_SAE[..CLIENT_SAE.len() - 1]),
    ] {
        let gw = start_gateway_with(&me, &["3.2"], &near).await;
        let (reason, drawn) = refused_hybrid(gw, &me).await;
        assert!(reason.contains("not among the SAE IDs"), "{near}: {reason}");
        assert_eq!(drawn, 0, "{near}");
    }
}

/// The refusal comes after the signature check: a hello that names a listed
/// client and another SAE, sent by someone who does not hold that client's
/// key, is refused for its signature and never reaches the SAE check.
#[tokio::test]
async fn an_unsigned_hello_is_refused_before_the_sae_check() {
    let me = PqKeyExchange::new().unwrap();
    let stranger = PqKeyExchange::new().unwrap();
    let gw = start_gateway_with(&me, &["3.2"], "sae=sae-of-this-client").await;
    let mut s = TcpStream::connect(gw.addr).await.unwrap();

    // The listed client's public keys, a hybrid request for CLIENT_SAE, and
    // a signature made with the stranger's key.
    let kem = EphemeralKemKey::new().unwrap();
    let mut hello = ClientHelloV3 {
        version: "3.2".to_string(),
        client_random: random_bytes::<32>(),
        kem_ek: kem.ek_bytes.clone(),
        falcon_vk: stranger.falcon_pk_bytes().to_vec(),
        slh_dsa_vk: stranger.slh_dsa_pk_bytes().to_vec(),
        requested_key_size: 32,
        client_sae_id: CLIENT_SAE.to_string(),
        qkd_capable: true,
        timestamp: unix_now(),
        hello_sig: Vec::new(),
    };
    hello.sign(&stranger).unwrap();
    hello.falcon_vk = me.falcon_pk_bytes().to_vec();
    hello.slh_dsa_vk = me.slh_dsa_pk_bytes().to_vec();
    write_frame(&mut s, &bincode::serialize(&hello).unwrap())
        .await
        .unwrap();
    assert!(read_frame(&mut s).await.is_none(), "no ServerHello");

    let drawn = gw.keys_drawn_for_client_sae().await;
    let reason = server_error(gw.outcome).await;
    assert!(reason.contains("signature"), "got: {reason}");
    assert!(!reason.contains("SAE"), "got: {reason}");
    assert_eq!(drawn, 0);
}
