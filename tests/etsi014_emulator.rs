//! Integration tests against an ETSI GS QKD 014 v1.1.1 emulator.
//!
//! Uses `httpmock` to stand up a mock vendor KME (Key Management Entity)
//! that serves canned responses for the three spec endpoints:
//!
//!   GET  /api/v1/keys/{slave_SAE_ID}/status
//!   POST /api/v1/keys/{slave_SAE_ID}/enc_keys
//!   POST /api/v1/keys/{master_SAE_ID}/dec_keys
//!
//! These tests exercise the `QkdClient` end-to-end against the emulator —
//! no real QKD hardware required. Reviewers and KirQ engineers can run
//! `cargo test --test etsi014_emulator` and verify the proxy speaks the
//! standard correctly.

use base64::Engine as _;
use httpmock::prelude::*;
use httpmock::Method::POST;
use pq_qkd_proxy::ProxyConfig;
use pq_qkd_proxy::QkdClient;
use serde_json::json;

/// Build a `QkdClient` pointed at a running httpmock server, with a chosen
/// pair of default SAE_IDs.
fn make_client(server_url: &str, slave_sae: &str, master_sae: &str) -> QkdClient {
    let mut config = ProxyConfig::default();
    config.qkd.vendor_api = server_url.to_string();
    config.qkd.vendor_cert = None;
    config.qkd.default_slave_sae_id = slave_sae.to_string();
    config.qkd.default_master_sae_id = master_sae.to_string();
    config.qkd.key_timeout = 2;
    QkdClient::new(&config).expect("client init")
}

#[tokio::test]
async fn status_endpoint_round_trip() {
    let server = MockServer::start_async().await;
    let mock = server
        .mock_async(|when, then| {
            when.method(GET).path("/api/v1/keys/sae-slave-1/status");
            then.status(200)
                .header("content-type", "application/json")
                .json_body(json!({
                    "source_KME_ID": "kme-A",
                    "target_KME_ID": "kme-B",
                    "master_SAE_ID": "sae-master-1",
                    "slave_SAE_ID": "sae-slave-1",
                    "key_size": 256,
                    "stored_key_count": 50,
                    "max_key_count": 1024,
                    "max_key_per_request": 8,
                    "max_key_size": 1024,
                    "min_key_size": 64,
                    "max_SAE_ID_count": 4
                }));
        })
        .await;

    let client = make_client(&server.url(""), "sae-slave-1", "sae-master-1");
    let status = client.status("sae-slave-1").await.expect("status ok");
    assert_eq!(status.source_KME_ID, "kme-A");
    assert_eq!(status.master_SAE_ID, "sae-master-1");
    assert_eq!(status.key_size, 256);
    assert_eq!(status.stored_key_count, 50);
    mock.assert_async().await;
}

#[tokio::test]
async fn enc_keys_returns_single_decoded_key() {
    let server = MockServer::start_async().await;
    // 32 bytes of 0xAA, base64-encoded.
    let key_b64 = base64::engine::general_purpose::STANDARD.encode([0xAAu8; 32]);
    let mock = server
        .mock_async(|when, then| {
            when.method(POST).path("/api/v1/keys/sae-slave-2/enc_keys");
            then.status(200)
                .header("content-type", "application/json")
                .json_body(json!({
                    "keys": [
                        { "key_ID": "11111111-2222-3333-4444-555555555555",
                          "key": key_b64 }
                    ]
                }));
        })
        .await;

    let client = make_client(&server.url(""), "sae-slave-2", "sae-master-2");
    let key = client.get_key(32).await.expect("get_key ok");
    assert_eq!(key.key_id, "11111111-2222-3333-4444-555555555555");
    assert_eq!(key.key_data.len(), 32);
    assert!(key.key_data.iter().all(|&b| b == 0xAA));
    mock.assert_async().await;
}

#[tokio::test]
async fn enc_keys_wrong_size_rejected() {
    let server = MockServer::start_async().await;
    // Server returns 16 bytes when client asked for 32.
    let key_b64 = base64::engine::general_purpose::STANDARD.encode([0xCCu8; 16]);
    server
        .mock_async(|when, then| {
            when.method(POST).path("/api/v1/keys/sae-slave-3/enc_keys");
            then.status(200).json_body(json!({
                "keys": [{ "key_ID": "uuid-bad-size", "key": key_b64 }]
            }));
        })
        .await;

    let client = make_client(&server.url(""), "sae-slave-3", "sae-master-3");
    let err = client.get_key(32).await.unwrap_err();
    assert!(
        err.to_string().contains("wrong key size"),
        "expected size mismatch error, got: {err}"
    );
}

#[tokio::test]
async fn enc_keys_503_with_etsi_error_body() {
    let server = MockServer::start_async().await;
    server
        .mock_async(|when, then| {
            when.method(POST).path("/api/v1/keys/sae-slave-4/enc_keys");
            then.status(503).json_body(json!({
                "message": "no keys available",
                "details": { "stored_key_count": 0 }
            }));
        })
        .await;

    let client = make_client(&server.url(""), "sae-slave-4", "sae-master-4");
    let err = client.get_key(32).await.unwrap_err();
    let msg = err.to_string();
    assert!(msg.contains("503"), "expected 503 in error: {msg}");
    assert!(
        msg.contains("no keys available"),
        "expected ETSI message in error: {msg}"
    );
}

#[tokio::test]
async fn enc_keys_400_with_etsi_error_body() {
    let server = MockServer::start_async().await;
    server
        .mock_async(|when, then| {
            when.method(POST).path("/api/v1/keys/sae-slave-5/enc_keys");
            then.status(400).json_body(json!({
                "message": "requested key size exceeds maximum",
                "details": { "max_key_size": 1024, "requested": 2048 }
            }));
        })
        .await;

    let client = make_client(&server.url(""), "sae-slave-5", "sae-master-5");
    let err = client.get_key(32).await.unwrap_err();
    let msg = err.to_string();
    assert!(msg.contains("400"), "expected 400 in error: {msg}");
    assert!(msg.contains("requested key size exceeds maximum"));
}

#[tokio::test]
async fn dec_keys_fetch_by_id_round_trip() {
    let server = MockServer::start_async().await;
    let key_b64 = base64::engine::general_purpose::STANDARD.encode([0x11u8; 32]);
    let mock = server
        .mock_async(|when, then| {
            when.method(POST).path("/api/v1/keys/sae-master-6/dec_keys");
            then.status(200).json_body(json!({
                "keys": [
                    { "key_ID": "uuid-A", "key": key_b64 }
                ]
            }));
        })
        .await;

    let client = make_client(&server.url(""), "sae-slave-6", "sae-master-6");
    let keys = client
        .get_keys_by_id(&["uuid-A".to_string()])
        .await
        .expect("dec_keys ok");
    assert_eq!(keys.len(), 1);
    assert_eq!(keys[0].key_id, "uuid-A");
    assert_eq!(keys[0].key_data.len(), 32);
    mock.assert_async().await;
}

#[tokio::test]
async fn dec_keys_carries_key_ids_in_request_body() {
    let server = MockServer::start_async().await;
    let key_b64 = base64::engine::general_purpose::STANDARD.encode([0x22u8; 32]);
    // Match the exact JSON body the client should be sending.
    let mock = server
        .mock_async(|when, then| {
            when.method(POST)
                .path("/api/v1/keys/sae-master-7/dec_keys")
                .json_body(json!({
                    "key_IDs": [
                        { "key_ID": "uuid-1" },
                        { "key_ID": "uuid-2" }
                    ]
                }));
            then.status(200).json_body(json!({
                "keys": [
                    { "key_ID": "uuid-1", "key": key_b64 },
                    { "key_ID": "uuid-2", "key": key_b64 }
                ]
            }));
        })
        .await;

    let client = make_client(&server.url(""), "sae-slave-7", "sae-master-7");
    let ids = vec!["uuid-1".to_string(), "uuid-2".to_string()];
    let keys = client.get_keys_by_id(&ids).await.expect("dec_keys ok");
    assert_eq!(keys.len(), 2);
    mock.assert_async().await;
}

#[tokio::test]
async fn enc_keys_supports_multi_key_request() {
    use pq_qkd_proxy::ProxyConfig;
    let server = MockServer::start_async().await;
    let key_a = base64::engine::general_purpose::STANDARD.encode([0xAAu8; 32]);
    let key_b = base64::engine::general_purpose::STANDARD.encode([0xBBu8; 32]);
    server
        .mock_async(|when, then| {
            when.method(POST).path("/api/v1/keys/sae-slave-8/enc_keys");
            then.status(200).json_body(json!({
                "keys": [
                    { "key_ID": "uuid-a", "key": key_a },
                    { "key_ID": "uuid-b", "key": key_b }
                ]
            }));
        })
        .await;

    let mut config = ProxyConfig::default();
    config.qkd.vendor_api = server.url("");
    config.qkd.default_slave_sae_id = "sae-slave-8".into();
    config.qkd.default_master_sae_id = "sae-master-8".into();
    let client = QkdClient::new(&config).unwrap();

    let req = pq_qkd_proxy::qkd_client::EncKeysRequest {
        number: Some(2),
        size: Some(256),
        ..Default::default()
    };
    let container = client
        .enc_keys("sae-slave-8", &req)
        .await
        .expect("enc_keys ok");
    assert_eq!(container.keys.len(), 2);
}

#[tokio::test]
async fn status_propagates_extension_field() {
    let server = MockServer::start_async().await;
    server
        .mock_async(|when, then| {
            when.method(GET).path("/api/v1/keys/sae-slave-9/status");
            then.status(200).json_body(json!({
                "source_KME_ID": "kme-A",
                "target_KME_ID": "kme-B",
                "master_SAE_ID": "sae-master-9",
                "slave_SAE_ID": "sae-slave-9",
                "key_size": 256,
                "stored_key_count": 100,
                "max_key_count": 1024,
                "max_key_per_request": 16,
                "max_key_size": 1024,
                "min_key_size": 64,
                "max_SAE_ID_count": 8,
                "status_extension": { "vendor": "Toshiba", "lot": "kirq-test-1" }
            }));
        })
        .await;

    let client = make_client(&server.url(""), "sae-slave-9", "sae-master-9");
    let status = client.status("sae-slave-9").await.unwrap();
    let ext = status.status_extension.expect("extension present");
    assert_eq!(ext["vendor"], "Toshiba");
    assert_eq!(ext["lot"], "kirq-test-1");
}
