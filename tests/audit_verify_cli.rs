//! End to end: the `--verify-audit-log` command accepts a log signed by the
//! identity in `proxy.pub`, exits 1 once a covered line is changed, and exits
//! 2 for a log nothing verifies.

use pq_qkd_proxy::audit::AuditLog;
use pq_qkd_proxy::crypto::PqKeyExchange;
use serde_json::json;
use std::path::Path;
use std::process::Command;
use std::sync::Arc;

fn verify(log: &Path, bundle: &Path) -> (i32, String) {
    let out = Command::new(env!("CARGO_BIN_EXE_pq-qkd-proxy"))
        .arg("--verify-audit-log")
        .arg(log)
        .arg(bundle)
        .output()
        .unwrap();
    (
        out.status.code().unwrap(),
        String::from_utf8_lossy(&out.stdout).into_owned(),
    )
}

#[test]
fn verify_command_accepts_a_signed_log_and_rejects_a_changed_one() {
    let dir = std::env::temp_dir().join(format!("pqtg-audit-cli-{}", uuid::Uuid::new_v4()));
    std::fs::create_dir_all(&dir).unwrap();
    let log_path = dir.join("audit.log");
    let bundle_path = dir.join("proxy.pub");

    let key = Arc::new(PqKeyExchange::new().unwrap());
    let mut bundle = key.falcon_pk_bytes().to_vec();
    bundle.extend_from_slice(key.slh_dsa_pk_bytes());
    std::fs::write(&bundle_path, &bundle).unwrap();

    let log = AuditLog::open(&log_path, Some(Arc::clone(&key)), 1000).unwrap();
    for peer in ["10.0.0.1:4000", "10.0.0.2:4000"] {
        log.record("connection", json!({ "peer_address": peer }))
            .unwrap();
    }
    assert!(log.checkpoint_now().unwrap());
    log.record("connection", json!({ "peer_address": "10.0.0.3:4000" }))
        .unwrap();

    let (code, out) = verify(&log_path, &bundle_path);
    assert_eq!(code, 0, "{out}");
    assert!(out.contains("Result: OK"), "{out}");
    assert!(
        out.contains("1 event(s) after the last checkpoint"),
        "{out}"
    );

    let text = std::fs::read_to_string(&log_path).unwrap();
    std::fs::write(&log_path, text.replace("10.0.0.2", "10.0.0.9")).unwrap();
    let (code, out) = verify(&log_path, &bundle_path);
    assert_eq!(code, 1, "{out}");
    assert!(out.contains("Result: FAILED"), "{out}");

    // A run without a signing key is chained but proves nothing: exit 2.
    let unsigned_path = dir.join("unsigned.log");
    let unsigned = AuditLog::open(&unsigned_path, None, 1000).unwrap();
    unsigned
        .record("connection", json!({ "peer_address": "10.0.0.4:4000" }))
        .unwrap();
    let (code, out) = verify(&unsigned_path, &bundle_path);
    assert_eq!(code, 2, "{out}");
    assert!(out.contains("Result: NOT VERIFIED"), "{out}");

    std::fs::remove_dir_all(dir).ok();
}
