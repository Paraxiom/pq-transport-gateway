//! `audit_enabled = false` must stop the gateway writing its audit log; it
//! used to be ignored. Starts the real binary against a vendor API that is
//! not listening, so it exits right after startup, where the log is opened.

use std::path::{Path, PathBuf};
use std::process::Command;

fn run_gateway(dir: &Path, audit_enabled: bool) -> PathBuf {
    let audit_log = dir.join(format!("audit-{audit_enabled}.log"));
    let authorized_keys = dir.join("authorized_keys");
    std::fs::write(&authorized_keys, "").unwrap();
    let config = format!(
        r#"
[proxy]
listen = "127.0.0.1:0"

[qkd]
vendor_api = "https://localhost:9"
default_slave_sae_id = "sae-b"
default_master_sae_id = "sae-a"

[security]
pq_algorithm = "falcon512"
sig_algorithm = "sphincsplus"
authorized_keys = "{}"
proxy_private_key = "{}"
proxy_certificate = "{}"
audit_enabled = {audit_enabled}
audit_log = "{}"

[performance]
"#,
        authorized_keys.display(),
        dir.join("proxy.key").display(),
        dir.join("proxy.crt").display(),
        audit_log.display(),
    );
    let config_path = dir.join(format!("config-{audit_enabled}.toml"));
    std::fs::write(&config_path, config).unwrap();

    let status = Command::new(env!("CARGO_BIN_EXE_pq-qkd-proxy"))
        .env("PQ_QKD_PROXY_CONFIG", &config_path)
        .status()
        .unwrap();
    assert!(
        !status.success(),
        "the vendor API is not listening, so startup must fail"
    );
    audit_log
}

#[test]
fn audit_enabled_false_writes_no_audit_log() {
    let dir = std::env::temp_dir().join(format!("pqtg-audit-enabled-{}", uuid::Uuid::new_v4()));
    std::fs::create_dir_all(&dir).unwrap();

    let disabled = run_gateway(&dir, false);
    assert!(
        !disabled.exists(),
        "audit_enabled = false wrote {}",
        disabled.display()
    );

    // Same config with the log enabled: the file appears, so the run above
    // got as far as where the log is opened.
    let enabled = run_gateway(&dir, true);
    let text = std::fs::read_to_string(&enabled).unwrap();
    assert!(text.contains("\"segment_start\""), "{text}");
    assert!(text.contains("\"startup\""), "{text}");

    std::fs::remove_dir_all(dir).ok();
}
