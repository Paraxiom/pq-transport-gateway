//! Audit logging for security compliance

use anyhow::Result;
use chrono::{DateTime, Utc};
use serde::Serialize;
use std::fs::OpenOptions;
use std::io::Write;
use std::net::SocketAddr;
use std::sync::Mutex;

static AUDIT_LOG: Mutex<Option<std::fs::File>> = Mutex::new(None);

#[derive(Serialize)]
struct AuditEntry {
    timestamp: DateTime<Utc>,
    event_type: String,
    details: serde_json::Value,
}

pub fn init(path: &str) -> Result<()> {
    // Create parent directory if needed
    if let Some(parent) = std::path::Path::new(path).parent() {
        std::fs::create_dir_all(parent)?;
    }

    let file = OpenOptions::new().create(true).append(true).open(path)?;

    *AUDIT_LOG.lock().unwrap() = Some(file);

    Ok(())
}

pub fn log_startup(config: &crate::config::Config) {
    write_entry(
        "startup",
        serde_json::json!({
            "version": env!("CARGO_PKG_VERSION"),
            "listen_address": config.proxy.listen.to_string(),
            "pq_algorithm": &config.security.pq_algorithm,
            "sig_algorithm": &config.security.sig_algorithm,
        }),
    );
}

pub fn log_connection(peer: &SocketAddr) {
    write_entry(
        "connection",
        serde_json::json!({
            "peer_address": peer.to_string(),
        }),
    );
}

pub fn log_key_request(peer: &SocketAddr, key_id: &str, size: usize) {
    write_entry(
        "key_request",
        serde_json::json!({
            "peer_address": peer.to_string(),
            "key_id": key_id,
            "size": size,
        }),
    );
}

pub fn log_qkd_key_used(peer: &SocketAddr, key_id: &str) {
    write_entry(
        "qkd_key_used",
        serde_json::json!({
            "peer_address": peer.to_string(),
            "qkd_key_id": key_id,
        }),
    );
}

pub fn log_auth_failure(peer: &SocketAddr, reason: &str) {
    write_entry(
        "auth_failure",
        serde_json::json!({
            "peer_address": peer.to_string(),
            "reason": reason,
        }),
    );
}

/// Audit-log helper for unexpected internal errors. Currently called only
/// from rare paths; `#[allow(dead_code)]` because the bin's hot path goes
/// through `tracing::error!` instead.
#[allow(dead_code)]
pub fn log_error(context: &str, error: &str) {
    write_entry(
        "error",
        serde_json::json!({
            "context": context,
            "error": error,
        }),
    );
}

fn write_entry(event_type: &str, details: serde_json::Value) {
    let entry = AuditEntry {
        timestamp: Utc::now(),
        event_type: event_type.to_string(),
        details,
    };

    let json = match serde_json::to_string(&entry) {
        Ok(j) => j,
        Err(e) => {
            eprintln!("Failed to serialize audit entry: {}", e);
            return;
        }
    };

    let mut guard = AUDIT_LOG.lock().unwrap();
    if let Some(file) = guard.as_mut() {
        if let Err(e) = writeln!(file, "{}", json) {
            eprintln!("Failed to write audit log: {}", e);
        }

        // Ensure it's flushed
        let _ = file.flush();
    }
}
