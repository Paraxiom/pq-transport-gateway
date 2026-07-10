// Field names follow ETSI GS QKD 014 v1.1.1 §5 exactly (`source_KME_ID`,
// `slave_SAE_ID`, `key_ID`, etc.). These are protocol identifiers, not Rust
// idiomatic names — `non_snake_case` is intentional.
#![allow(non_snake_case)]

//! ETSI GS QKD 014 v1.1.1 client.
//!
//! Implements the three endpoints defined by the standard:
//!
//!   GET  /api/v1/keys/{slave_SAE_ID}/status        → Status
//!   GET  /api/v1/keys/{slave_SAE_ID}/enc_keys      → Key container
//!         (or POST with body for `number`/`size`/`additional_slave_SAE_IDs`)
//!   GET  /api/v1/keys/{master_SAE_ID}/dec_keys?key_IDs=…  → Key container
//!         (or POST with body for `key_IDs`)
//!
//! Field names match the spec exactly. Error responses follow §5.3
//! (`{ message, details }` with HTTP 400/401/503).
//!
//! Note: the proxy currently authenticates clients via Falcon-512+SLH-DSA
//! at the PQTG layer; SAE_IDs are used as logical labels into the vendor
//! API. A future revision should bind a SAE_ID to a Falcon vk fingerprint
//! at the auth layer.

use crate::config::Config;
use anyhow::{anyhow, Result};
use base64::{engine::general_purpose, Engine as _};
use reqwest::{Certificate, Client, StatusCode};
use serde::{Deserialize, Serialize};
use tracing::debug;

// ── ETSI 014 v1.1.1 §5.1 Status object ──────────────────────────────────────

/// Status response: `GET /api/v1/keys/{slave_SAE_ID}/status`.
#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct Status {
    pub source_KME_ID: String,
    pub target_KME_ID: String,
    pub master_SAE_ID: String,
    pub slave_SAE_ID: String,
    /// Default key size in bits.
    pub key_size: u32,
    pub stored_key_count: u32,
    pub max_key_count: u32,
    pub max_key_per_request: u32,
    pub max_key_size: u32,
    pub min_key_size: u32,
    pub max_SAE_ID_count: u32,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub status_extension: Option<serde_json::Value>,
}

// ── ETSI 014 v1.1.1 §5.2 Key container ──────────────────────────────────────

/// Key container: response to `enc_keys` or `dec_keys`.
#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct KeyContainer {
    pub keys: Vec<Key>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub key_container_extension: Option<serde_json::Value>,
}

#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct Key {
    /// UUID per RFC 4122.
    pub key_ID: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub key_ID_extension: Option<serde_json::Value>,
    /// Base64-encoded key material per RFC 4648.
    pub key: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub key_extension: Option<serde_json::Value>,
}

// ── ETSI 014 v1.1.1 §5.3 Error format ───────────────────────────────────────

#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct EtsiError {
    pub message: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub details: Option<serde_json::Value>,
}

// ── enc_keys / dec_keys request bodies (POST variant) ───────────────────────

/// `POST /api/v1/keys/{slave_SAE_ID}/enc_keys` body.
#[derive(Debug, Clone, Default, Serialize)]
pub struct EncKeysRequest {
    #[serde(skip_serializing_if = "Option::is_none")]
    pub number: Option<u32>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub size: Option<u32>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub additional_slave_SAE_IDs: Option<Vec<String>>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub extension_mandatory: Option<Vec<serde_json::Value>>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub extension_optional: Option<Vec<serde_json::Value>>,
}

/// `POST /api/v1/keys/{master_SAE_ID}/dec_keys` body.
/// Used by the slave-SAE-side flow; bin currently ships master-side only,
/// so `#[allow(dead_code)]` here.
#[derive(Debug, Clone, Serialize)]
#[allow(dead_code)]
pub struct DecKeysRequest {
    pub key_IDs: Vec<KeyID>,
}

#[derive(Debug, Clone, Serialize)]
#[allow(dead_code)]
pub struct KeyID {
    pub key_ID: String,
}

// ── Decoded form for internal proxy use ─────────────────────────────────────

/// A QKD key after base64 decoding. Internal type; the wire format is
/// the ETSI `Key` above with base64 string.
#[derive(Debug)]
pub struct QkdKey {
    pub key_id: String,
    pub key_data: Vec<u8>,
}

// ── Client ──────────────────────────────────────────────────────────────────

pub struct QkdClient {
    client: Client,
    base_url: String,
    api_key: Option<String>,
    /// Default slave SAE_ID used when one isn't supplied per-request (e.g.
    /// the simple `get_key(size)` shortcut). Set from config.
    default_slave_sae_id: String,
    /// Used only by `get_keys_by_id` (slave-SAE side). `#[allow(dead_code)]`
    /// at the field level until the bin wires the slave flow.
    #[allow(dead_code)]
    default_master_sae_id: String,
}

impl QkdClient {
    pub fn new(config: &Config) -> Result<Self> {
        let mut client_builder =
            Client::builder().timeout(std::time::Duration::from_secs(config.qkd.key_timeout));

        if let Some(cert_path) = &config.qkd.vendor_cert {
            let cert_bytes = std::fs::read(cert_path)?;
            let cert = Certificate::from_pem(&cert_bytes)?;
            client_builder = client_builder.add_root_certificate(cert);
        }

        // Issue #4: cert validation is now configurable. Default `false`
        // matches the historical behaviour (most vendor KMEs ship
        // self-signed certs); production deployments that issue proper
        // certs should set `qkd.tls_verify = true` in their config.
        client_builder = client_builder
            .danger_accept_invalid_certs(!config.qkd.tls_verify)
            .no_proxy();

        let client = client_builder.build()?;

        Ok(Self {
            client,
            base_url: config.qkd.vendor_api.clone(),
            api_key: config.qkd.vendor_api_key.clone(),
            default_slave_sae_id: config.qkd.default_slave_sae_id.clone(),
            default_master_sae_id: config.qkd.default_master_sae_id.clone(),
        })
    }

    fn auth(&self, builder: reqwest::RequestBuilder) -> reqwest::RequestBuilder {
        if let Some(api_key) = &self.api_key {
            builder.header("X-API-Key", api_key)
        } else {
            builder
        }
    }

    async fn parse_response<T: for<'de> Deserialize<'de>>(
        response: reqwest::Response,
    ) -> Result<T> {
        let status = response.status();
        if status.is_success() {
            return Ok(response.json::<T>().await?);
        }
        // Try to parse a structured ETSI error; fall back to status text.
        let body = response.text().await.unwrap_or_default();
        if let Ok(err) = serde_json::from_str::<EtsiError>(&body) {
            return Err(match status {
                StatusCode::BAD_REQUEST => anyhow!("ETSI 014 400 Bad Request: {}", err.message),
                StatusCode::UNAUTHORIZED => anyhow!("ETSI 014 401 Unauthorized: {}", err.message),
                StatusCode::SERVICE_UNAVAILABLE => {
                    anyhow!("ETSI 014 503 Service Unavailable: {}", err.message)
                }
                _ => anyhow!("ETSI 014 {}: {}", status, err.message),
            });
        }
        Err(anyhow!("ETSI 014 {}: {}", status, body))
    }

    // ── Status (§5.1) ───────────────────────────────────────────────────────

    /// `GET /api/v1/keys/{slave_SAE_ID}/status`.
    pub async fn status(&self, slave_sae_id: &str) -> Result<Status> {
        let url = format!(
            "{}/api/v1/keys/{}/status",
            self.base_url.trim_end_matches('/'),
            slave_sae_id
        );
        let req = self.auth(self.client.get(&url));
        Self::parse_response(req.send().await?).await
    }

    /// Convenience: status against the default slave SAE_ID from config.
    pub async fn check_connectivity(&self) -> Result<()> {
        let _: Status = self.status(&self.default_slave_sae_id).await?;
        Ok(())
    }

    // ── enc_keys (§5.2, master SAE side) ────────────────────────────────────

    /// `POST /api/v1/keys/{slave_SAE_ID}/enc_keys`.
    /// Returns the key container; caller decodes base64 keys as needed.
    pub async fn enc_keys(
        &self,
        slave_sae_id: &str,
        request: &EncKeysRequest,
    ) -> Result<KeyContainer> {
        let url = format!(
            "{}/api/v1/keys/{}/enc_keys",
            self.base_url.trim_end_matches('/'),
            slave_sae_id
        );
        let req = self.auth(self.client.post(&url).json(request));
        Self::parse_response(req.send().await?).await
    }

    // ── dec_keys (§5.2, slave SAE side) ─────────────────────────────────────

    /// `POST /api/v1/keys/{master_SAE_ID}/dec_keys`.
    /// Slave-SAE-side flow; bin currently ships master-side only.
    #[allow(dead_code)]
    pub async fn dec_keys(
        &self,
        master_sae_id: &str,
        request: &DecKeysRequest,
    ) -> Result<KeyContainer> {
        let url = format!(
            "{}/api/v1/keys/{}/dec_keys",
            self.base_url.trim_end_matches('/'),
            master_sae_id
        );
        let req = self.auth(self.client.post(&url).json(request));
        Self::parse_response(req.send().await?).await
    }

    // ── Convenience helpers used by the proxy ───────────────────────────────

    /// Fetch a single key against the default slave SAE_ID, with a specified
    /// key size in bytes (translated to bits per the ETSI 014 wire spec).
    pub async fn get_key(&self, size_bytes: usize) -> Result<QkdKey> {
        // Issue #5: defensive overflow check. Bounded by max_key_size = 1 MB
        // in practice, but `checked_mul` future-proofs against config bumps.
        let size_bits: u32 = size_bytes
            .checked_mul(8)
            .and_then(|n| u32::try_from(n).ok())
            .ok_or_else(|| {
                anyhow!(
                    "Key size {} bytes overflows u32 bit count for ETSI 014 wire format",
                    size_bytes
                )
            })?;
        let req = EncKeysRequest {
            number: Some(1),
            size: Some(size_bits),
            ..Default::default()
        };
        let container = self.enc_keys(&self.default_slave_sae_id, &req).await?;
        let key = container
            .keys
            .into_iter()
            .next()
            .ok_or_else(|| anyhow!("ETSI 014: enc_keys returned empty container"))?;
        let bytes = general_purpose::STANDARD.decode(&key.key)?;
        if bytes.len() != size_bytes {
            return Err(anyhow!(
                "ETSI 014: vendor returned wrong key size: expected {} bytes, got {}",
                size_bytes,
                bytes.len()
            ));
        }
        debug!(
            "Retrieved QKD key: id={}, size={} bytes",
            key.key_ID, size_bytes
        );
        Ok(QkdKey {
            key_id: key.key_ID,
            key_data: bytes,
        })
    }

    /// Fetch keys-by-ID against the default master SAE_ID. Used by the slave
    /// SAE side to retrieve keys whose IDs were communicated out-of-band by
    /// the master.
    ///
    /// Issue #6: fails loud on any base64 decode error, returning a
    /// structured error containing the offending `key_ID`. The previous
    /// silent-skip behaviour could mask attacks where an attacker corrupts
    /// specific keys.
    ///
    /// `#[allow(dead_code)]`: bin currently ships master-SAE flow only;
    /// this is the slave-side counterpart for clients to use.
    #[allow(dead_code)]
    pub async fn get_keys_by_id(&self, key_ids: &[String]) -> Result<Vec<QkdKey>> {
        let req = DecKeysRequest {
            key_IDs: key_ids
                .iter()
                .map(|id| KeyID { key_ID: id.clone() })
                .collect(),
        };
        let container = self.dec_keys(&self.default_master_sae_id, &req).await?;
        let mut out = Vec::with_capacity(container.keys.len());
        for key in container.keys {
            let bytes = general_purpose::STANDARD
                .decode(&key.key)
                .map_err(|e| anyhow!("ETSI 014 key {} has invalid base64: {}", key.key_ID, e))?;
            out.push(QkdKey {
                key_id: key.key_ID,
                key_data: bytes,
            });
        }
        Ok(out)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Status field cardinality matches ETSI 014 v1.1.1 §5.1: 11 required
    /// fields, 1 optional `status_extension`.
    #[test]
    fn status_serializes_with_required_fields() {
        let s = Status {
            source_KME_ID: "kme-A".into(),
            target_KME_ID: "kme-B".into(),
            master_SAE_ID: "sae-master".into(),
            slave_SAE_ID: "sae-slave".into(),
            key_size: 256,
            stored_key_count: 100,
            max_key_count: 1024,
            max_key_per_request: 16,
            max_key_size: 1024,
            min_key_size: 64,
            max_SAE_ID_count: 8,
            status_extension: None,
        };
        let json = serde_json::to_value(&s).unwrap();
        // All 11 required fields present.
        for f in [
            "source_KME_ID",
            "target_KME_ID",
            "master_SAE_ID",
            "slave_SAE_ID",
            "key_size",
            "stored_key_count",
            "max_key_count",
            "max_key_per_request",
            "max_key_size",
            "min_key_size",
            "max_SAE_ID_count",
        ] {
            assert!(json.get(f).is_some(), "missing required field: {f}");
        }
        // status_extension omitted when None.
        assert!(json.get("status_extension").is_none());
    }

    #[test]
    fn enc_keys_request_omits_unset_optionals() {
        let req = EncKeysRequest {
            number: Some(2),
            size: Some(256),
            ..Default::default()
        };
        let json = serde_json::to_value(&req).unwrap();
        assert_eq!(json["number"], 2);
        assert_eq!(json["size"], 256);
        assert!(json.get("additional_slave_SAE_IDs").is_none());
        assert!(json.get("extension_mandatory").is_none());
    }

    #[test]
    fn dec_keys_request_carries_key_ids() {
        let req = DecKeysRequest {
            key_IDs: vec![
                KeyID {
                    key_ID: "uuid-1".into(),
                },
                KeyID {
                    key_ID: "uuid-2".into(),
                },
            ],
        };
        let json = serde_json::to_value(&req).unwrap();
        let arr = json["key_IDs"].as_array().unwrap();
        assert_eq!(arr.len(), 2);
        assert_eq!(arr[0]["key_ID"], "uuid-1");
        assert_eq!(arr[1]["key_ID"], "uuid-2");
    }

    #[test]
    fn key_container_round_trip() {
        let json = serde_json::json!({
            "keys": [
                { "key_ID": "uuid-1", "key": "AAAA" },
                { "key_ID": "uuid-2", "key": "BBBB", "key_extension": { "label": "test" } }
            ]
        });
        let container: KeyContainer = serde_json::from_value(json).unwrap();
        assert_eq!(container.keys.len(), 2);
        assert_eq!(container.keys[0].key_ID, "uuid-1");
        assert!(container.keys[0].key_extension.is_none());
        assert!(container.keys[1].key_extension.is_some());
    }

    #[test]
    fn etsi_error_round_trip() {
        let json = serde_json::json!({
            "message": "requested key size exceeds maximum",
            "details": { "max_key_size": 1024, "requested": 2048 }
        });
        let err: EtsiError = serde_json::from_value(json).unwrap();
        assert_eq!(err.message, "requested key size exceeds maximum");
        assert!(err.details.is_some());
    }
}
