//! Authentication and authorization

use crate::config::Config;
use anyhow::{anyhow, Result};
use base64::{engine::general_purpose, Engine as _};
use std::collections::HashMap;
use std::path::Path;
use tracing::{info, warn};

/// Authenticator for client connections
#[allow(dead_code)] // `from_keys`, `authorized_count`, `check_permission` are
                    // public API surface used by tests and future
                    // programmatic-config callers.
pub struct Authenticator {
    authorized_keys: HashMap<String, AuthorizedKey>,
}

#[derive(Clone, Debug)]
#[allow(dead_code)] // permissions + comment are surfaced to users via
                    // logging and future per-method authz (issue #8 §4)
pub struct AuthorizedKey {
    pub key_id: String,
    pub falcon_public_key: Vec<u8>,
    pub sphincs_public_key: Vec<u8>,
    pub permissions: Vec<String>,
    pub comment: String,
}

impl Authenticator {
    pub fn new(config: &Config) -> Result<Self> {
        let authorized_keys = Self::load_authorized_keys(&config.security.authorized_keys)?;

        info!("Loaded {} authorized keys", authorized_keys.len());

        Ok(Self { authorized_keys })
    }

    /// Construct an Authenticator from an explicit list of keys, bypassing
    /// file I/O. Used by tests and by future programmatic-config callers.
    #[allow(dead_code)] // public test helper / programmatic-config API
    pub fn from_keys(keys: Vec<AuthorizedKey>) -> Self {
        let map = keys.into_iter().map(|k| (k.key_id.clone(), k)).collect();
        Self {
            authorized_keys: map,
        }
    }

    /// Number of currently-authorized keys. Used by audit/logging.
    #[allow(dead_code)] // surfaced via future audit-log enrichment
    pub fn authorized_count(&self) -> usize {
        self.authorized_keys.len()
    }

    fn load_authorized_keys(path: &str) -> Result<HashMap<String, AuthorizedKey>> {
        let mut keys = HashMap::new();

        if !Path::new(path).exists() {
            warn!("Authorized keys file not found: {}", path);
            return Ok(keys);
        }

        let content = std::fs::read_to_string(path)?;

        for (line_no, line) in content.lines().enumerate() {
            let line = line.trim();

            // Skip empty lines and comments
            if line.is_empty() || line.starts_with('#') {
                continue;
            }

            // Parse line: algorithm key_data permissions comment
            let parts: Vec<&str> = line.split_whitespace().collect();
            if parts.len() < 3 {
                warn!(
                    "Invalid authorized_keys line {}: too few fields",
                    line_no + 1
                );
                continue;
            }

            let algorithm = parts[0];
            if algorithm != "falcon512+slh-dsa-shake128f" && algorithm != "falcon512+sphincs+" {
                warn!(
                    "Unsupported algorithm on line {}: {}",
                    line_no + 1,
                    algorithm
                );
                continue;
            }

            // Parse base64 encoded keys
            let key_data = parts[1];
            let decoded = match general_purpose::STANDARD.decode(key_data) {
                Ok(d) => d,
                Err(e) => {
                    warn!("Invalid base64 on line {}: {}", line_no + 1, e);
                    continue;
                }
            };

            // Expected format: falcon_vk(897) || slh_dsa_shake128f_vk(32)
            // Falcon-512 verification key = 897 bytes
            // SLH-DSA-Shake128f verification key = 32 bytes (PK_seed ‖ PK_root, each 16 bytes)
            const FALCON_VK_LEN: usize = 897;
            const SLH_DSA_VK_LEN: usize = 32;
            if decoded.len() < FALCON_VK_LEN + SLH_DSA_VK_LEN {
                warn!("Invalid key length on line {}", line_no + 1);
                continue;
            }

            let falcon_pk = decoded[..FALCON_VK_LEN].to_vec();
            let sphincs_pk = decoded[FALCON_VK_LEN..FALCON_VK_LEN + SLH_DSA_VK_LEN].to_vec();

            // Parse permissions
            let permissions = if parts.len() > 2 && parts[2].starts_with("perm=") {
                parts[2][5..].split(',').map(|s| s.to_string()).collect()
            } else {
                vec!["read".to_string()]
            };

            // Rest is comment
            let comment = if parts.len() > 3 {
                parts[3..].join(" ")
            } else {
                String::new()
            };

            let key_id = format!("key-{}", line_no);

            keys.insert(
                key_id.clone(),
                AuthorizedKey {
                    key_id,
                    falcon_public_key: falcon_pk,
                    sphincs_public_key: sphincs_pk,
                    permissions,
                    comment,
                },
            );
        }

        Ok(keys)
    }

    pub fn verify_client(&self, falcon_pk: &[u8], sphincs_pk: &[u8]) -> Result<&AuthorizedKey> {
        for auth_key in self.authorized_keys.values() {
            if auth_key.falcon_public_key == falcon_pk && auth_key.sphincs_public_key == sphincs_pk
            {
                return Ok(auth_key);
            }
        }
        Err(anyhow!("Unauthorized client key"))
    }

    /// Check whether an `AuthorizedKey` has a given permission. Currently
    /// used only by tests; the proxy's per-method authz lives in issue
    /// #8 §4 (RFC for the generalized PQ reverse proxy).
    #[allow(dead_code)]
    pub fn check_permission(&self, auth_key: &AuthorizedKey, permission: &str) -> bool {
        auth_key.permissions.contains(&permission.to_string())
            || auth_key.permissions.contains(&"*".to_string())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn key(name: &str, falcon: Vec<u8>, slh: Vec<u8>, perms: Vec<&str>) -> AuthorizedKey {
        AuthorizedKey {
            key_id: name.to_string(),
            falcon_public_key: falcon,
            sphincs_public_key: slh,
            permissions: perms.into_iter().map(String::from).collect(),
            comment: String::new(),
        }
    }

    #[test]
    fn empty_authenticator_rejects_everyone() {
        let auth = Authenticator::from_keys(vec![]);
        let err = auth.verify_client(&[1u8; 897], &[2u8; 32]).unwrap_err();
        assert!(err.to_string().contains("Unauthorized"));
    }

    #[test]
    fn authorized_client_accepted() {
        let f = vec![0xAAu8; 897];
        let s = vec![0xBBu8; 32];
        let auth =
            Authenticator::from_keys(vec![key("client-1", f.clone(), s.clone(), vec!["read"])]);
        let ok = auth.verify_client(&f, &s).expect("should be authorized");
        assert_eq!(ok.key_id, "client-1");
    }

    #[test]
    fn unauthorized_client_rejected() {
        let f = vec![0xAAu8; 897];
        let s = vec![0xBBu8; 32];
        let auth = Authenticator::from_keys(vec![key("client-1", f, s, vec!["read"])]);
        // Different keys → unauthorized.
        let err = auth
            .verify_client(&[0xCCu8; 897], &[0xDDu8; 32])
            .unwrap_err();
        assert!(err.to_string().contains("Unauthorized"));
    }

    /// Falcon match but SLH-DSA mismatch is a rejection (both must align).
    #[test]
    fn partial_match_rejected() {
        let f = vec![0xAAu8; 897];
        let s = vec![0xBBu8; 32];
        let auth = Authenticator::from_keys(vec![key("client-1", f.clone(), s, vec!["read"])]);
        let err = auth.verify_client(&f, &[0xEEu8; 32]).unwrap_err();
        assert!(err.to_string().contains("Unauthorized"));
    }

    #[test]
    fn permission_check_respects_wildcard() {
        let auth =
            Authenticator::from_keys(vec![key("admin", vec![1u8; 897], vec![2u8; 32], vec!["*"])]);
        let key_ref = auth.verify_client(&[1u8; 897], &[2u8; 32]).unwrap();
        assert!(auth.check_permission(key_ref, "read"));
        assert!(auth.check_permission(key_ref, "write"));
        assert!(auth.check_permission(key_ref, "admin"));
    }

    #[test]
    fn permission_check_specific_only() {
        let auth = Authenticator::from_keys(vec![key(
            "reader",
            vec![1u8; 897],
            vec![2u8; 32],
            vec!["read"],
        )]);
        let key_ref = auth.verify_client(&[1u8; 897], &[2u8; 32]).unwrap();
        assert!(auth.check_permission(key_ref, "read"));
        assert!(!auth.check_permission(key_ref, "write"));
    }

    /// Two clients in the same Authenticator: each authorized only for itself.
    #[test]
    fn multi_client_isolation() {
        let f1 = vec![0xA1u8; 897];
        let s1 = vec![0xB1u8; 32];
        let f2 = vec![0xA2u8; 897];
        let s2 = vec![0xB2u8; 32];
        let auth = Authenticator::from_keys(vec![
            key("alice", f1.clone(), s1.clone(), vec!["read"]),
            key("bob", f2.clone(), s2.clone(), vec!["write"]),
        ]);
        assert_eq!(auth.verify_client(&f1, &s1).unwrap().key_id, "alice");
        assert_eq!(auth.verify_client(&f2, &s2).unwrap().key_id, "bob");
        // Cross-pairs are unauthorized — even though both keys are independently valid.
        assert!(auth.verify_client(&f1, &s2).is_err());
        assert!(auth.verify_client(&f2, &s1).is_err());
    }
}
