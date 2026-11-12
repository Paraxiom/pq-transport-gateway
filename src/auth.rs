//! Authentication and authorization

use crate::config::{Config, WIRE_2_1, WIRE_3_2};
use crate::crypto::HandshakeVersion;
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
    /// The one wire version this key may speak: 3.2, unless its line carries
    /// `wire=2.1`. A key never opens both doors: a key request signed in a
    /// 3.2 session would otherwise be accepted again in a 2.1 session, whose
    /// hello anyone can send in this client's name.
    pub wire: HandshakeVersion,
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

    /// Number of authorized keys registered for this wire version.
    pub fn count_for_wire(&self, wire: HandshakeVersion) -> usize {
        self.authorized_keys
            .values()
            .filter(|k| k.wire == wire)
            .count()
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

            // Parse line: algorithm key_data [perm=a,b] [wire=2.1] comment
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

            // Options, in either order, then the comment. A line whose
            // options cannot be read is dropped, like any other malformed
            // line: the key is then not authorized at all, which fails
            // closed. In particular a mistyped `wire=` never turns into the
            // default.
            let options = match parse_options(&parts[2..]) {
                Ok(o) => o,
                Err(e) => {
                    warn!("Invalid authorized_keys line {}: {}", line_no + 1, e);
                    continue;
                }
            };
            let permissions = options
                .permissions
                .unwrap_or_else(|| vec!["read".to_string()]);
            let wire = options.wire.unwrap_or(HandshakeVersion::V3);
            let comment = parts[2 + options.consumed..].join(" ");

            let key_id = format!("key-{line_no}");

            keys.insert(
                key_id.clone(),
                AuthorizedKey {
                    key_id,
                    falcon_public_key: falcon_pk,
                    sphincs_public_key: sphincs_pk,
                    permissions,
                    comment,
                    wire,
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

/// The options of an `authorized_keys` line: what follows the key and comes
/// before the comment.
struct LineOptions {
    permissions: Option<Vec<String>>,
    wire: Option<HandshakeVersion>,
    /// How many tokens were options; the comment starts after them.
    consumed: usize,
}

/// Read `perm=a,b` and `wire=2.1` (or `wire=3.2`) from the start of `tokens`,
/// in either order, each at most once. The first token that is neither ends
/// the options.
fn parse_options(tokens: &[&str]) -> Result<LineOptions> {
    let mut options = LineOptions {
        permissions: None,
        wire: None,
        consumed: 0,
    };
    for token in tokens {
        if let Some(list) = token.strip_prefix("perm=") {
            if options.permissions.is_some() {
                return Err(anyhow!("perm= given twice"));
            }
            options.permissions = Some(list.split(',').map(|s| s.to_string()).collect());
        } else if let Some(version) = token.strip_prefix("wire=") {
            if options.wire.is_some() {
                return Err(anyhow!("wire= given twice"));
            }
            options.wire = Some(match version {
                WIRE_2_1 => HandshakeVersion::V2,
                WIRE_3_2 => HandshakeVersion::V3,
                other => {
                    return Err(anyhow!(
                        "wire={other} is not a wire version (use wire={WIRE_2_1}, or no option \
                         for {WIRE_3_2})"
                    ))
                }
            });
        } else {
            break;
        }
        options.consumed += 1;
    }
    Ok(options)
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
            wire: HandshakeVersion::V3,
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

    // ---- the wire version of a key (`wire=`) --------------------------------

    /// A key of the right length whose bytes are all `tag`, as the base64 an
    /// `authorized_keys` line carries. The loader checks lengths only.
    fn line_key(tag: u8) -> String {
        let mut vks = vec![tag; 897];
        vks.extend_from_slice(&[tag; 32]);
        general_purpose::STANDARD.encode(vks)
    }

    /// Load an `authorized_keys` file with this content.
    fn load(content: &str) -> HashMap<String, AuthorizedKey> {
        use std::sync::atomic::{AtomicUsize, Ordering};
        static NEXT: AtomicUsize = AtomicUsize::new(0);
        let path = std::env::temp_dir().join(format!(
            "pqtg-authorized-keys-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        std::fs::write(&path, content).unwrap();
        let keys = Authenticator::load_authorized_keys(&path.to_string_lossy()).unwrap();
        let _ = std::fs::remove_file(&path);
        keys
    }

    /// The key loaded from the line whose key bytes are `tag`, if that line
    /// was accepted.
    fn loaded(keys: &HashMap<String, AuthorizedKey>, tag: u8) -> Option<&AuthorizedKey> {
        keys.values().find(|k| k.falcon_public_key[0] == tag)
    }

    const ALG: &str = "falcon512+slh-dsa-shake128f";

    /// Every line written before the option existed is a 3.2 key. No existing
    /// file gives a client wire 2.1.
    #[test]
    fn a_line_without_the_option_is_a_wire_3_2_key() {
        let keys = load(&format!(
            "{ALG} {} perm=read,write alice@example.com\n\
             {ALG} {} bob with a comment\n",
            line_key(1),
            line_key(2),
        ));
        assert_eq!(keys.len(), 2);
        let alice = loaded(&keys, 1).unwrap();
        assert_eq!(alice.wire, HandshakeVersion::V3);
        assert_eq!(alice.permissions, vec!["read", "write"]);
        assert_eq!(alice.comment, "alice@example.com");
        let bob = loaded(&keys, 2).unwrap();
        assert_eq!(bob.wire, HandshakeVersion::V3);
        assert_eq!(bob.permissions, vec!["read"]);
        assert_eq!(bob.comment, "bob with a comment");
    }

    #[test]
    fn wire_2_1_is_read_from_the_line_before_or_after_perm() {
        let keys = load(&format!(
            "{ALG} {} perm=read wire=2.1 legacy client one\n\
             {ALG} {} wire=2.1 perm=read,write legacy client two\n\
             {ALG} {} wire=2.1\n\
             {ALG} {} wire=3.2 said in full\n",
            line_key(1),
            line_key(2),
            line_key(3),
            line_key(4),
        ));
        assert_eq!(keys.len(), 4);
        let one = loaded(&keys, 1).unwrap();
        assert_eq!(one.wire, HandshakeVersion::V2);
        assert_eq!(one.permissions, vec!["read"]);
        assert_eq!(one.comment, "legacy client one");
        let two = loaded(&keys, 2).unwrap();
        assert_eq!(two.wire, HandshakeVersion::V2);
        assert_eq!(two.permissions, vec!["read", "write"]);
        assert_eq!(two.comment, "legacy client two");
        let three = loaded(&keys, 3).unwrap();
        assert_eq!(three.wire, HandshakeVersion::V2);
        assert_eq!(three.permissions, vec!["read"]);
        assert_eq!(three.comment, "");
        let four = loaded(&keys, 4).unwrap();
        assert_eq!(four.wire, HandshakeVersion::V3);
        assert_eq!(four.comment, "said in full");

        let auth = Authenticator {
            authorized_keys: keys,
        };
        assert_eq!(auth.count_for_wire(HandshakeVersion::V2), 3);
        assert_eq!(auth.count_for_wire(HandshakeVersion::V3), 1);
    }

    /// A `wire=` the loader cannot read drops the line: the key is then not
    /// authorized at all. It must never become a 3.2 key by default, nor a
    /// 2.1 key by resemblance.
    #[test]
    fn a_line_with_an_unreadable_option_authorizes_nobody() {
        for option in [
            "wire=2.0",
            "wire=3.1",
            "wire=2",
            "wire=",
            "wire=2.1,3.2",
            "wire=2.1 wire=2.1",
            "wire=2.1 wire=3.2",
            "perm=read perm=write",
        ] {
            let keys = load(&format!(
                "{ALG} {} {option} someone\n{ALG} {} perm=read the next line still loads\n",
                line_key(1),
                line_key(2),
            ));
            assert!(loaded(&keys, 1).is_none(), "{option}: the line must drop");
            assert!(loaded(&keys, 2).is_some(), "{option}: the next line loads");
        }
    }

    /// Once the comment has begun, nothing in it is an option.
    #[test]
    fn an_option_written_inside_the_comment_is_a_comment() {
        let keys = load(&format!(
            "{ALG} {} perm=read moved off wire=2.1 on 2026-11-12\n",
            line_key(1),
        ));
        let key = loaded(&keys, 1).unwrap();
        assert_eq!(key.wire, HandshakeVersion::V3);
        assert_eq!(key.comment, "moved off wire=2.1 on 2026-11-12");
    }
}
