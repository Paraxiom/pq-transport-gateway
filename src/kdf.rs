//! Domain-separated hashing and a keyed key schedule (backlog B2 and B3).
//!
//! # Tree of labels (B2)
//!
//! Every hash and PRF use in the v3 gateway handshake and in the relay gets a
//! 32-byte domain constant derived from a *path* in one tree, in the manner of
//! Rosenpass's `hash_domain_ns!`:
//!
//! ```text
//! D(root)          = SHA3-256("PQTG-DOMAIN-TREE-v1")
//! D(parent / leaf) = SHA3-256(D(parent) ‖ len32(leaf) ‖ leaf)
//! ```
//!
//! Two different paths cannot share a constant without a SHA3-256 collision,
//! and every path in use is listed in [`ALL_DOMAINS`], which a test checks for
//! distinctness and whose constants are published as known-answer vectors.
//! The v2 gateway schedule (flat `pqtg-*-v2` labels) and the identity
//! fingerprint (`pqtg-identity-fingerprint-v1`) are deliberately NOT moved:
//! the KirQ Phase 1 client speaks v2, and pins must keep their values.
//!
//! # Keyed schedule (B3)
//!
//! Secrets never go through a bare hash. [`prf`] is HMAC-SHA3-256 keyed by
//! the secret, with the domain constant and length-prefixed inputs as the
//! message. [`Chain`] is a Noise-style running chaining key: start it from a
//! domain, `mix` each secret or public context in a fixed order, `finish`
//! under an output domain. Each step is a PRF of the previous key, so the
//! order of inputs is bound, and the running key is zeroized when dropped.

use hmac::{Hmac, Mac};
use sha3::{Digest, Sha3_256};
use std::sync::LazyLock;
use zeroize::{Zeroize, ZeroizeOnDrop};

type HmacSha3 = Hmac<Sha3_256>;

/// A 32-byte domain constant, see the module docs.
pub type Domain = [u8; 32];

const ROOT: &[u8] = b"PQTG-DOMAIN-TREE-v1";

/// Derive the domain constant for a path. Public so tooling (and the KAT
/// generator in another language) can reproduce every constant.
pub fn domain(path: &[&str]) -> Domain {
    let mut d = Sha3_256::digest(ROOT);
    for leaf in path {
        let mut h = Sha3_256::new();
        h.update(d);
        h.update((leaf.len() as u32).to_be_bytes());
        h.update(leaf.as_bytes());
        d = h.finalize();
    }
    let mut out = [0u8; 32];
    out.copy_from_slice(&d);
    out
}

/// Every path in use. Add here when adding a domain; the distinctness test
/// and the published vectors are driven by this list.
// The binary compiles this module privately and only the tests read the
// registry; the library exports it.
#[allow(dead_code)]
pub const ALL_DOMAINS: &[&[&str]] = &[
    &["gateway", "v3", "transcript"],
    &["gateway", "v3", "client-hello"],
    &["gateway", "v3", "chain"],
    &["gateway", "v3", "mix", "kem"],
    &["gateway", "v3", "mix", "qkd"],
    &["gateway", "v3", "mix", "transcript"],
    &["gateway", "v3", "session-key"],
    &["relay", "v4", "hello"],
    &["relay", "v4", "transcript"],
    &["relay", "v4", "key", "c2s"],
    &["relay", "v4", "key", "s2c"],
    &["relay", "v4", "ratchet"],
];

macro_rules! domains {
    ($($name:ident = [$($seg:literal),+];)+) => {
        $(pub static $name: LazyLock<Domain> = LazyLock::new(|| domain(&[$($seg),+]));)+
    };
}

domains! {
    GATEWAY_V3_TRANSCRIPT     = ["gateway", "v3", "transcript"];
    GATEWAY_V3_CLIENT_HELLO   = ["gateway", "v3", "client-hello"];
    GATEWAY_V3_CHAIN          = ["gateway", "v3", "chain"];
    GATEWAY_V3_MIX_KEM        = ["gateway", "v3", "mix", "kem"];
    GATEWAY_V3_MIX_QKD        = ["gateway", "v3", "mix", "qkd"];
    GATEWAY_V3_MIX_TRANSCRIPT = ["gateway", "v3", "mix", "transcript"];
    GATEWAY_V3_SESSION_KEY    = ["gateway", "v3", "session-key"];
    RELAY_HELLO               = ["relay", "v4", "hello"];
    RELAY_TRANSCRIPT          = ["relay", "v4", "transcript"];
    RELAY_KEY_C2S             = ["relay", "v4", "key", "c2s"];
    RELAY_KEY_S2C             = ["relay", "v4", "key", "s2c"];
    RELAY_RATCHET             = ["relay", "v4", "ratchet"];
}

/// Domain-separated hash of public data: `SHA3-256(D ‖ len32(p1) ‖ p1 ‖ …)`.
/// Every part is length-prefixed, fixed-size ones included, so the layout is
/// uniform and unambiguous.
pub fn hash(d: &Domain, parts: &[&[u8]]) -> [u8; 32] {
    let mut h = Sha3_256::new();
    h.update(d);
    for p in parts {
        h.update((p.len() as u32).to_be_bytes());
        h.update(p);
    }
    let mut out = [0u8; 32];
    out.copy_from_slice(&h.finalize());
    out
}

/// Keyed derivation: `HMAC-SHA3-256(key, D ‖ len32(p1) ‖ p1 ‖ …)`.
pub fn prf(key: &[u8; 32], d: &Domain, parts: &[&[u8]]) -> [u8; 32] {
    let mut mac = HmacSha3::new_from_slice(key).expect("HMAC accepts any key length");
    mac.update(d);
    for p in parts {
        mac.update(&(p.len() as u32).to_be_bytes());
        mac.update(p);
    }
    let mut out = [0u8; 32];
    out.copy_from_slice(&mac.finalize().into_bytes());
    out
}

/// A running chaining key. Consumed by each step so a chain cannot be forked
/// or reused by accident; zeroized on drop.
#[derive(ZeroizeOnDrop)]
pub struct Chain([u8; 32]);

impl Chain {
    /// `ck0 = SHA3-256(D)`: the chain's starting point is the domain itself.
    pub fn start(d: &Domain) -> Self {
        Self(hash(d, &[]))
    }

    /// `ck' = PRF(ck, D_step ‖ len32(input) ‖ input)`. Order matters: mixing
    /// the same inputs in another order yields another key.
    pub fn mix(self, d: &Domain, input: &[u8]) -> Self {
        let next = prf(&self.0, d, &[input]);
        drop(self);
        Self(next)
    }

    /// `out = PRF(ck, D_out)`. Consumes the chain.
    pub fn finish(self, d: &Domain) -> [u8; 32] {
        let mut out = prf(&self.0, d, &[]);
        drop(self);
        let result = out;
        out.zeroize();
        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashSet;

    #[test]
    fn every_listed_domain_is_distinct_and_stable() {
        let set: HashSet<Domain> = ALL_DOMAINS.iter().map(|p| domain(p)).collect();
        assert_eq!(set.len(), ALL_DOMAINS.len(), "two paths share a constant");
        // The statics agree with the registry.
        assert_eq!(
            *GATEWAY_V3_TRANSCRIPT,
            domain(&["gateway", "v3", "transcript"])
        );
        assert_eq!(*RELAY_RATCHET, domain(&["relay", "v4", "ratchet"]));
        // Deterministic.
        assert_eq!(domain(&["a", "b"]), domain(&["a", "b"]));
    }

    #[test]
    fn the_tree_is_a_tree_not_a_concatenation() {
        // Boundaries between path segments are bound by the length prefix, so
        // "ab" and "a","b" and "a/b" are three different leaves.
        assert_ne!(domain(&["ab"]), domain(&["a", "b"]));
        assert_ne!(domain(&["a/b"]), domain(&["a", "b"]));
        assert_ne!(domain(&["a", "b"]), domain(&["b", "a"]));
        assert_ne!(domain(&[]), domain(&[""]));
    }

    #[test]
    fn hash_and_prf_bind_domain_key_and_part_boundaries() {
        let d1 = domain(&["x"]);
        let d2 = domain(&["y"]);
        assert_ne!(hash(&d1, &[b"m"]), hash(&d2, &[b"m"]));
        assert_ne!(hash(&d1, &[b"ab", b""]), hash(&d1, &[b"a", b"b"]));
        let k1 = [1u8; 32];
        let k2 = [2u8; 32];
        assert_ne!(prf(&k1, &d1, &[b"m"]), prf(&k2, &d1, &[b"m"]));
        assert_ne!(prf(&k1, &d1, &[b"m"]), prf(&k1, &d2, &[b"m"]));
        assert_ne!(prf(&k1, &d1, &[b"ab", b""]), prf(&k1, &d1, &[b"a", b"b"]));
        assert_ne!(
            prf(&k1, &d1, &[b"m"]),
            hash(&d1, &[b"m"]),
            "keyed and unkeyed never coincide"
        );
    }

    #[test]
    fn a_chain_binds_the_order_and_the_count_of_its_inputs() {
        let d = domain(&["t"]);
        let s1 = [3u8; 32];
        let s2 = [4u8; 32];
        let ab = Chain::start(&d).mix(&d, &s1).mix(&d, &s2).finish(&d);
        let ba = Chain::start(&d).mix(&d, &s2).mix(&d, &s1).finish(&d);
        let a = Chain::start(&d).mix(&d, &s1).finish(&d);
        assert_ne!(ab, ba);
        assert_ne!(ab, a);
        assert_eq!(
            ab,
            Chain::start(&d).mix(&d, &s1).mix(&d, &s2).finish(&d),
            "deterministic"
        );
    }
}
