//! Kani harnesses (bounded model checks) for the gateway session layer
//! (wire 2.1 / 3.2): `PqSession`, `session_nonce` and `derive_direction_keys`
//! in `src/crypto.rs`.
//!
//! The code under proof is the gateway's own source, compiled verbatim:
//! `src/kdf.rs` through `#[path]`, `src/crypto.rs` through `build.rs`, which
//! wraps the unmodified file in `mod crypto` and appends the proofs
//! (`session_proofs.rs`) as a child module. What is replaced, and only for
//! these proofs:
//!
//! - AES-256-GCM, by the model in `aead-model/` (the dependency named
//!   `aes_gcm` here). The real `aead` trait code around it still runs.
//! - HMAC-SHA3-256 (`kdf::prf`), in the harnesses that say so, by a stub that
//!   XORs the key into the domain constant. The domain constants themselves
//!   are the real ones, computed by the real SHA3-256.
//!
//! Run (from this directory):
//!
//! ```text
//! cargo kani -Z stubbing
//! ```
//!
//! Results and what each proof covers: `formal/GATEWAY-SESSION-RESULTS-2026-10-15.md`.
//!
//! Status 2026-10-15 (Kani 0.67.0, macOS arm64): only
//! `a_session_nonce_is_injective` reaches a verdict (successful). The two
//! `d_*` harnesses fail on a Kani limitation (`ptr_mask` inside `LazyLock`),
//! and the `b_*` and `c_*` harnesses give no verdict within 25 minutes. Read
//! the results file before citing any of this.

#![allow(dead_code, unused_imports)]

#[path = "../../src/kdf.rs"]
pub mod kdf;

include!(concat!(env!("OUT_DIR"), "/crypto_under_proof.rs"));
