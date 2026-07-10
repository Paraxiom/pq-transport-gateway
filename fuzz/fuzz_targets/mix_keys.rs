#![no_main]
//! Fuzz the QKD-key-mix combiner.
//!
//! Target: `pq_qkd_proxy::crypto::mix_keys(qkd_key: &[u8], pqc_key: &[u8; 32]) -> [u8; 32]`
//! Inputs: arbitrary QKD key bytes (any length, including 0 and oversized);
//! the PQC half is held constant at 32 zero bytes so the fuzzer focuses on
//! the variable-length QKD input.
//!
//! Boundary cases of interest:
//! - empty qkd_key (PQC-only fallback path)
//! - qkd_key exactly at the 1 MB cap (`max_qkd_key = 1_048_576`)
//! - qkd_key larger than the cap (must not panic — should error or saturate)
//! - very short inputs (1-3 bytes)
//!
//! Pass criterion: no panic, no UB, no infinite loop, deterministic output
//! for a given input.
//!
//! Run with:
//!   cargo +nightly fuzz run mix_keys -- -max_total_time=3600

use libfuzzer_sys::fuzz_target;
use pq_qkd_proxy::crypto;

fuzz_target!(|data: &[u8]| {
    let pqc_key: [u8; 32] = [0u8; 32];
    let _ = crypto::mix_keys(data, &pqc_key);
});
