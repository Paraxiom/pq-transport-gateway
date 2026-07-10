#![no_main]
//! Fuzz the ETSI GS QKD 014 v1.1.1 EtsiError JSON deserializer.
//!
//! Target: `pq_qkd_proxy::qkd_client::EtsiError`
//! Inputs: arbitrary bytes interpreted as a JSON document representing a
//! 400 / 401 / 503 structured error body (`{message, details}`).
//! Pass criterion: no panic, no memory unsafety.
//!
//! Run with:
//!   cargo +nightly fuzz run etsi014_error -- -max_total_time=3600

use libfuzzer_sys::fuzz_target;
use pq_qkd_proxy::qkd_client::EtsiError;

fuzz_target!(|data: &[u8]| {
    let _ = serde_json::from_slice::<EtsiError>(data);
});
