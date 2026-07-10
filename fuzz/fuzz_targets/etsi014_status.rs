#![no_main]
//! Fuzz the ETSI GS QKD 014 v1.1.1 Status JSON deserializer.
//!
//! Target: `pq_qkd_proxy::qkd_client::Status`
//! Inputs: arbitrary bytes interpreted as a JSON document.
//! Pass criterion: no panic, no memory unsafety, no infinite loop.
//!
//! Run with:
//!   cargo +nightly fuzz run etsi014_status -- -max_total_time=3600

use libfuzzer_sys::fuzz_target;
use pq_qkd_proxy::qkd_client::Status;

fuzz_target!(|data: &[u8]| {
    let _ = serde_json::from_slice::<Status>(data);
});
