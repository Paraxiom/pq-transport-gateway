#![no_main]
//! Fuzz the ETSI GS QKD 014 v1.1.1 KeyContainer JSON deserializer.
//!
//! Target: `pq_qkd_proxy::qkd_client::KeyContainer`
//! Coverage: keys array (UUID `key_ID`, base64 `key`, optional extensions),
//! plus `key_container_extension`. Boundary cases of interest:
//! - empty keys array
//! - malformed UUIDs / non-UUID strings in `key_ID`
//! - malformed base64 in `key`
//! - nested / oversized extension objects
//!
//! Run with:
//!   cargo +nightly fuzz run etsi014_key_container -- -max_total_time=3600

use libfuzzer_sys::fuzz_target;
use pq_qkd_proxy::qkd_client::KeyContainer;

fuzz_target!(|data: &[u8]| {
    let _ = serde_json::from_slice::<KeyContainer>(data);
});
