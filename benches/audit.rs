//! Audit-trail micro-benchmarks: SLH-DSA-Shake128f signature/verification
//! cost per audit log line. Quantifies the per-event cost of T9
//! (audit-log integrity) in `docs/THREAT-MODEL.md`.

use criterion::{black_box, criterion_group, criterion_main, Criterion};
use pq_qkd_proxy::crypto::PqKeyExchange;

fn bench_slh_dsa_sign_audit_line(c: &mut Criterion) {
    let server = PqKeyExchange::new().unwrap();
    let line = b"2026-05-05T18:00:00Z key_request peer=1.2.3.4 size=32 key_id=uuid-1";
    c.bench_function("slh_dsa_sign_audit_line (SLH-DSA-Shake128f)", |b| {
        b.iter(|| {
            let sig = server.sign_hash_based(line).unwrap();
            black_box(sig);
        })
    });
}

fn bench_slh_dsa_verify_audit_line(c: &mut Criterion) {
    let server = PqKeyExchange::new().unwrap();
    let line = b"2026-05-05T18:00:00Z key_request peer=1.2.3.4 size=32 key_id=uuid-1";
    let sig = server.sign_hash_based(line).unwrap();
    let vk = server.slh_dsa_pk_bytes().to_vec();
    c.bench_function("slh_dsa_verify_audit_line (SLH-DSA-Shake128f)", |b| {
        b.iter(|| {
            let ok = PqKeyExchange::verify_slh_dsa(line, &sig, &vk).unwrap();
            black_box(ok);
        })
    });
}

criterion_group!(
    benches,
    bench_slh_dsa_sign_audit_line,
    bench_slh_dsa_verify_audit_line,
);
criterion_main!(benches);
