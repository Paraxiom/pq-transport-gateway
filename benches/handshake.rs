//! Handshake-stage micro-benchmarks for PQTG v2 (ML-KEM-768 + Falcon-512).
//!
//! Run with `cargo bench --bench handshake`. Each bench measures one
//! cryptographic stage in isolation so reviewers can see where the
//! handshake budget actually lives.
//!
//! Stages:
//!   - server identity keygen (Falcon-512 + SLH-DSA-Shake128f)
//!   - client ephemeral KEM keygen (ML-KEM-768)
//!   - server-side encapsulation (`encapsulate_to`)
//!   - client-side decapsulation
//!   - transcript hash (SHA3-256 over ~3 KB of bytes)
//!   - server transcript signature (Falcon-512)
//!   - client transcript verification (Falcon-512)
//!   - end-to-end handshake (all stages combined)

use criterion::{black_box, criterion_group, criterion_main, BatchSize, Criterion};
use pq_qkd_proxy::crypto::{
    derive_session_key, encapsulate_to, random_bytes, transcript_hash, EphemeralKemKey,
    PqKeyExchange,
};

fn bench_server_identity_keygen(c: &mut Criterion) {
    c.bench_function(
        "server_identity_keygen (Falcon-512 + SLH-DSA-Shake128f)",
        |b| {
            b.iter(|| {
                let kex = PqKeyExchange::new().unwrap();
                black_box(kex);
            })
        },
    );
}

fn bench_client_kem_keygen(c: &mut Criterion) {
    c.bench_function("client_kem_keygen (ML-KEM-768)", |b| {
        b.iter(|| {
            let kem = EphemeralKemKey::new().unwrap();
            black_box(kem);
        })
    });
}

fn bench_encapsulate(c: &mut Criterion) {
    let client_kem = EphemeralKemKey::new().unwrap();
    c.bench_function("encapsulate (ML-KEM-768)", |b| {
        b.iter(|| {
            let (ct, ss) = encapsulate_to(&client_kem.ek_bytes).unwrap();
            black_box((ct, ss));
        })
    });
}

fn bench_decapsulate(c: &mut Criterion) {
    // A valid-length ciphertext. `EphemeralKemKey` is single-use (decapsulate
    // consumes it), so each iteration gets a fresh key via `iter_batched`;
    // keygen is the untimed setup. ML-KEM decapsulation is constant-time
    // regardless of whether the ciphertext matches the per-iteration key.
    let seed_kem = EphemeralKemKey::new().unwrap();
    let (ct, _ss) = encapsulate_to(&seed_kem.ek_bytes).unwrap();
    c.bench_function("decapsulate (ML-KEM-768)", |b| {
        b.iter_batched(
            || EphemeralKemKey::new().unwrap(),
            |kem| {
                let ss = kem.decapsulate(&ct).unwrap();
                black_box(ss);
            },
            BatchSize::SmallInput,
        )
    });
}

fn bench_transcript_hash(c: &mut Criterion) {
    let server = PqKeyExchange::new().unwrap();
    let client_kem = EphemeralKemKey::new().unwrap();
    let (ct, _) = encapsulate_to(&client_kem.ek_bytes).unwrap();
    let cr = random_bytes::<32>();
    let sr = random_bytes::<32>();
    let server_pk = server.falcon_pk_bytes().to_vec();
    c.bench_function("transcript_hash (SHA3-256, ~3.2 KB)", |b| {
        b.iter(|| {
            let h = transcript_hash(&cr, &sr, &client_kem.ek_bytes, &server_pk, &ct);
            black_box(h);
        })
    });
}

fn bench_falcon_sign_transcript(c: &mut Criterion) {
    let server = PqKeyExchange::new().unwrap();
    let transcript = [0xAAu8; 32];
    c.bench_function("falcon_sign_transcript (Falcon-512)", |b| {
        b.iter(|| {
            let sig = server.sign_transcript(&transcript).unwrap();
            black_box(sig);
        })
    });
}

fn bench_falcon_verify_transcript(c: &mut Criterion) {
    let server = PqKeyExchange::new().unwrap();
    let transcript = [0xAAu8; 32];
    let sig = server.sign_transcript(&transcript).unwrap();
    let vk = server.falcon_pk_bytes().to_vec();
    c.bench_function("falcon_verify_transcript (Falcon-512)", |b| {
        b.iter(|| {
            let ok = PqKeyExchange::verify_falcon(&transcript, &sig, &vk).unwrap();
            black_box(ok);
        })
    });
}

fn bench_session_kdf(c: &mut Criterion) {
    let kem_secret = [0xAAu8; 32];
    let transcript = [0xBBu8; 32];
    c.bench_function("derive_session_key (SHA3-256)", |b| {
        b.iter(|| {
            let k = derive_session_key(&kem_secret, &transcript);
            black_box(k);
        })
    });
}

/// End-to-end: every stage of the handshake, summed. The throughput
/// reciprocal is "max handshakes/sec on this hardware."
fn bench_full_handshake(c: &mut Criterion) {
    c.bench_function("full_handshake_e2e", |b| {
        b.iter(|| {
            // Identity (would normally be persisted; included here for
            // honest worst-case timing if regenerated).
            let server = PqKeyExchange::new().unwrap();
            let client_kem = EphemeralKemKey::new().unwrap();
            let client_ek = client_kem.ek_bytes.clone();

            let cr = random_bytes::<32>();
            let sr = random_bytes::<32>();

            // Server side
            let (ct, server_ss) = encapsulate_to(&client_ek).unwrap();
            let server_transcript =
                transcript_hash(&cr, &sr, &client_ek, server.falcon_pk_bytes(), &ct);
            let sig = server.sign_transcript(&server_transcript).unwrap();
            let server_session_key = derive_session_key(&server_ss, &server_transcript);

            // Client side
            let client_ss = client_kem.decapsulate(&ct).unwrap();
            let client_transcript =
                transcript_hash(&cr, &sr, &client_ek, server.falcon_pk_bytes(), &ct);
            let ok =
                PqKeyExchange::verify_falcon(&client_transcript, &sig, server.falcon_pk_bytes())
                    .unwrap();
            let client_session_key = derive_session_key(&client_ss, &client_transcript);

            black_box((ok, server_session_key, client_session_key));
        })
    });
}

criterion_group!(
    benches,
    bench_server_identity_keygen,
    bench_client_kem_keygen,
    bench_encapsulate,
    bench_decapsulate,
    bench_transcript_hash,
    bench_falcon_sign_transcript,
    bench_falcon_verify_transcript,
    bench_session_kdf,
    bench_full_handshake
);
criterion_main!(benches);
