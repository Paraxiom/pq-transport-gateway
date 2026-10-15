// Kani harnesses for the gateway session layer. This file is included by
// build.rs as `crypto::session_proofs`, a child of the unmodified
// src/crypto.rs, so it reads PqSession's private counters the way the unit
// tests in that file do.
//
// Stubs and models, all of them:
// - AES-256-GCM: the oracle/ideal model of aead-model/ (see its docs). The
//   real `aead` 0.5 blanket `Aead` impl and default in-place methods run.
// - HMAC-SHA3-256 (`kdf::prf`): replaced by `prf_xor` in the harnesses marked
//   `#[kani::stub(crate::kdf::prf, prf_xor)]`. The domain constants are the
//   real SHA3-256 values.
// - Falcon-512 verification (`PqKeyExchange::verify_falcon`): replaced by an
//   arbitrary outcome in `c_open_and_verify_*` only.
// - `std::backtrace::Backtrace::capture`: replaced by `Backtrace::disabled()`
//   everywhere, because anyhow asks for one on every error and the real one
//   reads the environment and walks the stack.
// - `anyhow::__private::format_err` (what `anyhow!("literal")` calls):
//   replaced by an error with a fixed message, so the formatting machinery
//   is not encoded. No proof reads an error's text; only Ok versus Err.

use super::*;
use aes_gcm::oracle;
use aes_gcm::{Aes256Gcm, Key, KeyInit};

fn no_backtrace() -> std::backtrace::Backtrace {
    std::backtrace::Backtrace::disabled()
}

fn error_message(_args: core::fmt::Arguments<'_>) -> anyhow::Error {
    anyhow::Error::msg("error (text elided in the proofs)")
}

/// Stand-in for HMAC-SHA3-256 in the role-mapping proofs: the key XORed into
/// the domain constant. Injective in the domain for a fixed key, so two
/// different domains give two different keys under this stub. For the real
/// HMAC that is the PRF assumption, not something proved here.
fn prf_xor(key: &[u8; 32], d: &crate::kdf::Domain, parts: &[&[u8]]) -> [u8; 32] {
    assert!(parts.is_empty(), "the direction keys take no further input");
    let mut out = *d;
    let mut i = 0;
    while i < 32 {
        out[i] ^= key[i];
        i += 1;
    }
    out
}

/// Arbitrary outcome of Falcon-512 verification, error included.
fn verify_falcon_any(_msg: &[u8], _sig: &[u8], _vk: &[u8]) -> Result<bool> {
    if kani::any() {
        Ok(kani::any())
    } else {
        Err(anyhow!("stubbed verification error"))
    }
}

/// One end of a session in an arbitrary state, built field by field (the
/// constructor is covered by the role-mapping proofs).
fn end_in_state(
    role: Role,
    send_key: [u8; 32],
    recv_key: [u8; 32],
    send_counter: u64,
    recv_counter: u64,
) -> PqSession {
    PqSession {
        send: Aes256Gcm::new(Key::<Aes256Gcm>::from_slice(&send_key)),
        recv: Aes256Gcm::new(Key::<Aes256Gcm>::from_slice(&recv_key)),
        role,
        session_id: [0u8; 32],
        send_counter,
        recv_counter,
        remote_falcon_pk: Vec::new(),
    }
}

fn any_role() -> Role {
    if kani::any() {
        Role::Client
    } else {
        Role::Server
    }
}

// ── (a) session_nonce is injective ──────────────────────────────────────────

/// For every pair of u64 counters: equal nonces iff equal counters. Also the
/// layout: four zero bytes, then the counter big-endian (a left inverse).
#[kani::proof]
fn a_session_nonce_is_injective() {
    let a: u64 = kani::any();
    let b: u64 = kani::any();
    let na = session_nonce(a);
    let nb = session_nonce(b);
    assert!(na[..4] == [0u8; 4]);
    let mut tail = [0u8; 8];
    tail.copy_from_slice(&na[4..]);
    assert!(u64::from_be_bytes(tail) == a);
    assert!((na == nb) == (a == b));
}

// ── (b) sealing ─────────────────────────────────────────────────────────────

/// One `encrypt` from any state, any role, any key pair, any AEAD outcome and
/// any plaintext up to 3 bytes:
/// - at send_counter = u64::MAX it returns an error and the AEAD is never
///   called (nothing is sealed) and the counter stays;
/// - otherwise the AEAD is called exactly once, with this end's sending key
///   and session_nonce(send_counter); on success the returned nonce is that
///   nonce, the ciphertext is plaintext plus a 16-byte tag, and the counter
///   moves by exactly one; on failure the counter stays;
/// - the receive counter never moves.
/// With (a), this is the inductive step for any run: successful seals use
/// strictly increasing counters, hence distinct nonces.
#[kani::proof]
#[kani::unwind(34)]
#[kani::stub(std::backtrace::Backtrace::capture, no_backtrace)]
#[kani::stub(::anyhow::__private::format_err, error_message)]
fn b_one_seal_from_any_state() {
    oracle::reset();
    let send_key: [u8; 32] = kani::any();
    let recv_key: [u8; 32] = kani::any();
    let c: u64 = kani::any();
    let r: u64 = kani::any();
    let mut s = end_in_state(any_role(), send_key, recv_key, c, r);
    let seal_ok: bool = kani::any();
    unsafe { oracle::SEAL_OK = seal_ok };
    let pt: [u8; 3] = kani::any();
    let len: usize = kani::any();
    kani::assume(len <= 3);

    let res = s.encrypt(&pt[..len]);

    let calls = unsafe { oracle::SEAL_CALLS };
    assert!(s.recv_counter == r);
    if c == u64::MAX {
        assert!(res.is_err());
        assert!(calls == 0);
        assert!(s.send_counter == u64::MAX);
    } else {
        assert!(calls == 1);
        assert!(unsafe { oracle::SEAL_KEY[0] } == send_key);
        assert!(unsafe { oracle::SEAL_NONCE[0] } == session_nonce(c));
        match res {
            Ok((ct, nonce)) => {
                assert!(seal_ok);
                assert!(nonce == session_nonce(c));
                assert!(ct.len() == len + 16);
                assert!(s.send_counter == c + 1);
            }
            Err(_) => {
                assert!(!seal_ok);
                assert!(s.send_counter == c);
            }
        }
    }
}

/// Four `encrypt` calls in a row from any starting counter (u64::MAX - 3 ..
/// u64::MAX included), each with any AEAD outcome: the nonces of the frames
/// actually produced are pairwise distinct, each equals the nonce the AEAD
/// was called with, and the counter moved by exactly the number of frames
/// produced.
#[kani::proof]
#[kani::unwind(6)]
#[kani::stub(std::backtrace::Backtrace::capture, no_backtrace)]
#[kani::stub(::anyhow::__private::format_err, error_message)]
fn b_no_nonce_repeats_in_a_run_of_seals() {
    oracle::reset();
    let c0: u64 = kani::any();
    let mut s = end_in_state(Role::Client, [1; 32], [2; 32], c0, 0);
    let mut produced = [[0u8; 12]; 4];
    let mut count = 0usize;
    let mut i = 0;
    while i < 4 {
        unsafe { oracle::SEAL_OK = kani::any() };
        let calls_before = unsafe { oracle::SEAL_CALLS };
        if let Ok((_, nonce)) = s.encrypt(&[i as u8]) {
            assert!(unsafe { oracle::SEAL_NONCE[calls_before] } == nonce);
            produced[count] = nonce;
            count += 1;
        }
        i += 1;
    }
    let mut x = 0;
    while x < count {
        let mut y = x + 1;
        while y < count {
            assert!(produced[x] != produced[y]);
            y += 1;
        }
        x += 1;
    }
    assert!(s.send_counter - c0 == count as u64);
}

// ── (c) opening ─────────────────────────────────────────────────────────────

/// One `decrypt` from any state with any nonce, any frame up to 20 bytes and
/// any AEAD outcome (a failed tag included):
/// - a nonce other than session_nonce(recv_counter), or a receive counter at
///   u64::MAX, is refused and the AEAD is never called;
/// - when the AEAD is called, it is called once, with this end's receiving
///   key, the expected nonce and the frame minus its tag;
/// - Ok only if the nonce was the expected one, the counter was below
///   u64::MAX, the frame held a tag, and the AEAD accepted; then the receive
///   counter moved by exactly one;
/// - on any refusal the receive counter is where it was;
/// - the send counter never moves.
#[kani::proof]
#[kani::unwind(22)]
#[kani::stub(std::backtrace::Backtrace::capture, no_backtrace)]
#[kani::stub(::anyhow::__private::format_err, error_message)]
fn c_open_accepts_only_the_expected_nonce_and_moves_only_on_success() {
    oracle::reset();
    let send_key: [u8; 32] = kani::any();
    let recv_key: [u8; 32] = kani::any();
    let c: u64 = kani::any();
    let r: u64 = kani::any();
    let mut s = end_in_state(any_role(), send_key, recv_key, c, r);
    let open_ok: bool = kani::any();
    unsafe { oracle::OPEN_OK = open_ok };
    let nonce: [u8; 12] = kani::any();
    let frame: [u8; 20] = kani::any();
    let len: usize = kani::any();
    kani::assume(len <= 20);

    let res = s.decrypt(&frame[..len], &nonce);

    let calls = unsafe { oracle::OPEN_CALLS };
    let expected = session_nonce(r);
    assert!(s.send_counter == c);
    match &res {
        Ok(pt) => {
            assert!(nonce == expected);
            assert!(r < u64::MAX);
            assert!(len >= 16);
            assert!(open_ok);
            assert!(pt.len() + 16 == len);
            assert!(s.recv_counter == r + 1);
        }
        Err(_) => assert!(s.recv_counter == r),
    }
    if nonce != expected || r == u64::MAX {
        assert!(res.is_err());
        assert!(calls == 0);
    }
    if calls > 0 {
        assert!(calls == 1);
        assert!(unsafe { oracle::OPEN_KEY } == recv_key);
        assert!(unsafe { oracle::OPEN_NONCE } == expected);
        assert!(unsafe { oracle::OPEN_LEN } + 16 == len);
    }
    if nonce == expected && r < u64::MAX && len >= 16 {
        assert!(calls == 1);
        assert!(res.is_ok() == open_ok);
    }
}

/// `decrypt_and_verify` (what the gateway runs on every request) on any
/// frame up to 40 bytes, from any state, with any AEAD outcome and any
/// Falcon outcome: it never panics; a frame refused by the record layer
/// leaves the receive counter where it was; Ok only when the record layer
/// accepted at the expected nonce and the inner signature verified, and then
/// the counter moved by exactly one. The one way to get Err with the counter
/// moved is a frame the AEAD accepted, i.e. one sealed under this end's
/// receiving key, which only the peer holds; the gateway ends the connection
/// on any Err.
#[kani::proof]
#[kani::unwind(42)]
#[kani::stub(std::backtrace::Backtrace::capture, no_backtrace)]
#[kani::stub(::anyhow::__private::format_err, error_message)]
#[kani::stub(PqKeyExchange::verify_falcon, verify_falcon_any)]
fn c_open_and_verify_never_panics_and_moves_only_on_an_authenticated_frame() {
    oracle::reset();
    let c: u64 = kani::any();
    let r: u64 = kani::any();
    let mut s = end_in_state(any_role(), [1; 32], [2; 32], c, r);
    let open_ok: bool = kani::any();
    unsafe { oracle::OPEN_OK = open_ok };
    let frame: [u8; 40] = kani::any();
    let len: usize = kani::any();
    kani::assume(len <= 40);

    let res = s.decrypt_and_verify(&frame[..len]);

    let calls = unsafe { oracle::OPEN_CALLS };
    assert!(s.send_counter == c);
    let mut nonce = [0u8; 12];
    if len >= 12 {
        nonce.copy_from_slice(&frame[..12]);
    }
    let authenticated =
        len >= 12 + 16 && nonce == session_nonce(r) && r < u64::MAX && open_ok && calls == 1;
    if authenticated {
        assert!(s.recv_counter == r + 1);
    } else {
        assert!(res.is_err());
        assert!(s.recv_counter == r);
    }
    if res.is_ok() {
        assert!(authenticated);
    }
}

// ── (d) role mapping and direction labels ───────────────────────────────────

/// For any session key and either handshake version, the two ends built by
/// `PqSession::new` (the real constructor and `derive_direction_keys`, with
/// HMAC-SHA3-256 replaced by `prf_xor`):
/// - the client seals with the key the server opens with, PRF(k, D[c2s]);
/// - the server seals with the key the client opens with, PRF(k, D[s2c]);
/// - the roles are recorded as given;
/// - the c2s and s2c domain constants of that version differ (the real
///   SHA3-256 constants), and so, under the stub, do the two keys, so no end
///   ever opens with the key it seals with.
/// That the real HMAC-SHA3-256 also gives two different keys for two
/// different domains is the PRF assumption, not proved here.
#[kani::proof]
#[kani::unwind(33)]
#[kani::stub(crate::kdf::prf, prf_xor)]
#[kani::stub(std::backtrace::Backtrace::capture, no_backtrace)]
#[kani::stub(::anyhow::__private::format_err, error_message)]
fn d_roles_map_the_direction_keys() {
    oracle::reset();
    let k: [u8; 32] = kani::any();
    let v2: bool = kani::any();
    let version = if v2 {
        HandshakeVersion::V2
    } else {
        HandshakeVersion::V3
    };
    let vk = vec![0u8; FALCON_512_VK_LEN];
    let client = PqSession::new(&k, version, Role::Client, [0u8; 32], vk.clone()).unwrap();
    let server = PqSession::new(&k, version, Role::Server, [0u8; 32], vk).unwrap();

    let (d_c2s, d_s2c) = if v2 {
        (
            *crate::kdf::GATEWAY_V2_KEY_C2S,
            *crate::kdf::GATEWAY_V2_KEY_S2C,
        )
    } else {
        (
            *crate::kdf::GATEWAY_V3_KEY_C2S,
            *crate::kdf::GATEWAY_V3_KEY_S2C,
        )
    };
    assert!(d_c2s != d_s2c);
    let k_c2s = prf_xor(&k, &d_c2s, &[]);
    let k_s2c = prf_xor(&k, &d_s2c, &[]);

    assert!(client.role() == Role::Client);
    assert!(server.role() == Role::Server);
    assert!(client.send.key == k_c2s);
    assert!(server.recv.key == k_c2s);
    assert!(server.send.key == k_s2c);
    assert!(client.recv.key == k_s2c);
    assert!(client.send.key != client.recv.key);
    assert!(server.send.key != server.recv.key);
    assert!(client.send_counter == 0 && client.recv_counter == 0);
    assert!(server.send_counter == 0 && server.recv_counter == 0);
}

/// The four direction domains of the gateway session are pairwise distinct
/// (the real SHA3-256 constants, computed concretely). So the v2 and v3
/// schedules never use the same label either. Distinctness from the other
/// twelve registry domains is the unit test
/// `kdf::tests::every_listed_domain_is_distinct_and_stable`.
#[kani::proof]
#[kani::unwind(33)]
fn d_direction_domains_are_distinct() {
    let v3c = *crate::kdf::GATEWAY_V3_KEY_C2S;
    let v3s = *crate::kdf::GATEWAY_V3_KEY_S2C;
    let v2c = *crate::kdf::GATEWAY_V2_KEY_C2S;
    let v2s = *crate::kdf::GATEWAY_V2_KEY_S2C;
    assert!(v3c != v3s);
    assert!(v2c != v2s);
    assert!(v3c != v2c);
    assert!(v3c != v2s);
    assert!(v3s != v2c);
    assert!(v3s != v2s);
}
