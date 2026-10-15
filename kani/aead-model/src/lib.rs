//! Kani only. Stands in for the `aes-gcm` crate when `src/crypto.rs` is
//! compiled for the proofs in `kani/`. Every item `src/crypto.rs` imports from
//! `aes_gcm` is the real one, re-exported from aes-gcm 0.10, except
//! `Aes256Gcm`, which is the model below.
//!
//! What the model is. A type with the real `aead` 0.5 traits (`KeyInit`, and
//! `AeadCore` with a 12-byte nonce and a 16-byte tag, and `AeadInPlace`), so
//! the real blanket `Aead::encrypt` / `Aead::decrypt` and the real default
//! `encrypt_in_place` / `decrypt_in_place` of the `aead` crate run unchanged
//! around it. Only the two detached primitives, the part that is AES-256-GCM,
//! are replaced. Each records the key and the nonce it was called with.
//!
//! It runs in one of two modes, chosen by the harness:
//!
//! - Oracle mode (default). The outcome of the next seal or open (success or
//!   failure) is whatever the harness wrote in [`oracle::SEAL_OK`] /
//!   [`oracle::OPEN_OK`]. A harness that sets them from `kani::any()` covers
//!   every outcome a real AEAD could produce for that call, a failed tag
//!   included. Nothing is encrypted.
//! - Ideal mode ([`oracle::IDEAL`]). An ideal authenticated encryption, as a
//!   table: sealing always succeeds, leaves the bytes as they are (no
//!   confidentiality is modelled) with an all-zero tag, and records the
//!   (key, nonce, bytes) triple; opening succeeds if and only if the exact
//!   (key, nonce, bytes, tag) was produced by an earlier seal. This is the
//!   INT-CTXT property of AES-256-GCM made perfect, which is a cryptographic
//!   assumption, not something any harness proves.
//!
//! What the model is not: a cipher. Whether AES-256-GCM really behaves as the
//! ideal mode says is outside every proof that uses it.

pub use aes_gcm::aead;
pub use aes_gcm::{AeadCore, AeadInPlace, Error, Key, KeyInit, KeySizeUser, Nonce, Tag};

use aes_gcm::aead::consts::{U0, U12, U16, U32};

/// The model that replaces AES-256-GCM. Holds its key so harnesses can see
/// which key each end seals and opens with.
#[derive(Clone)]
pub struct Aes256Gcm {
    pub key: [u8; 32],
}

impl KeySizeUser for Aes256Gcm {
    type KeySize = U32;
}

impl KeyInit for Aes256Gcm {
    fn new(key: &Key<Self>) -> Self {
        let mut k = [0u8; 32];
        k.copy_from_slice(key.as_slice());
        Self { key: k }
    }
}

impl AeadCore for Aes256Gcm {
    type NonceSize = U12;
    type TagSize = U16;
    type CiphertextOverhead = U0;
}

/// Oracles the harness sets and records the model writes. Plain `static mut`
/// because Kani verifies one thread; nothing else reads them.
pub mod oracle {
    /// How many seal calls are logged individually.
    pub const LOG: usize = 6;

    /// Outcome of seal calls in oracle mode.
    pub static mut SEAL_OK: bool = true;
    /// Outcome of open calls in oracle mode.
    pub static mut OPEN_OK: bool = true;
    /// Ideal mode instead of oracle mode.
    pub static mut IDEAL: bool = false;

    /// Calls into the sealing primitive, failed ones included.
    pub static mut SEAL_CALLS: usize = 0;
    /// Calls into the opening primitive, failed ones included.
    pub static mut OPEN_CALLS: usize = 0;

    /// Per seal call, in order: key, nonce, and whether it succeeded.
    pub static mut SEAL_KEY: [[u8; 32]; LOG] = [[0; 32]; LOG];
    pub static mut SEAL_NONCE: [[u8; 12]; LOG] = [[0; 12]; LOG];
    pub static mut SEAL_DONE: [bool; LOG] = [false; LOG];
    /// Ideal mode: the bytes each successful seal produced (one-byte frames;
    /// longer ones are refused by the model so a harness cannot exceed it).
    pub static mut SEAL_BYTE: [u8; LOG] = [0; LOG];

    /// The last open call: key, nonce, and ciphertext length without the tag.
    pub static mut OPEN_KEY: [u8; 32] = [0; 32];
    pub static mut OPEN_NONCE: [u8; 12] = [0; 12];
    pub static mut OPEN_LEN: usize = 0;

    /// Back to a fresh state; harnesses call this first.
    pub fn reset() {
        unsafe {
            SEAL_OK = true;
            OPEN_OK = true;
            IDEAL = false;
            SEAL_CALLS = 0;
            OPEN_CALLS = 0;
            SEAL_KEY = [[0; 32]; LOG];
            SEAL_NONCE = [[0; 12]; LOG];
            SEAL_DONE = [false; LOG];
            SEAL_BYTE = [0; LOG];
            OPEN_KEY = [0; 32];
            OPEN_NONCE = [0; 12];
            OPEN_LEN = 0;
        }
    }
}

impl AeadInPlace for Aes256Gcm {
    fn encrypt_in_place_detached(
        &self,
        nonce: &Nonce<U12>,
        _associated_data: &[u8],
        buffer: &mut [u8],
    ) -> Result<Tag<U16>, Error> {
        unsafe {
            let i = oracle::SEAL_CALLS;
            oracle::SEAL_CALLS += 1;
            if i >= oracle::LOG {
                // A harness that seals more often than the log holds is
                // outside what the model was built for: fail loudly.
                panic!("aead model: seal log exhausted");
            }
            oracle::SEAL_KEY[i] = self.key;
            let mut n = [0u8; 12];
            n.copy_from_slice(nonce.as_slice());
            oracle::SEAL_NONCE[i] = n;
            let ok = if oracle::IDEAL {
                if buffer.len() != 1 {
                    panic!("aead model: ideal mode seals one-byte frames only");
                }
                oracle::SEAL_BYTE[i] = buffer[0];
                true
            } else {
                oracle::SEAL_OK
            };
            oracle::SEAL_DONE[i] = ok;
            if ok {
                Ok(Tag::<U16>::default())
            } else {
                Err(Error)
            }
        }
    }

    fn decrypt_in_place_detached(
        &self,
        nonce: &Nonce<U12>,
        _associated_data: &[u8],
        buffer: &mut [u8],
        tag: &Tag<U16>,
    ) -> Result<(), Error> {
        unsafe {
            oracle::OPEN_CALLS += 1;
            oracle::OPEN_KEY = self.key;
            let mut n = [0u8; 12];
            n.copy_from_slice(nonce.as_slice());
            oracle::OPEN_NONCE = n;
            oracle::OPEN_LEN = buffer.len();
            let ok = if oracle::IDEAL {
                let mut found = false;
                let mut i = 0;
                while i < oracle::SEAL_CALLS && i < oracle::LOG {
                    if oracle::SEAL_DONE[i]
                        && oracle::SEAL_KEY[i] == self.key
                        && oracle::SEAL_NONCE[i] == n
                        && buffer.len() == 1
                        && buffer[0] == oracle::SEAL_BYTE[i]
                        && tag.as_slice() == [0u8; 16]
                    {
                        found = true;
                    }
                    i += 1;
                }
                found
            } else {
                oracle::OPEN_OK
            };
            if ok {
                Ok(())
            } else {
                Err(Error)
            }
        }
    }
}
