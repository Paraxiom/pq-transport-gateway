// Wraps the gateway's src/crypto.rs, unmodified, in `pub mod crypto { ... }`
// and appends the proofs as a child module, so they can read the session's
// private counters exactly as the in-file unit tests do. Nothing is edited:
// the bytes of src/crypto.rs are copied as they are, and the build fails if
// the copy ever differs from the file.

use std::env;
use std::fs;
use std::path::PathBuf;

fn main() {
    let manifest = PathBuf::from(env::var("CARGO_MANIFEST_DIR").expect("manifest dir"));
    let crypto = manifest.join("../src/crypto.rs");
    let proofs = manifest.join("src/session_proofs.rs");
    println!("cargo:rerun-if-changed={}", crypto.display());
    println!("cargo:rerun-if-changed={}", proofs.display());

    let source = fs::read_to_string(&crypto).expect("read src/crypto.rs");
    let proofs = proofs.canonicalize().expect("proofs path");
    let wrapped = format!(
        "pub mod crypto {{\n{source}\n#[cfg(kani)]\nmod session_proofs {{\ninclude!({:?});\n}}\n}}\n",
        proofs.display().to_string()
    );
    // The copy must contain the file byte for byte.
    assert!(wrapped.contains(&source));

    let out = PathBuf::from(env::var("OUT_DIR").expect("out dir")).join("crypto_under_proof.rs");
    fs::write(out, wrapped).expect("write wrapped crypto.rs");
}
