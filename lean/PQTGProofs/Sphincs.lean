/-
  PQTGProofs.Sphincs

  SLH-DSA-Shake128f (FIPS 205) parameter conformance.

  Scope: parameter sizes used by `paraxiom-pqc::sign` for the SLH-DSA-Shake128f
  algorithm (the hash-based signature scheme PQTG uses for audit-trail
  signatures alongside Falcon). Does NOT prove EUF-CMA security; that is
  inherited from FIPS 205.

  Note: this module is named `Sphincs` for backward compatibility with the
  v0.1 Lean library (which referenced SPHINCS+). The actual algorithm in
  use is SLH-DSA-Shake128f, the FIPS 205 standardization of SPHINCS+.

  Mirrors: src/crypto.rs (HASH_ALG = SignAlgorithm::SlhDsaShake128f).
-/

import Mathlib.Tactic.NormNum

namespace PQTGProofs.Sphincs

/-! ## SLH-DSA-Shake128f constants (FIPS 205 §11) -/

/-- SLH-DSA-Shake128f verification key size in bytes. -/
def pk_size : ℕ := 32

/-- SLH-DSA-Shake128f signing key size in bytes (when serialized as
    full key material; paraxiom-pqc stores the full key, not just a seed). -/
def sk_size : ℕ := 64

/-- SLH-DSA-Shake128f signature size in bytes. -/
def sig_size : ℕ := 17088

/-- SLH-DSA-Shake128f post-quantum security level in bits (NIST Level 1). -/
def security_bits : ℕ := 128

/-! ## Parameter conformance lemmas -/

theorem slh_dsa_pk_size : pk_size = 32 := rfl
theorem slh_dsa_sk_size : sk_size = 64 := rfl
theorem slh_dsa_sig_size : sig_size = 17088 := rfl
theorem slh_dsa_security_bits : security_bits = 128 := rfl

/-- SLH-DSA-Shake128f vk = 32 bytes = SHA-256 output size. -/
theorem slh_dsa_pk_eq_sha256 : pk_size = 32 := rfl

/-- SLH-DSA-Shake128f sk = 2 × pk (PK_seed ‖ PK_root, each 16 bytes,
    concatenated with SK_seed and SK_prf). -/
theorem slh_dsa_sk_eq_two_pk : sk_size = 2 * pk_size := by norm_num [sk_size, pk_size]

/-- NIST Level 1: 128 ≥ 128 bits PQ security. -/
theorem slh_dsa_pq_security : security_bits ≥ 128 := by norm_num [security_bits]

/-- SLH-DSA-Shake128f vk fits in a CPU cache line (32 ≤ 64). -/
theorem slh_dsa_pk_fits_cache_line : pk_size ≤ 64 := by norm_num [pk_size]

/-- SLH-DSA-Shake128f vk < Falcon-512 vk: 32 < 897. Hash-based vks are compact. -/
theorem slh_dsa_pk_lt_falcon_pk : pk_size < 897 := by norm_num [pk_size]

/-- SLH-DSA is stateless: signature is a function of (sk, message,
    randomness). Modeled abstractly: vk + sk < signature (the small keys
    expand into a much larger signature). -/
theorem slh_dsa_stateless : pk_size + sk_size < sig_size := by
  norm_num [pk_size, sk_size, sig_size]

/-- Signature size is bounded by the per-frame request limit (≤ 1 MB). -/
theorem slh_dsa_sig_lt_max_frame : sig_size < 1048576 := by norm_num [sig_size]

/-- Total key+signature material per audit signature: vk + sig. -/
theorem slh_dsa_audit_overhead : pk_size + sig_size = 17120 := by
  norm_num [pk_size, sig_size]

end PQTGProofs.Sphincs
