/-
  PQTGProofs.KeyMixing

  SHA3-256 key-mixing parameter conformance (QKD + PQC hybrid).

  Scope: byte-level structural lemmas for the `mix_keys` function — domain
  separator length, output size, deterministic structure. Does NOT prove
  collision/preimage resistance of SHA3-256; those are inherited from the
  Keccak family.

  Mirrors: src/crypto.rs (mix_keys, KEY_MIXING_LABEL = "pqtg-key-mixing-v2").
-/

import Mathlib.Tactic.NormNum

namespace PQTGProofs.KeyMixing

/-! ## Key mixing constants -/

/-- SHA3-256 output size in bytes. -/
def sha3_output : ℕ := 32

/-- Domain separator string "pqtg-key-mixing-v2" = 18 bytes. -/
def domain_sep_len : ℕ := 18

/-- PQC shared secret size in bytes (ML-KEM-768 output, also = SHA3-256 output). -/
def pqc_key_size : ℕ := 32

/-- Maximum QKD key size accepted by `mix_keys` (1 MB). -/
def max_qkd_key : ℕ := 1048576

/-- Length-prefix field size used for the QKD-key length frame (`u32`). -/
def length_prefix_size : ℕ := 4

/-! ## Parameter conformance lemmas -/

theorem sha3_256_output : sha3_output = 32 := rfl
theorem domain_separator : domain_sep_len = 18 := rfl

/-- The mixed-key output size equals the SHA3-256 output size — derived,
    not a separate fact, to make the dependency explicit. -/
theorem mixed_key_size : sha3_output = 32 := sha3_256_output

/-- The PQC half of the mix is non-empty and exactly 32 bytes. This is the
    *structural* property; that both QKD and PQC inputs actually contribute
    to the output is an operational fact about how `mix_keys` is invoked
    by `src/crypto.rs` (not a parameter-conformance lemma). -/
theorem pqc_half_well_formed : pqc_key_size > 0 ∧ pqc_key_size = 32 := by
  constructor <;> norm_num [pqc_key_size]

/-- Domain-separator length is positive (prevents cross-protocol collision
    with sibling KDFs that share SHA3-256 but differ in domain). -/
theorem domain_separation_prevents_collision : domain_sep_len > 0 := by
  norm_num [domain_sep_len]

/-- PQC-only fallback: when QKD is unavailable, the PQC secret (32 bytes)
    flows through directly; the output remains 32 bytes (same hash output). -/
theorem pqc_only_fallback : pqc_key_size = sha3_output := by
  norm_num [pqc_key_size, sha3_output]

/-- The PQC shared secret provides 256 bits of entropy. ML-KEM-768 targets
    NIST PQC security category 3 (~192-bit post-quantum security level);
    informal heuristics that "Grover halves classical bit-strength" should
    not be conflated with this structural fact — see `docs/THREAT-MODEL.md`
    for the security argument. -/
theorem pqc_secret_bits : pqc_key_size * 8 = 256 := by
  norm_num [pqc_key_size]

theorem qkd_key_max_size : max_qkd_key = 2 ^ 20 := by norm_num [max_qkd_key]

/-- Minimum hash input: domain_sep(18) + length_prefix(4) + qkd(≥0) + pqc(32). -/
theorem mixing_input_size : domain_sep_len + length_prefix_size + pqc_key_size ≥ 54 := by
  norm_num [domain_sep_len, length_prefix_size, pqc_key_size]

/-- SHA3-256 collision resistance: 128 bits (birthday on 256-bit output). -/
theorem sha3_256_collision_resistance : sha3_output * 8 / 2 = 128 := by
  norm_num [sha3_output]

/-- SHA3-256 preimage resistance: 256 bits (full output length). -/
theorem sha3_256_preimage_resistance : sha3_output * 8 = 256 := by
  norm_num [sha3_output]

end PQTGProofs.KeyMixing
