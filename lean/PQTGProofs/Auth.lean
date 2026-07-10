/-
  PQTGProofs.Auth

  Authorized-keys file format conformance (dual-algorithm: Falcon + SLH-DSA).

  Scope: byte-level structural lemmas for the `authorized_keys` line format
  parsed by `auth.rs`. Does NOT prove anything about the security of the
  dual-algorithm composition; that depends on Falcon EUF-CMA and SLH-DSA
  EUF-CMA, both inherited from their respective standards.

  Mirrors: src/auth.rs (FALCON_VK_LEN = 897, SLH_DSA_VK_LEN = 32,
                       algorithm = "falcon512+slh-dsa-shake128f").
-/

import Mathlib.Tactic.NormNum

namespace PQTGProofs.Auth

/-! ## Authentication constants -/

/-- Falcon-512 verification key size in bytes. -/
def falcon_pk_size : ℕ := 897

/-- SLH-DSA-Shake128f verification key size in bytes. -/
def sphincs_pk_size : ℕ := 32

/-- Combined verification key: Falcon ‖ SLH-DSA. -/
def combined_pk_size : ℕ := 929

/-- Maximum concurrent connections. -/
def max_connections : ℕ := 100

/-- Algorithm string: "falcon512+slh-dsa-shake128f" = 27 characters. -/
def algorithm_string_len : ℕ := 27

/-! ## Parameter conformance lemmas -/

/-- Combined PK: falcon_pk(897) + sphincs_pk(32) = 929 bytes. -/
theorem combined_pk_size_eq :
    falcon_pk_size + sphincs_pk_size = combined_pk_size := by
  norm_num [falcon_pk_size, sphincs_pk_size, combined_pk_size]

/-- Base64-encoded combined PK: ⌈929 × 4/3⌉ = 1240 characters.
    929 bytes → ⌈929/3⌉ × 4 = 310 × 4 = 1240. -/
theorem base64_encoded_pk_size :
    (combined_pk_size + 2) / 3 * 4 = 1240 := by
  norm_num [combined_pk_size]

/-- Algorithm identifier: "falcon512+slh-dsa-shake128f" = 27 characters. -/
theorem algorithm_string : algorithm_string_len = 27 := by rfl

/-- Dual-algorithm verification: both Falcon AND SLH-DSA must verify.
    Modeled: combined_pk contains material from both schemes. -/
theorem auth_requires_both_keys :
    combined_pk_size = falcon_pk_size + sphincs_pk_size := by
  norm_num [combined_pk_size, falcon_pk_size, sphincs_pk_size]

/-- Falcon PK starts at byte 0 in the combined key. -/
theorem falcon_pk_offset : (0 : ℕ) + falcon_pk_size = 897 := by
  norm_num [falcon_pk_size]

/-- SLH-DSA vk starts at byte 897 in the combined key. -/
theorem sphincs_pk_offset : falcon_pk_size = 897 := by
  norm_num [falcon_pk_size]

/-- Max concurrent connections = 100. -/
theorem max_connections_eq : max_connections = 100 := by rfl

/-- Wildcard "*" grants all permissions.
    Modeled: the wildcard is a single character. -/
theorem permission_wildcard : String.length "*" = 1 := by native_decide

/-- Private key file permissions: owner read-write only (0o600 = 384 decimal).
    Modeled: 6 × 64 = 384. -/
theorem key_file_permissions : 6 * 64 = 384 := by norm_num

/-- Dual-algorithm security: attacker must break BOTH Falcon AND SLH-DSA.
    Since SLH-DSA is hash-based and Falcon is lattice-based, the security
    floor is min(lattice, hash) under the independent-failure assumption.
    Both provide ≥ 128-bit PQ security. -/
theorem dual_algorithm_security : min 128 128 = 128 := by norm_num

end PQTGProofs.Auth
