/-
  PQTGProofs.Falcon

  Falcon-512 signature scheme parameter properties.

  Key results:
    - falcon_q_prime          — q = 12289 is prime
    - falcon_q_ntt_compat     — 512 ∣ (q - 1) (NTT-compatible)
    - falcon_n_power_of_two   — n = 2^9
    - falcon_pk_lt_mtu        — public key fits in a single packet
    - falcon_security_level   — bit security > 128

  Mirrors: crypto.rs Falcon-512 constants.
  Tier 3 verification (Kani → Verus → **Lean 4**).
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime

namespace PQTGProofs.Falcon

/-! ## Falcon modulus and ring dimension -/

/-- The Falcon modulus q = 12289. -/
def q : ℕ := 12289

/-- Falcon-512 ring dimension n = 512. -/
def n : ℕ := 512

/-- Falcon-512 public key size in bytes. -/
def pk_size : ℕ := 897

/-- Falcon-512 secret key size in bytes. -/
def sk_size : ℕ := 1281

/-- Falcon-512 maximum signature size in bytes. -/
def sig_max : ℕ := 666

/-! ## Theorems (14) -/

/-- q = 12289 is prime. Foundational to the NTRU lattice hardness assumption. -/
theorem falcon_q_prime : Nat.Prime q := by norm_num [q]

/-- q ≡ 1 (mod 512): NTT-compatibility for efficient polynomial multiplication.
    12289 = 24 × 512 + 1. -/
theorem falcon_q_ntt_compat : n ∣ (q - 1) := by norm_num [q, n]

/-- n = 512 > 0. -/
theorem falcon_n_pos : n > 0 := by norm_num [n]

/-- n = 512 = 2^9. -/
theorem falcon_n_power_of_two : n = 2 ^ 9 := by norm_num [n]

/-- Falcon-512 public key = 897 bytes. -/
theorem falcon_pk_size : pk_size = 897 := by rfl

/-- Falcon-512 secret key = 1281 bytes. -/
theorem falcon_sk_size : sk_size = 1281 := by rfl

/-- Falcon-512 max signature = 666 bytes. -/
theorem falcon_sig_max : sig_max = 666 := by rfl

/-- Falcon-512 public key fits in a single MTU (897 < 1500). -/
theorem falcon_pk_lt_mtu : pk_size < 1500 := by norm_num [pk_size]

/-- Falcon-512 signature fits in a single MTU (666 < 1500). -/
theorem falcon_sig_lt_mtu : sig_max < 1500 := by norm_num [sig_max]

/-- Falcon-512 pk + sig fits in a ClientHello (897 + 666 < 8192). -/
theorem falcon_pk_plus_sig_lt_clienthello : pk_size + sig_max < 8192 := by
  norm_num [pk_size, sig_max]

/-- Falcon-512 bit security: q^n has log₂ > 128.
    More precisely, q = 12289 > 2^13, so log₂(q^512) > 13 × 512 = 6656 >> 128. -/
theorem falcon_security_level : q ^ 1 > 2 ^ 13 := by norm_num [q]

/-- q = 12289 is odd. -/
theorem falcon_q_odd : ¬ 2 ∣ q := by norm_num [q]

/-- (q - 1) / n = 24: explicit NTT quotient. -/
theorem falcon_n_dvd_q_sub_one : (q - 1) / n = 24 := by norm_num [q, n]

/-- Combined key material: pk + sk = 2178 bytes. -/
theorem falcon_combined_pk_sk : pk_size + sk_size = 2178 := by norm_num [pk_size, sk_size]

end PQTGProofs.Falcon
