-- SPDX-License-Identifier: MIT
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Nat.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
  General number theory facts, independent of R and T.
-/

namespace AcceleratedCollatz

/-- Trailing 1-bits of n: the 2-adic valuation of n+1. -/
def trailingOnes (n : ℕ) : ℕ := padicValNat 2 (n + 1)

/-- Trailing 0-bits of n: the 2-adic valuation of n. -/
def trailingZeros (n : ℕ) : ℕ := padicValNat 2 n

/-- n+1 is exactly divisible by 2^(trailingOnes n). -/
theorem pow_trailingOnes_dvd (x : ℕ) : 2 ^ (trailingOnes x) ∣ (x + 1) := pow_padicValNat_dvd

/-- Dividing x+1 by the full power of 2 dividing it leaves an odd quotient. -/
theorem odd_div_pow_trailingOnes (x : ℕ) (_hx : Odd x) :
    Odd ((x + 1) / 2 ^ (trailingOnes x)) := by
  rw [← Nat.not_even_iff_odd]
  intro heven
  apply pow_succ_padicValNat_not_dvd (p := 2) (n := x + 1) (by omega)
  obtain ⟨q, hq⟩ := heven
  have heq : (x + 1) / 2 ^ (trailingOnes x) * 2 ^ (trailingOnes x) = x + 1 :=
    Nat.div_mul_cancel (pow_padicValNat_dvd (p := 2) (n := x + 1))
  have hval : x + 1 = 2 ^ (trailingOnes x + 1) * q := by
    rw [pow_succ]
    calc x + 1 = (x + 1) / 2 ^ (trailingOnes x) * 2 ^ (trailingOnes x) := heq.symm
      _ = (q + q) * 2 ^ (trailingOnes x) := by rw [hq]
      _ = 2 ^ (trailingOnes x) * 2 * q := by ring
  exact ⟨q, hval⟩

/-- 2^(v+1) ≤ 3^v for v ≥ 2. -/
theorem three_pow_ge_two_pow_succ : ∀ v ≥ 2, 3 ^ v ≥ 2 ^ (v + 1) := by
  intro v hv
  induction v, hv using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    calc 2 ^ (n + 1 + 1) = 2 * 2 ^ (n + 1) := by ring
      _ ≤ 2 * 3 ^ n := by omega
      _ ≤ 3 * 3 ^ n := by omega
      _ = 3 ^ (n + 1) := by ring
/-- Dividing x by the full power of 2 dividing it leaves an odd quotient. -/
theorem odd_div_pow_trailingZeros (x : ℕ) (hx : x ≠ 0) :
    Odd (x / 2 ^ (trailingZeros x)) := by
  rw [← Nat.not_even_iff_odd]
  intro heven
  apply pow_succ_padicValNat_not_dvd (p := 2) (n := x) hx
  obtain ⟨q, hq⟩ := heven
  have heq : x / 2 ^ (trailingZeros x) * 2 ^ (trailingZeros x) = x :=
    Nat.div_mul_cancel (pow_padicValNat_dvd (p := 2) (n := x))
  have hval : x = 2 ^ (trailingZeros x + 1) * q := by
    rw [pow_succ]
    calc x = x / 2 ^ (trailingZeros x) * 2 ^ (trailingZeros x) := heq.symm
      _ = (q + q) * 2 ^ (trailingZeros x) := by rw [hq]
      _ = 2 ^ (trailingZeros x) * 2 * q := by ring
  exact ⟨q, hval⟩

end AcceleratedCollatz
