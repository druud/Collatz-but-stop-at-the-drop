-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TBlockRecord
import AcceleratedCollatz.TRhoMax

/-!
  The terms of the slack of `rho_le_of_admissible` and the lower record Orders. By
  `rhoMax_slack` the slack 2 (n 3^(n-1) - rhoMax n) is the sum over m < n of the terms
  3^(n-1-m) d(m), with the lower deficit d(m) = 2 3^m - 2^p2(m) (`lowDeficit`; d(0) = 0).
  Two terms compare like d(m) 3^k and d(k) 3^m (`slackTerm_lt_iff`), and d(m) 3^k is below
  d(k) 3^m for every 1 ≤ k < m exactly when m is a lower record Order
  (`lowerRecord_iff_lowDeficit`). So, in every Order n > m, the term of m is smaller than
  every earlier term from k = 1 on exactly at the lower record Orders m
  (`lowerRecord_iff_slackTerm`).
-/

namespace AcceleratedCollatz

/-- The lower deficit of Order m: 2 3^m - 2^p2(m). -/
def lowDeficit (m : ℕ) : ℕ := 2 * 3 ^ m - 2 ^ p2_of m

theorem lowDeficit_add (m : ℕ) : lowDeficit m + 2 ^ p2_of m = 2 * 3 ^ m :=
  Nat.sub_add_cancel (two_pow_p2_of_le_nat m)

theorem lowDeficit_zero : lowDeficit 0 = 0 := by
  decide

/-- Lower record Orders: d(m) 3^k < d(k) 3^m for every 1 ≤ k < m. -/
theorem lowerRecord_iff_lowDeficit (m : ℕ) :
    LowerRecord m ↔ ∀ k, 1 ≤ k → k < m → lowDeficit m * 3 ^ k < lowDeficit k * 3 ^ m := by
  rw [lowerRecord_iff_blockFactor]
  apply forall_congr'
  intro k
  apply imp_congr_right
  intro _
  apply imp_congr_right
  intro _
  rw [blockFactor_eq, blockFactor_eq, div_lt_div_iff₀ (by positivity) (by positivity)]
  have hq : ((3 : ℚ) ^ m * 2 ^ p2_of k < 3 ^ k * 2 ^ p2_of m) ↔
      (3 ^ m * 2 ^ p2_of k < 3 ^ k * 2 ^ p2_of m) := by
    norm_cast
  rw [hq]
  have e1 : lowDeficit m * 3 ^ k + 3 ^ k * 2 ^ p2_of m = 2 * (3 ^ m * 3 ^ k) := by
    rw [Nat.mul_comm (3 ^ k), ← Nat.add_mul, lowDeficit_add]
    ring
  have e2 : lowDeficit k * 3 ^ m + 3 ^ m * 2 ^ p2_of k = 2 * (3 ^ m * 3 ^ k) := by
    rw [Nat.mul_comm (3 ^ m), ← Nat.add_mul, lowDeficit_add]
    ring
  omega

/-- In Order n, the terms 3^(n-1-m) d(m) and 3^(n-1-k) d(k) of the slack compare like
    d(m) 3^k and d(k) 3^m. -/
theorem slackTerm_lt_iff {n m k : ℕ} (hm : m < n) (hk : k < n) :
    3 ^ (n - 1 - m) * lowDeficit m < 3 ^ (n - 1 - k) * lowDeficit k ↔
      lowDeficit m * 3 ^ k < lowDeficit k * 3 ^ m := by
  have hE1 : 3 ^ (n - 1 - m) * 3 ^ m = 3 ^ (n - 1) := by
    rw [← pow_add]
    congr 1
    omega
  have hE2 : 3 ^ (n - 1 - k) * 3 ^ k = 3 ^ (n - 1) := by
    rw [← pow_add]
    congr 1
    omega
  have hpos : 0 < 3 ^ m * 3 ^ k := by
    positivity
  have hpos' : 0 < 3 ^ (n - 1) := by
    positivity
  have eL : 3 ^ (n - 1 - m) * lowDeficit m * (3 ^ m * 3 ^ k) =
      lowDeficit m * 3 ^ k * 3 ^ (n - 1) := by
    rw [← hE1]
    ring
  have eR : 3 ^ (n - 1 - k) * lowDeficit k * (3 ^ m * 3 ^ k) =
      lowDeficit k * 3 ^ m * 3 ^ (n - 1) := by
    rw [← hE2]
    ring
  constructor
  · intro h
    have h1 := Nat.mul_lt_mul_of_pos_right h hpos
    rw [eL, eR] at h1
    exact Nat.lt_of_mul_lt_mul_right h1
  · intro h
    have h1 := Nat.mul_lt_mul_of_pos_right h hpos'
    rw [← eL, ← eR] at h1
    exact Nat.lt_of_mul_lt_mul_right h1

/-- In Order n > m, the term of m in the slack is smaller than every earlier term from
    k = 1 on exactly when m is a lower record Order. -/
theorem lowerRecord_iff_slackTerm {n m : ℕ} (hm : m < n) :
    LowerRecord m ↔
      ∀ k, 1 ≤ k → k < m → 3 ^ (n - 1 - m) * lowDeficit m < 3 ^ (n - 1 - k) * lowDeficit k := by
  rw [lowerRecord_iff_lowDeficit]
  apply forall_congr'
  intro k
  apply imp_congr_right
  intro _
  apply imp_congr_right
  intro hkm
  exact (slackTerm_lt_iff hm (by omega)).symm

end AcceleratedCollatz
