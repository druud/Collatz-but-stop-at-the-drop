-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.DropEquivalence
import AcceleratedCollatz.RMap

/-!
  The R-trajectory and its stopping index (`trajectory`, `sigma`; paper sec:fast),
  the per-step order contribution `stepOrder`, and the length `p2_of` (paper
  sec:words).
-/

namespace AcceleratedCollatz

def trajectory (x0 : ℕ) (j : ℕ) : ℕ := R^[j] x0

noncomputable def sigma (x0 : ℕ) (h : ∃ k ≥ 1, trajectory x0 k < x0) : ℕ :=
  Nat.find h

theorem sigma_spec (x0 : ℕ) (h : ∃ k ≥ 1, trajectory x0 k < x0) :
    sigma x0 h ≥ 1 ∧ trajectory x0 (sigma x0 h) < x0 :=
  Nat.find_spec h

def stepOrder (x : ℕ) : ℕ := if Odd x then trailingOnes x else 0

/-- Length of an admissible word of Order p3: the least p2 with 3^p3 < 2^p2. -/
def p2_of (p3 : ℕ) : ℕ := Nat.log 2 (3 ^ p3) + 1

theorem p2_of_spec (p3 : ℕ) : 2 ^ (p2_of p3) > 3 ^ p3 := by
  unfold p2_of
  exact Nat.lt_pow_succ_log_self (by omega) (3 ^ p3)

/-- Lower side of the bound on `p2_of`: 2^(p2_of p3 - 1) ≤ 3^p3. -/
theorem p2_of_spec_lower (p3 : ℕ) : 2 ^ (p2_of p3 - 1) ≤ 3 ^ p3 := by
  unfold p2_of
  simp only [Nat.add_sub_cancel]
  exact Nat.pow_log_le_self 2 (by positivity)

end AcceleratedCollatz
