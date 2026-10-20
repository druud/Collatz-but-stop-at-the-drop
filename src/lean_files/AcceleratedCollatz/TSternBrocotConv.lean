-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TSternBrocot
import AcceleratedCollatz.TSternBrocotConvQ

/-!
  The record Orders and the continued fraction of log2 3: the q = 3 case of
  TSternBrocotConvQ. The fractions above log2 3 on the Stern–Brocot walk are exactly its
  semiconvergents Q(j) + t Q(j + 1) with odd j and 1 ≤ t ≤ a(j), those below it after the
  first step exactly the ones with even j (`sbWalk_hi_iff`, `sbWalk_lo_iff`); t = a(j)
  gives the convergent Q(j + 2), Mathlib's j-th convergent of log2 3 (`log2_three_convs`).
  So the upper record Orders n ≥ 1 are exactly the denominators of the semiconvergents
  above log2 3 (`upperRecord_iff_semiconv`), the lower ones those of the semiconvergents
  below it (`lowerRecord_iff_semiconv`).
-/

namespace AcceleratedCollatz

/-- The fractions above log2 3 on the walk, with denominator n ≥ 1, are exactly the
    semiconvergents of log2 3 with odd j. -/
theorem sbWalk_hi_iff {p n : ℕ} (hn : 1 ≤ n) :
    (∃ k, (sbWalk k).hiNum = p ∧ (sbWalk k).hiDen = n) ↔
      ∃ j t, j % 2 = 1 ∧ IsSemiconvQ 3 j t p n :=
  sbWalkQ_hi_iff (by decide) le_rfl hn

/-- The fractions below log2 3 on the walk after its first step are exactly the
    semiconvergents of log2 3 with even j. -/
theorem sbWalk_lo_iff {p n : ℕ} :
    (∃ k, 1 ≤ k ∧ (sbWalk k).loNum = p ∧ (sbWalk k).loDen = n) ↔
      ∃ j t, j % 2 = 0 ∧ IsSemiconvQ 3 j t p n :=
  sbWalkQ_lo_iff (by decide) le_rfl

/-- The upper record Orders n ≥ 1 are exactly the denominators of the semiconvergents of
    log2 3 above it. -/
theorem upperRecord_iff_semiconv {n : ℕ} (hn : 1 ≤ n) :
    UpperRecord n ↔ ∃ j t p, j % 2 = 1 ∧ IsSemiconvQ 3 j t p n :=
  upperRecordQ_iff_semiconvQ (by decide) le_rfl hn

/-- The lower record Orders n ≥ 1 are exactly the denominators of the semiconvergents of
    log2 3 below it. -/
theorem lowerRecord_iff_semiconv {n : ℕ} (hn : 1 ≤ n) :
    LowerRecord n ↔ ∃ j t p, j % 2 = 0 ∧ IsSemiconvQ 3 j t p n :=
  lowerRecordQ_iff_semiconvQ (by decide) le_rfl hn

/-- Q(j + 2) is Mathlib's j-th convergent of log2 3. -/
theorem log2_three_convs (j : ℕ) :
    (GenContFract.of (Real.logb 2 3)).convs j = (cfNumQ 3 (j + 2) : ℝ) / cfDenQ 3 (j + 2) := by
  have h := of_log2Q_convs (q := 3) (by decide) le_rfl j
  rw [log2Q, Nat.cast_ofNat] at h
  exact h

end AcceleratedCollatz
