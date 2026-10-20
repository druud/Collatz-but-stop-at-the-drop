-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TSmoothProgram
import AcceleratedCollatz.TSternBrocotConv

/-!
  The A003586 program with a convergent of log2 3. Every semiconvergent p/n of log2 3
  (n ≥ 1) is a record fraction (`recordFrac_of_semiconv`): above log2 3, n is an upper record
  Order with p = p2(n); below it, a lower one with p = p2(n) - 1. So is every convergent
  N(j + 2)/D(j + 2), Mathlib's j-th convergent of log2 3 (`recordFrac_conv`,
  `log2_three_convs`), and with it, when its numerator exceeds 2h, the program returns the
  exponents of the n-th 3-smooth number (`latticeOrd_smoothJI_conv`). PARI's `bestappr`
  returns convergents of its argument; that they are those of log2 3 is a matter of the
  working precision.
-/

namespace AcceleratedCollatz

/-- A semiconvergent p/n of log2 3 with n ≥ 1 is a record fraction. -/
theorem recordFrac_of_semiconv {j t p n : ℕ} (h : IsSemiconvQ 3 j t p n) (hn : 1 ≤ n) :
    RecordFrac p n := by
  refine ⟨hn, ?_⟩
  rcases Nat.mod_two_eq_zero_or_one j with hj | hj
  · right
    refine ⟨(lowerRecord_iff_semiconv hn).mpr ⟨j, t, p, hj, h⟩, ?_⟩
    obtain ⟨k, hk1, hkp, hkn⟩ := (sbWalk_lo_iff (p := p) (n := n)).mpr ⟨j, t, hj, h⟩
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · have hk : k = 1 := by omega
      subst hk
      have h1 : (sbWalk 1).loNum + 1 = p2_of (sbWalk 1).loDen := by
        decide +kernel
      change (sbWalk 1).loNum = p at hkp
      change (sbWalk 1).loDen = n at hkn
      rw [hkp, hkn] at h1
      omega
    · have h1 := sbWalk_loNum hk2
      change (sbWalk k).loNum = p at hkp
      change (sbWalk k).loDen = n at hkn
      rw [hkp, hkn] at h1
      omega
  · left
    refine ⟨(upperRecord_iff_semiconv hn).mpr ⟨j, t, p, hj, h⟩, ?_⟩
    obtain ⟨k, hkp, hkn⟩ := (sbWalk_hi_iff (p := p) hn).mpr ⟨j, t, hj, h⟩
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · exfalso
      have h0 : (sbWalk k).hiDen = 0 := by
        rcases Nat.lt_or_ge k 1 with hk1 | hk1
        · have : k = 0 := by omega
          subst this
          decide +kernel
        · have : k = 1 := by omega
          subst this
          decide +kernel
      change (sbWalk k).hiDen = n at hkn
      omega
    · have h1 := sbWalk_hiNum hk2
      change (sbWalk k).hiNum = p at hkp
      change (sbWalk k).hiDen = n at hkn
      rw [hkp, hkn] at h1
      exact h1

/-- The convergent N(j + 2)/D(j + 2) of log2 3 is a record fraction. -/
theorem recordFrac_conv (j : ℕ) : RecordFrac (cfNumQ 3 (j + 2)) (cfDenQ 3 (j + 2)) := by
  apply recordFrac_of_semiconv (isSemiconvQ_conv (by decide) le_rfl j)
  rw [cfDenQ_add_two]
  have ha := one_le_cfQuotQ (q := 3) (by decide) le_rfl j
  have hd := one_le_cfDenQ_add 3 j
  have hm : cfDenQ 3 (j + 1) ≤ cfQuotQ 3 j * cfDenQ 3 (j + 1) := Nat.le_mul_of_pos_left _ ha
  omega

/-- With the j-th convergent of log2 3 as P/Q and P > 2h, the program returns the
    exponents of the n-th 3-smooth number. -/
theorem latticeOrd_smoothJI_conv {j n : ℕ} (hn : 1 ≤ n)
    (hP : 2 * smoothBound n < cfNumQ 3 (j + 2)) :
    latticeOrd 2 3 (2 ^ (smoothJI (cfNumQ 3 (j + 2)) (cfDenQ 3 (j + 2)) n).1 *
      3 ^ (smoothJI (cfNumQ 3 (j + 2)) (cfDenQ 3 (j + 2)) n).2) + 1 = n :=
  latticeOrd_smoothJI (recordFrac_conv j) hn hP

end AcceleratedCollatz
