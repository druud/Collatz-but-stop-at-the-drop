-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TNest
import AcceleratedCollatz.TSurvivors

/-!
  The period of OEIS A399760 (the odd part of the parity vector of 4n - 1 until the drop).
  When x > 1 drops at step L and its first L parity bits form an admissible word (x drops at
  its coefficient stopping time), every x + 2^L j has the same first L bits and drops first
  at step L too (`isTDrop_add_of_admissible`): the prefixes keep a coefficient above 1, so no
  member of the class is below itself before step L, and at step L the coefficient is below 1
  and the larger start keeps the drop. With x = 4n - 1 this is the period 2^(L-2) of
  A399760 (`a399760_period`). That every x > 1 drops at its coefficient stopping time is
  Terras's conjecture (Terras 1976, Conjecture 2.9).
-/

namespace AcceleratedCollatz

/-- Admissible drop word at x: every x + 2^L j drops first at L, with the same word. -/
theorem isTDrop_add_of_admissible {x L : ℕ} (hx : 1 < x) (hA : Admissible (tBits x L))
    (hD : tStep^[L] x < x) (j : ℕ) :
    IsTDrop (x + 2 ^ L * j) L ∧ tBits (x + 2 ^ L * j) L = tBits x L := by
  set y := x + 2 ^ L * j with hy
  have hb : tBits y L = tBits x L := by
    refine tBits_congr _ _ _ ?_
    change (x + 2 ^ L * j) % 2 ^ L = x % 2 ^ L
    exact Nat.add_mul_mod_self_left x (2 ^ L) j
  refine ⟨?_, hb⟩
  have hy1 : y ≠ 1 := by omega
  simp only [IsTDrop, hy1, ↓reduceIte]
  have hL : 0 < L := by
    rcases Nat.eq_zero_or_pos L with h0 | h0
    · rw [h0] at hD
      simp at hD
    · exact h0
  refine ⟨hL, ?_, ?_⟩
  · -- the drop at L: 3^o y + rho < 2^L y
    have hlt : 3 ^ order (tBits x L) < 2 ^ L := by
      have := (seqProduct_lt_one_iff (tBits x L)).mp hA.lt_one
      rwa [length_tBits] at this
    have hNx := tStep_iterate_nForm L x
    have hNy := tStep_iterate_nForm L y
    rw [hb] at hNy
    have hx2 : 3 ^ order (tBits x L) * x + rho (tBits x L) < 2 ^ L * x := by
      have := Nat.mul_lt_mul_of_pos_left hD (by positivity : 0 < 2 ^ L)
      omega
    have hj : 3 ^ order (tBits x L) * (2 ^ L * j) ≤ 2 ^ L * (2 ^ L * j) :=
      Nat.mul_le_mul_right _ hlt.le
    have hyL : 2 ^ L * tStep^[L] y < 2 ^ L * y := by
      rw [hNy, hy, Nat.mul_add, Nat.mul_add]
      omega
    exact Nat.lt_of_mul_lt_mul_left hyL
  · -- before L: the prefix coefficients are above 1
    intro k hk0 hkL
    have hp := hA.prefix_gt k hk0 (by rw [length_tBits]; exact hkL)
    rw [← hb, tBits_take y L k hkL.le, one_lt_seqProduct_iff, length_tBits] at hp
    exact (lt_tStep_iterate_of_pow_lt (by omega) hp).le

/-- A399760: a(n) = a(n + 2^(L-2)) when 4n - 1 drops at L with an admissible word. -/
theorem a399760_period {n L : ℕ} (hn : 1 ≤ n) (hA : Admissible (tBits (4 * n - 1) L))
    (hD : tStep^[L] (4 * n - 1) < 4 * n - 1) :
    IsTDrop (4 * (n + 2 ^ (L - 2)) - 1) L ∧
      tBits (4 * (n + 2 ^ (L - 2)) - 1) L = tBits (4 * n - 1) L := by
  have hL : 2 ≤ L := by
    rcases L with _ | _ | L
    · exact absurd hA.lt_one (by simp [tBits, seqProduct])
    · have hodd : (4 * n - 1) % 2 = 1 := by omega
      exact absurd hA.lt_one (by norm_num [tBits, hodd, seqProduct, factor])
    · omega
  have he : 4 * (n + 2 ^ (L - 2)) - 1 = 4 * n - 1 + 2 ^ L * 1 := by
    have : 2 ^ L = 4 * 2 ^ (L - 2) := by
      rw [show 4 = 2 ^ 2 by norm_num, ← pow_add]
      congr 1
      omega
    omega
  rw [he]
  exact isTDrop_add_of_admissible (by omega) hA hD 1

end AcceleratedCollatz
