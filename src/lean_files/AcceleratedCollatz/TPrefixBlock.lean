-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TCongruenceSplit

/-!
  Backlog 11's E at the first block (generation 85): for an admissible block B, E says that
  the class id of the word 1 :: B lies above the cycle point of B, c(1B) d(B) > rho(B)
  (`PrefixBlockBound`; measured on every admissible word of Orders 2 to 31, never proved).
  When 3 c(1B) + 1 <= 2^(1 + |B|), c(B) = T(c(1B)) > c(1B) (`classId_tail_eq_tStep`), so E
  gives the drop of B's class, c(B) d(B) > rho(B) (`classDrop_of_prefixBlockBound`): E at
  the first block is at least ClassDrops for those B, which is why it stays open. The
  smallest ratio c(1B) d(B) / rho(B) over Orders 4 to 31 is 35/23, at B = 11010
  (`prefixBlockBound_11010`).
-/

namespace AcceleratedCollatz

/-- E at the first block: c(1B) d(B) > rho(B). -/
def PrefixBlockBound (B : List Bool) : Prop :=
  rho B < d_23 B * classId (true :: B)

/-- E at the first block gives the drop of B's class when 3 c(1B) + 1 <= 2^(1 + |B|). -/
theorem classDrop_of_prefixBlockBound {B : List Bool}
    (h3 : 3 * classId (true :: B) + 1 ≤ 2 ^ (true :: B).length) (hE : PrefixBlockBound B) :
    rho B < d_23 B * classId B := by
  have hc := classId_tail_eq_tStep B h3
  have hodd : classId (true :: B) % 2 = 1 := by
    have hb := tBits_classId (true :: B)
    simp only [List.length_cons, tBits, List.cons.injEq, decide_eq_true_eq] at hb
    exact hb.1
  rw [tStep_odd _ hodd] at hc
  have hle : classId (true :: B) ≤ classId B := by omega
  exact lt_of_lt_of_le hE (Nat.mul_le_mul_left _ hle)

/-- The smallest ratio of E at the first block: c(111010) = 7, d(11010) = 5,
    rho(11010) = 23, and 7 * 5 = 35 > 23. -/
theorem prefixBlockBound_11010 :
    classId [true, true, true, false, true, false] = 7 ∧
      d_23 [true, true, false, true, false] = 5 ∧
      rho [true, true, false, true, false] = 23 ∧
      PrefixBlockBound [true, true, false, true, false] := by
  have hc : classId [true, true, true, false, true, false] = 7 :=
    (classId_unique _ 7 (by norm_num) (by norm_num) (by decide)).symm
  have hd : d_23 [true, true, false, true, false] = 5 := by decide
  have hr : rho [true, true, false, true, false] = 23 := by decide
  exact ⟨hc, hd, hr, by rw [PrefixBlockBound, hd, hr, hc]; norm_num⟩

end AcceleratedCollatz
