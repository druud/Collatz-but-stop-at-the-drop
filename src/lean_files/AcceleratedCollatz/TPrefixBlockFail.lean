-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TPrefixBlockMod3

/-!
  E at the first block is false (A23, 2 Nov 2026). B, the word of 47, is admissible of Order
  34 and length 54, c(1B) = 31, and 31 d(B) < rho(B) (`not_prefixBlockBound_47`). B is the
  first block of the chain of the word of 31, 1 B 0, of Order 35, with c = 31, so
  c(w) > p(B_i) fails too (`not_lt_classId_31`). The drop of w itself is not touched.
-/

namespace AcceleratedCollatz

/-- The word of 47, up to its drop to 46. -/
def word47 : List Bool := tBits 47 54

theorem word47_admissible : Admissible word47 := by decide +kernel

theorem word31_admissible : Admissible (true :: word47 ++ [false]) := by decide +kernel

/-- c(1B) = 31 for B the word of 47. -/
theorem classId_cons_word47 : classId (true :: word47) = 31 :=
  (classId_unique _ 31 (by norm_num) (by decide +kernel) (by decide +kernel)).symm

theorem d_23_word47 : d_23 word47 = 1337216809815415 := by decide +kernel

theorem rho_word47 : rho word47 = 44834791551842521 := by decide +kernel

/-- E at the first block fails at the word of 47. -/
theorem not_prefixBlockBound_47 : ¬ PrefixBlockBound word47 := by
  rw [PrefixBlockBound, d_23_word47, rho_word47, classId_cons_word47]
  norm_num

/-- The word of 31 is 1 B 0, B the word of 47. -/
theorem tBits_31 : tBits 31 56 = true :: word47 ++ [false] := by decide +kernel

theorem classId_word31 : classId (true :: word47 ++ [false]) = 31 :=
  (classId_unique _ 31 (by norm_num) (by decide +kernel) (by decide +kernel)).symm

/-- c(w) d(B) < rho(B) for w the word of 31, B its first block. -/
theorem not_lt_classId_31 :
    ¬ rho word47 < d_23 word47 * classId (true :: word47 ++ [false]) := by
  rw [d_23_word47, rho_word47, classId_word31]
  norm_num

/-- Checks n <= 2 d(n) on lo <= n < lo + 2^k, by halving the range. -/
def allOrderLe : ℕ → ℕ → Bool
  | 0, lo => decide (lo ≤ 2 * (2 ^ (Nat.log2 (3 ^ lo) + 1) - 3 ^ lo))
  | k + 1, lo => allOrderLe k lo && allOrderLe k (lo + 2 ^ k)

theorem allOrderLe_spec (k lo : ℕ) (h : allOrderLe k lo = true) (n : ℕ) (h1 : lo ≤ n)
    (h2 : n < lo + 2 ^ k) : n ≤ 2 * (2 ^ (Nat.log2 (3 ^ n) + 1) - 3 ^ n) := by
  induction k generalizing lo with
  | zero =>
    have e : n = lo := by simp at h2; omega
    subst e
    simpa [allOrderLe] using h
  | succ k ih =>
    rw [allOrderLe, Bool.and_eq_true] at h
    rw [pow_succ] at h2
    by_cases hn : n < lo + 2 ^ k
    · exact ih lo h.1 h1 hn
    · exact ih _ h.2 (by omega) (by omega)

/-- n <= 2 d(n) for the Orders below 2^10 (A24). -/
theorem order_le_two_mul_d_table (n : ℕ) (hn : n < 2 ^ 10) :
    n ≤ 2 * (2 ^ (Nat.log2 (3 ^ n) + 1) - 3 ^ n) :=
  allOrderLe_spec 10 0 (by decide +kernel) n (Nat.zero_le _) (by omega)

/-- An admissible word of Order below 2^10 has n <= 2 d. -/
theorem order_le_two_mul_d_23 {B : List Bool} (hA : Admissible B) (hn : order B < 2 ^ 10) :
    order B ≤ 2 * d_23 B := by
  have h := order_le_two_mul_d_table (order B) hn
  rw [Nat.log2_eq_log_two] at h
  rw [d_23, admissible_length B hA]
  exact h

/-- E at the first block when T(c(1B)) is not c(B), for Orders below 2^10. -/
theorem prefixBlockBound_of_lt_small {B : List Bool} (hA : Admissible B)
    (hlt : classId B < tStep (classId (true :: B))) (hd : 0 < d_23 B)
    (hn : order B < 2 ^ 10) : PrefixBlockBound B :=
  prefixBlockBound_of_lt_admissible hA hlt hd (order_le_two_mul_d_23 hA hn)

end AcceleratedCollatz
