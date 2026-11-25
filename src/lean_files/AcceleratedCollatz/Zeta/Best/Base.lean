-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TParity
import AcceleratedCollatz.TCorrespondence
import AcceleratedCollatz.TRhoMax
import AcceleratedCollatz.TRhoLower
import AcceleratedCollatz.TSieve
import AcceleratedCollatz.TDrop
import AcceleratedCollatz.TCongruenceSplit
import AcceleratedCollatz.TAttrs

/-!
  The base of the best of the Order (`AcceleratedCollatz.Best`): the series' statements in the
  terms of the paper. The words are `List Bool`
  (true = an odd step), `order` counts the ones, `tStep` is T, `tBits x L` is the word of the
  first L steps of x, `rho` the constant of a word and `rhoMax n` the constant of the wall word
  of Order n. Paper, Chapters 2 and 3: Terras's affine form (`affine`), the class of a word
  (`mem_class_iff`), the constant of a concatenation (`rho_append`), the wall
  (`rho_le_wall`, `rho_eq_wall_iff`, `wall_eq_sum`, `rhoMax_le_mul`), the lower wall
  (`three_pow_le_rho_add'`,
  `rho_eq_lower_iff`) and admissibility in powers
  (`admissible_iff_pow`).
-/

namespace AcceleratedCollatz.Best

/-- Lemma 2.2 (Terras): 2^L T^L(x) = 3^n x + rho for the word of x's first L steps. -/
theorem affine (L x : ℕ) :
    2 ^ L * tStep^[L] x = 3 ^ order (tBits x L) * x + rho (tBits x L) :=
  tStep_iterate_nForm L x

/-- Lemma 2.2, the class: x's word starts with s iff 2^|s| divides 3^(order s) x + rho s. -/
theorem mem_class_iff (s : List Bool) (x : ℕ) :
    tBits x s.length = s ↔ 2 ^ s.length ∣ 3 ^ order s * x + rho s :=
  tBits_eq_iff s x

/-- The word of the first a + b steps. -/
theorem tBits_add' (x a b : ℕ) : tBits x (a + b) = tBits x a ++ tBits (tStep^[a] x) b :=
  tBits_add x a b

theorem tBits_take' (x n m : ℕ) (hm : m ≤ n) : (tBits x n).take m = tBits x m :=
  tBits_take x n m hm

theorem length_tBits' (x n : ℕ) : (tBits x n).length = n := length_tBits x n

/-- The constant of a concatenation. -/
theorem rho_append (a b : List Bool) :
    rho (a ++ b) = 3 ^ order b * rho a + 2 ^ a.length * rho b :=
  AcceleratedCollatz.rho_append a b

theorem order_append (a b : List Bool) : order (a ++ b) = order a + order b :=
  AcceleratedCollatz.order_append a b

theorem rho_pos_iff (s : List Bool) : 0 < rho s ↔ 0 < order s :=
  AcceleratedCollatz.rho_pos_iff s

/-- Admissible, in powers of 2 and 3. -/
theorem admissible_iff_pow (s : List Bool) :
    Admissible s ↔
      (∀ m < s.length, 1 ≤ m → 2 ^ m < 3 ^ order (s.take m)) ∧ 3 ^ order s < 2 ^ s.length :=
  AcceleratedCollatz.admissible_iff_pow s

/-- An admissible word has length p2 of its Order. -/
theorem admissible_length' (s : List Bool) (hA : Admissible s) : s.length = p2_of (order s) :=
  admissible_length s hA

/-- Theorem 3.2 (Terras), the wall: rho ≤ R(n). -/
theorem rho_le_wall {s : List Bool} (hA : Admissible s) : rho s ≤ rhoMax (order s) :=
  rho_le_rhoMax hA

/-- Theorem 3.2, equality only for the wall word (the first word of the Order). -/
theorem rho_eq_wall_iff {s : List Bool} (hA : Admissible s) :
    rho s = rhoMax (order s) ↔ s = firstWord (order s) :=
  rho_eq_rhoMax_iff hA

/-- The lower wall: 3^n - 2^n ≤ rho, for any word with n ones. -/
theorem three_pow_le_rho_add' (s : List Bool) : 3 ^ order s ≤ rho s + 2 ^ order s :=
  three_pow_le_rho_add s

/-- The lower wall, equality: exactly for the words with all their ones first. -/
theorem rho_eq_lower_iff (s : List Bool) :
    rho s + 2 ^ order s = 3 ^ order s ↔
      ∃ k, s = List.replicate (order s) true ++ List.replicate k false :=
  rho_add_eq_three_pow_iff s

/-- R(n) = sum over m < n of 3^(n-1-m) 2^(p2(m)-1). -/
theorem wall_eq_sum (n : ℕ) :
    rhoMax n = ∑ m ∈ Finset.range n, 3 ^ (n - 1 - m) * 2 ^ (p2_of m - 1) :=
  rhoMax_eq_sum n

/-- 2^(p2(m) - 1) ≤ 3^m, for every m. -/
theorem two_pow_p2_sub_one_le (m : ℕ) : 2 ^ (p2_of m - 1) ≤ 3 ^ m := by
  rw [p2_of, Nat.add_sub_cancel]
  exact Nat.pow_log_le_self 2 (by positivity)

/-- Proposition 3.4, the wall from above: R(n) ≤ n 3^(n-1). -/
theorem rhoMax_le_mul (n : ℕ) : rhoMax n ≤ n * 3 ^ (n - 1) := by
  rw [wall_eq_sum]
  calc ∑ m ∈ Finset.range n, 3 ^ (n - 1 - m) * 2 ^ (p2_of m - 1)
      ≤ ∑ _m ∈ Finset.range n, 3 ^ (n - 1) := by
        apply Finset.sum_le_sum
        intro m hm
        have hm' : m ≤ n - 1 := by
          have := Finset.mem_range.mp hm
          omega
        calc 3 ^ (n - 1 - m) * 2 ^ (p2_of m - 1) ≤ 3 ^ (n - 1 - m) * 3 ^ m :=
              Nat.mul_le_mul_left _ (two_pow_p2_sub_one_le m)
          _ = 3 ^ (n - 1) := by rw [← pow_add, Nat.sub_add_cancel hm']
    _ = n * 3 ^ (n - 1) := by simp

/-- 2^k < 3^n iff k < p2(n), for n ≥ 1. -/
theorem two_pow_lt_three_pow_iff' (k n : ℕ) (hn : 1 ≤ n) : 2 ^ k < 3 ^ n ↔ k < p2_of n :=
  two_pow_lt_three_pow_iff k n hn

end AcceleratedCollatz.Best
