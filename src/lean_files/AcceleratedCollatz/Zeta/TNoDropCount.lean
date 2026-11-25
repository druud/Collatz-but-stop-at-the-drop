-- SPDX-License-Identifier: MIT
import Mathlib

/-!
  The words that never drop, counted (C122; zeta paper, Theorem thm:nodrop).

  A word `v : Fin k → Bool` (a one is `true`) never drops when each nonempty prefix, of length j
  with o ones, has level 3^o/2^j above 1: `2 ^ j < 3 ^ o` (`NoDrop`). `noDropCount k` is their
  number, S(k) in the paper. For a share a/(a+b) of ones with b ≤ a and 3^a ≤ 2^(a+b) (that is,
  a/(a+b) ≤ 1/log2 3), and k = (a+b) m,

    S(k) · a^(a m) · b^(b m) ≤ (a+b)^k        (`noDropCount_mul_le`),

  in natural numbers: a never-dropping word has at least a m ones (`le_ones_of_noDrop`), so its
  weight ∏ (a if one, b if zero) is at least a^(a m) b^(b m) (`weight_ge`), and the weights of
  all words add up to (a+b)^k (`sum_weight`). As a/(a+b) rises to 1/log2 3 this is
  S(k) ≤ 2^(k (H(p) + ε)); the 2-adic isometry and the dimensions are not formalized.
-/

namespace AcceleratedCollatz

open Finset

/-- The number of ones among the first `j` letters. -/
def onesUpTo {k : ℕ} (v : Fin k → Bool) (j : ℕ) : ℕ :=
  (univ.filter fun i : Fin k => i.val < j ∧ v i = true).card

/-- Every nonempty prefix has level above 1. -/
def NoDrop {k : ℕ} (v : Fin k → Bool) : Prop :=
  ∀ j, 1 ≤ j → j ≤ k → 2 ^ j < 3 ^ onesUpTo v j

instance {k : ℕ} (v : Fin k → Bool) : Decidable (NoDrop v) := by
  unfold NoDrop; infer_instance

/-- S(k): the words of length `k` that never drop. -/
def noDropCount (k : ℕ) : ℕ := (univ.filter fun v : Fin k → Bool => NoDrop v).card

/-- The weight of a word: `a` per one, `b` per zero. -/
def weight (a b : ℕ) {k : ℕ} (v : Fin k → Bool) : ℕ := ∏ i, if v i = true then a else b

theorem sum_weight (a b k : ℕ) : ∑ v : Fin k → Bool, weight a b v = (a + b) ^ k := by
  unfold weight
  rw [← Fintype.prod_sum (fun (_ : Fin k) (x : Bool) => if x = true then a else b)]
  simp

theorem onesUpTo_le {k : ℕ} (v : Fin k → Bool) (j : ℕ) : onesUpTo v j ≤ k := by
  unfold onesUpTo
  exact (card_filter_le _ _).trans (by simp)

theorem weight_eq {a b k : ℕ} (v : Fin k → Bool) :
    weight a b v = a ^ onesUpTo v k * b ^ (k - onesUpTo v k) := by
  unfold weight onesUpTo
  rw [prod_ite, prod_const, prod_const]
  have hc : (univ.filter fun i : Fin k => i.val < k ∧ v i = true)
      = univ.filter fun i : Fin k => v i = true := by
    ext i; simp
  have hs := card_filter_add_card_filter_not (s := (univ : Finset (Fin k)))
    (fun i : Fin k => v i = true)
  rw [hc]
  congr 2
  rw [card_univ, Fintype.card_fin] at hs
  omega

/-- A word that never drops has at least `a m` ones, when `3^a ≤ 2^(a+b)` and `k = (a+b) m`. -/
theorem le_ones_of_noDrop {a b m : ℕ} (h32 : 3 ^ a ≤ 2 ^ (a + b))
    {v : Fin ((a + b) * m) → Bool} (hv : NoDrop v) : a * m ≤ onesUpTo v ((a + b) * m) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  by_contra hlt
  replace hlt := Nat.lt_of_not_le hlt
  rcases Nat.eq_zero_or_pos (a + b) with hab | hab
  · have : a = 0 := by omega
    subst this; simp at hlt
  have hk : 1 ≤ (a + b) * m := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have h1 := hv ((a + b) * m) hk le_rfl
  have h2 : 3 ^ onesUpTo v ((a + b) * m) < 3 ^ (a * m) :=
    Nat.pow_lt_pow_right (by norm_num) hlt
  have h3 : 3 ^ (a * m) ≤ 2 ^ ((a + b) * m) := by
    rw [pow_mul, pow_mul]; exact Nat.pow_le_pow_left h32 m
  omega

/-- With `b ≤ a`, a weight with at least `a m` ones among `(a+b) m` letters is at least
`a^(a m) b^(b m)`. -/
theorem weight_ge {a b m : ℕ} (hba : b ≤ a) {v : Fin ((a + b) * m) → Bool}
    (ho : a * m ≤ onesUpTo v ((a + b) * m)) :
    a ^ (a * m) * b ^ (b * m) ≤ weight a b v := by
  rw [weight_eq]
  set o := onesUpTo v ((a + b) * m)
  have hok : o ≤ (a + b) * m := onesUpTo_le v _
  obtain ⟨d, hd⟩ : ∃ d, o = a * m + d := ⟨o - a * m, by omega⟩
  have hbm : b * m = ((a + b) * m - o) + d := by rw [add_mul] at hok ⊢; omega
  rw [hbm, hd, pow_add, pow_add]
  calc a ^ (a * m) * (b ^ ((a + b) * m - (a * m + d)) * b ^ d)
      = a ^ (a * m) * b ^ d * b ^ ((a + b) * m - (a * m + d)) := by ring
    _ ≤ a ^ (a * m) * a ^ d * b ^ ((a + b) * m - (a * m + d)) := by
        gcongr
    _ = _ := by ring

/-- The count of the words that never drop, in natural numbers (zeta paper, Theorem thm:nodrop):
`S(k) a^(a m) b^(b m) ≤ (a+b)^k` for `k = (a+b) m`, `b ≤ a` and `3^a ≤ 2^(a+b)`. -/
theorem noDropCount_mul_le {a b m : ℕ} (hba : b ≤ a) (h32 : 3 ^ a ≤ 2 ^ (a + b)) :
    noDropCount ((a + b) * m) * (a ^ (a * m) * b ^ (b * m)) ≤ (a + b) ^ ((a + b) * m) := by
  unfold noDropCount
  rw [← sum_weight a b ((a + b) * m), card_eq_sum_ones, sum_mul, one_mul]
  calc ∑ v ∈ univ.filter (fun v : Fin ((a + b) * m) → Bool => NoDrop v), a ^ (a * m) * b ^ (b * m)
      ≤ ∑ v ∈ univ.filter (fun v : Fin ((a + b) * m) → Bool => NoDrop v), weight a b v :=
        sum_le_sum fun v hv => weight_ge hba (le_ones_of_noDrop h32 (mem_filter.mp hv).2)
    _ ≤ ∑ v, weight a b v := sum_le_sum_of_subset (filter_subset _ _)

/-- Small values: S(0), ..., S(5) = 1, 1, 1, 2, 3, 4. -/
example : (List.range 6).map noDropCount = [1, 1, 1, 2, 3, 4] := by decide

end AcceleratedCollatz
