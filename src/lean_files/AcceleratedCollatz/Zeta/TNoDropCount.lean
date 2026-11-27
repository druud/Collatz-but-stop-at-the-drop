-- SPDX-License-Identifier: MIT
import Mathlib
import AcceleratedCollatz.Core

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

  The exact count (C135): with `firstDropCount j` the words of length j+1 that drop first at
  their end, S(k+1) + firstDropCount k = 2 S(k) (`noDropCount_succ`), so

    S(k) + Σ_{j<k} firstDropCount j · 2^(k-1-j) = 2^k        (`noDropCount_add_sum`),

  and a first drop at length j with o ones has j = p2(o) (`p2_of_firstDrop`), so these counts
  are the drop-word counts N(m) at the lengths p2(m).
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

/-- The words of length `k+1` that drop first at their end (every shorter nonempty
prefix above 1, the whole word at most 1). -/
def firstDropCount (k : ℕ) : ℕ :=
  (univ.filter fun v : Fin (k + 1) → Bool =>
    NoDrop (Fin.init v) ∧ 3 ^ onesUpTo v (k + 1) ≤ 2 ^ (k + 1)).card

/-- Below the last letter, a word and its `Fin.init` have the same ones. -/
theorem onesUpTo_init {k : ℕ} (v : Fin (k + 1) → Bool) {j : ℕ} (hj : j ≤ k) :
    onesUpTo v j = onesUpTo (Fin.init v) j := by
  unfold onesUpTo
  rw [card_filter, card_filter, Fin.sum_univ_castSucc]
  simp only [Fin.val_last, Nat.not_lt.mpr hj, false_and, ite_false, add_zero, Fin.val_castSucc,
    Fin.init]
  exact sum_congr rfl fun _ _ => by congr

/-- Never dropping at length `k+1`: never before, and above 1 at the end. -/
theorem noDrop_succ_iff {k : ℕ} (v : Fin (k + 1) → Bool) :
    NoDrop v ↔ NoDrop (Fin.init v) ∧ 2 ^ (k + 1) < 3 ^ onesUpTo v (k + 1) := by
  constructor
  · intro h
    refine ⟨fun j h1 hj => ?_, h _ (by omega) le_rfl⟩
    rw [← onesUpTo_init v hj]; exact h j h1 (by omega)
  · rintro ⟨h, hl⟩ j h1 hj
    rcases Nat.lt_or_ge j (k + 1) with hj' | hj'
    · rw [onesUpTo_init v (by omega)]; exact h j h1 (by omega)
    · obtain rfl : j = k + 1 := by omega
      exact hl

/-- A condition on the first `k` letters only is met by twice as many words of length `k+1`. -/
theorem card_init (k : ℕ) (P : (Fin k → Bool) → Prop) [DecidablePred P] :
    (univ.filter fun v : Fin (k + 1) → Bool => P (Fin.init v)).card
      = 2 * (univ.filter P).card := by
  rw [← card_map (Fin.snocEquiv (fun _ => Bool)).symm.toEmbedding]
  have : (univ.filter fun v : Fin (k + 1) → Bool => P (Fin.init v)).map
      (Fin.snocEquiv (fun _ => Bool)).symm.toEmbedding
      = (univ : Finset Bool) ×ˢ univ.filter P := by
    ext ⟨x, p⟩
    simp [Fin.snocEquiv, Fin.init_snoc]
  rw [this, card_product]; simp


/-- More letters, at least as many ones. -/
theorem onesUpTo_mono {k : ℕ} (v : Fin k → Bool) {i j : ℕ} (h : i ≤ j) :
    onesUpTo v i ≤ onesUpTo v j := by
  unfold onesUpTo
  exact card_le_card fun x hx => by
    simp only [mem_filter, mem_univ, true_and] at hx ⊢; exact ⟨by omega, hx.2⟩

/-- A word that drops first at length `k+1`, with `o` ones, has `k + 1 = p2(o)`. -/
theorem p2_of_firstDrop {k : ℕ} {v : Fin (k + 1) → Bool} (hv : NoDrop (Fin.init v))
    (hl : 3 ^ onesUpTo v (k + 1) ≤ 2 ^ (k + 1)) : p2_of (onesUpTo v (k + 1)) = k + 1 := by
  unfold p2_of
  congr 1
  set o := onesUpTo v (k + 1)
  have hlow : 2 ^ k ≤ 3 ^ o := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact Nat.one_le_pow _ _ (by norm_num)
    · have h1 := hv k hk le_rfl
      rw [← onesUpTo_init v le_rfl] at h1
      exact h1.le.trans (Nat.pow_le_pow_right (by norm_num) (onesUpTo_mono v (by omega)))
  have hne : 3 ^ o ≠ 2 ^ (k + 1) := by
    intro h
    have h3 : Odd (3 ^ o) := Odd.pow (by decide)
    rw [h] at h3
    exact (Nat.not_odd_iff_even.mpr ((Nat.even_pow' (by omega)).mpr even_two)) h3
  exact Nat.log_eq_of_pow_le_of_lt_pow hlow (lt_of_le_of_ne hl hne)

/-- S(k+1) + firstDropCount k = 2 S(k). -/
theorem noDropCount_succ (k : ℕ) :
    noDropCount (k + 1) + firstDropCount k = 2 * noDropCount k := by
  unfold noDropCount firstDropCount
  rw [← card_init k (fun w => NoDrop w)]
  rw [← card_union_of_disjoint]
  · congr 1; ext v; simp only [mem_filter, mem_union, mem_univ, true_and, noDrop_succ_iff]
    constructor
    · rintro (⟨a, _⟩ | ⟨a, _⟩) <;> exact a
    · intro a
      rcases lt_or_ge (2 ^ (k + 1)) (3 ^ onesUpTo v (k + 1)) with h | h
      · exact Or.inl ⟨a, h⟩
      · exact Or.inr ⟨a, h⟩
  · rw [disjoint_filter]; intro v _ h1 h2; rw [noDrop_succ_iff] at h1
    exact absurd h2.2 (not_le.mpr h1.2)

/-- The exact count (zeta paper, before Corollary cor:norate), in natural numbers:
`S(k) + Σ_{j<k} firstDropCount j · 2^(k-1-j) = 2^k`; with `p2_of_firstDrop` these are the
drop-word counts N(m)
at the lengths p2(m), so S(k) = 2^k - Σ_{p2(m) ≤ k} N(m) 2^(k - p2(m)). -/
theorem noDropCount_add_sum (k : ℕ) :
    noDropCount k + ∑ j ∈ range k, firstDropCount j * 2 ^ (k - 1 - j) = 2 ^ k := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [sum_range_succ, Nat.add_sub_cancel, Nat.sub_self, pow_zero, mul_one]
    have hs : ∑ j ∈ range k, firstDropCount j * 2 ^ (k - j)
        = 2 * ∑ j ∈ range k, firstDropCount j * 2 ^ (k - 1 - j) := by
      rw [mul_sum]; refine sum_congr rfl fun j hj => ?_
      have := mem_range.mp hj
      rw [show k - j = (k - 1 - j) + 1 by omega, pow_succ]; ring
    rw [hs, pow_succ]
    have := noDropCount_succ k
    omega

/-- Small values: S(0), ..., S(5) = 1, 1, 1, 2, 3, 4. -/
example : (List.range 6).map noDropCount = [1, 1, 1, 2, 3, 4] := by decide

/-- Small values: the first drops at the lengths 1, ..., 5 number 1, 1, 0, 1, 2 (the drop words
of Orders 0, 1, 2, 3 at the lengths 1, 2, 4, 5). -/
example : (List.range 5).map firstDropCount = [1, 1, 0, 1, 2] := by decide

end AcceleratedCollatz
