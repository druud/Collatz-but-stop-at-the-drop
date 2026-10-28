-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TSubwordShort

/-!
  The admissible words counted by start and end together. A start y that stays above 1 (every
  nonempty prefix of y, y itself included, has level > 1; `StaysAbove`) is never cut by a first
  passage: an admissible a has y <+: a ++ r exactly when y <+: a
  (`prefix_append_iff_of_admissible`).
  So `suffix_first_passage` keeps its form with the start y carried along: with
  M = p2(n) - p2(i), k = n - i and J(y, x, i) the admissible words of Order i that start with
  y and end with x,
    C(p2(n) - 1 - |y| - |x|, n - order y - order x)
      = Σ_{i=1..n} [J(y, [], i) C(M - |x|, k - order x) if |x| ≤ M,
          else J(y, x.take (|x| - M), i) [order (x.drop (|x| - M)) = k]]
  for y = 1 :: y' and |y| + |x| ≤ p2(n) (`joint_first_passage`, `jointAdm_rec`). With y = 1
  and x = [] it is `choose_eq_sum_admSet`; the subword counts of length 4 and 5 across the end
  of a word (`occAdm_add_wrap_of_upperRecord`) need these with |y| ≤ 4 and |x| ≤ 4.
-/

namespace AcceleratedCollatz

/-- Every nonempty prefix of y, y itself included, has level > 1. -/
def StaysAbove (y : List Bool) : Prop :=
  ∀ m, 1 ≤ m → m ≤ y.length → 1 < seqProduct (y.take m)

/-- A start that stays above 1 is not cut by the end of an admissible word. -/
theorem prefix_append_iff_of_admissible {y a : List Bool} (hy : StaysAbove y)
    (hA : Admissible a) (r : List Bool) : y <+: a ++ r ↔ y <+: a := by
  constructor
  · intro h
    rcases (prefix_append_iff_cut y a r).mp h with h1 | ⟨hl, ht, -⟩
    · exact h1
    · exfalso
      have ha := ne_nil_of_admissible a hA
      have h1 : 1 ≤ a.length := List.length_pos_of_ne_nil ha
      have := hy a.length h1 hl.le
      rw [ht] at this
      exact absurd hA.lt_one (not_lt.mpr this.le)
  · exact fun h => h.trans (List.prefix_append a r)

/-- The admissible words of Order i that start with y and end with x. -/
def jointAdm (y x : List Bool) (i : ℕ) : ℕ :=
  ((admSet i).filter (fun a => y <+: a ∧ x <:+ a)).card

/-- The part of Order i in the first-passage identity for the start y and the end x. -/
def jointTerm (y x : List Bool) (n i : ℕ) : ℕ :=
  if x.length ≤ p2_of n - p2_of i then jointAdm y [] i * pc x (p2_of n - p2_of i) (n - i)
  else jointAdm y (x.take (x.length - (p2_of n - p2_of i))) i *
    if order (x.drop (x.length - (p2_of n - p2_of i))) = n - i then 1 else 0

/-- The words r of length M and Order k for which a ++ r ends with x. -/
theorem sum_suffix_append (x a : List Bool) (M k : ℕ) :
    (∑ r ∈ wordSet M k, if x <:+ a ++ r then 1 else 0) =
      if x.length ≤ M then pc x M k
      else (if x.take (x.length - M) <:+ a then 1 else 0) *
        if order (x.drop (x.length - M)) = k then 1 else 0 := by
  have hlen : ∀ r ∈ wordSet M k, r.length = M := fun r hr => ((mem_wordSet _ _ _).mp hr).1
  by_cases hxM : x.length ≤ M
  · rw [ite_eq_left hxM, ← card_filter_suffix, Finset.card_filter]
    apply Finset.sum_congr rfl
    intro r hr
    have hiff : x <:+ a ++ r ↔ x <:+ r := by
      rw [suffix_append_iff_cut, hlen r hr]
      simp [show ¬ M < x.length by omega]
    simp only [hiff]
  · rw [ite_eq_right hxM]
    have hcnt : ∀ r ∈ wordSet M k, (if x <:+ a ++ r then 1 else 0) =
        (if x.take (x.length - M) <:+ a then 1 else 0) *
          if r = x.drop (x.length - M) then 1 else 0 := by
      intro r hr
      have hiff : x <:+ a ++ r ↔ x.take (x.length - M) <:+ a ∧ r = x.drop (x.length - M) := by
        rw [suffix_append_iff_cut, hlen r hr]
        have hnr : ¬ x <:+ r := fun h => by
          have := h.length_le
          rw [hlen r hr] at this
          omega
        simp only [hnr, false_or, show M < x.length by omega, true_and]
        constructor
        · exact fun ⟨h1, h2⟩ => ⟨h2, h1.symm⟩
        · exact fun ⟨h1, h2⟩ => ⟨h2.symm, h1⟩
      simp only [hiff]
      by_cases h1 : x.take (x.length - M) <:+ a <;> by_cases h2 : r = x.drop (x.length - M) <;>
        simp [h1, h2]
    rw [Finset.sum_congr rfl hcnt, ← Finset.mul_sum, Finset.sum_ite_eq']
    congr 1
    have hmem : x.drop (x.length - M) ∈ wordSet M k ↔ order (x.drop (x.length - M)) = k := by
      rw [mem_wordSet, List.length_drop]
      exact ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩
    simp only [hmem]

/-- First-passage identity for the start y and the end x: the start words of Order n that
    start with y and end with x, cut at their first passage below 1. -/
theorem joint_first_passage {y : List Bool} (hy : StaysAbove y) (x : List Bool) (n : ℕ)
    (hn : 1 ≤ n) :
    ((startWords n).filter (fun w => y <+: w ∧ x <:+ w)).card =
      ∑ i ∈ Finset.Icc 1 n, jointTerm y x n i := by
  rw [Finset.card_filter, sum_startWords n hn]
  apply Finset.sum_congr rfl
  intro i _
  rw [jointTerm]
  set M := p2_of n - p2_of i
  set k := n - i
  have hsplit : ∀ a ∈ admSet i,
      (∑ r ∈ wordSet M k, if y <+: a ++ r ∧ x <:+ a ++ r then 1 else 0) =
      (if y <+: a then 1 else 0) * ∑ r ∈ wordSet M k, if x <:+ a ++ r then 1 else 0 := by
    intro a ha
    have hA := ((mem_admSet i a).mp ha).1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    simp only [prefix_append_iff_of_admissible hy hA r]
    by_cases h1 : y <+: a <;> by_cases h2 : x <:+ a ++ r <;> simp [h1, h2]
  rw [Finset.sum_congr rfl hsplit]
  simp only [sum_suffix_append]
  split_ifs with hxM
  · rw [← Finset.sum_mul, jointAdm, Finset.card_filter]
    simp [List.nil_suffix]
  · rw [jointAdm, Finset.card_filter, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    by_cases h1 : y <+: a <;> by_cases h2 : x.take (x.length - M) <:+ a <;> simp [h1, h2]
  · simp

/-- The words of length M and Order k that start with y and end with x, for |y| + |x| ≤ M. -/
theorem card_filter_prefix_suffix (y x : List Bool) (M k : ℕ) (hM : y.length + x.length ≤ M) :
    ((wordSet M k).filter (fun r => y <+: r ∧ x <:+ r)).card = pc (y ++ x) M k := by
  unfold pc
  rw [List.length_append, order_append]
  split_ifs with h
  · have himg : (wordSet M k).filter (fun r => y <+: r ∧ x <:+ r) =
        (wordSet (M - (y.length + x.length)) (k - (order y + order x))).image
          (fun t => y ++ (t ++ x)) := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_image, mem_wordSet]
      constructor
      · rintro ⟨⟨hl, ho⟩, ⟨u, rfl⟩, hx⟩
        rw [List.length_append] at hl
        rw [order_append] at ho
        have hxu : x <:+ u := by
          rcases (suffix_append_iff_cut x y u).mp hx with h1 | ⟨h1, -, -⟩
          · exact h1
          · omega
        obtain ⟨t, rfl⟩ := hxu
        rw [List.length_append] at hl
        rw [order_append] at ho
        exact ⟨t, ⟨by omega, by omega⟩, rfl⟩
      · rintro ⟨t, ⟨hl, ho⟩, rfl⟩
        refine ⟨⟨?_, ?_⟩, List.prefix_append y _, ?_⟩
        · simp only [List.length_append]
          omega
        · simp only [order_append]
          omega
        · exact (List.suffix_append t x).trans (List.suffix_append y _)
    have hinj : Function.Injective (fun t : List Bool => y ++ (t ++ x)) := fun t t' h =>
      List.append_left_injective x (List.append_right_injective y h)
    rw [himg, Finset.card_image_of_injective _ hinj, card_wordSet]
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro r hr ⟨⟨u, rfl⟩, hx⟩
    rw [mem_wordSet, List.length_append, order_append] at hr
    have hxu : x <:+ u := by
      rcases (suffix_append_iff_cut x y u).mp hx with h1 | ⟨h1, -, -⟩
      · exact h1
      · omega
    obtain ⟨t, rfl⟩ := hxu
    rw [order_append] at hr
    omega

/-- The start words of Order n that start with 1 :: y' and end with x, for
    |y'| + |x| < p2(n): C(p2(n) - 1 - |y'| - |x|, n - 1 - order y' - order x). -/
theorem card_joint_startWords (y' x : List Bool) (n : ℕ)
    (hl : y'.length + x.length < p2_of n) :
    ((startWords n).filter (fun w => (true :: y') <+: w ∧ x <:+ w)).card =
      pc (y' ++ x) (p2_of n - 1) (n - 1) := by
  rw [← card_filter_prefix_suffix y' x _ _ (by omega), startWords, Finset.filter_image,
    Finset.card_image_of_injective _ List.cons_injective]
  congr 1
  apply Finset.filter_congr
  intro u hu
  rw [mem_wordSet] at hu
  rw [List.cons_prefix_cons, List.suffix_cons_iff]
  simp only [true_and]
  constructor
  · rintro ⟨h1, h | h⟩
    · have := congrArg List.length h
      simp at this
      omega
    · exact ⟨h1, h⟩
  · exact fun ⟨h1, h2⟩ => ⟨h1, Or.inr h2⟩

/-- The part of Order n in `joint_first_passage` is J(y, x, n). -/
theorem jointTerm_self (y x : List Bool) (n : ℕ) : jointTerm y x n n = jointAdm y x n := by
  rw [jointTerm, Nat.sub_self, Nat.sub_self]
  rcases x with _ | ⟨b, x⟩
  · simp [pc, order]
  · rw [ite_eq_right (by simp)]
    simp [order]

/-- The admissible words of Order n that start with 1 :: y' (staying above 1) and end with x,
    |y'| + |x| < p2(n), from lower Orders. -/
theorem jointAdm_rec (y' x : List Bool) (hy : StaysAbove (true :: y')) (n : ℕ) (hn : 1 ≤ n)
    (hl : y'.length + x.length < p2_of n) :
    jointAdm (true :: y') x n =
      pc (y' ++ x) (p2_of n - 1) (n - 1) -
        ∑ i ∈ Finset.Ico 1 n, jointTerm (true :: y') x n i := by
  have h := joint_first_passage hy x n hn
  rw [card_joint_startWords y' x n hl, ← Finset.Ico_insert_right hn,
    Finset.sum_insert Finset.right_notMem_Ico, jointTerm_self] at h
  omega

/-! ## Check: Order 8 (words of length 13) -/

set_option linter.hashCommand false in
#guard jointAdm [true, true, false] [true, false] 8 = 7 ∧
  jointAdm [true, true, false] [false, false] 8 = 12 ∧ jointAdm [true, true, false] [] 8 = 19

end AcceleratedCollatz
