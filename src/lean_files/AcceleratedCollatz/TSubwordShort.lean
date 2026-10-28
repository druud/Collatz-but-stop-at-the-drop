-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TSubwordCycle

/-!
  Explicit counts of the subwords of length at most 3 at the upper record Orders. Every
  admissible word of Order n ≥ 2 starts with 11 (`prefix_true_true`) and ends in 0, so an
  occurrence across its end is a suffix count times a fixed start
  (`occAdm_short_of_upperRecord`), and the short suffix counts are a(n) (for 0,
  `sufAdm_false`), 0 (for a suffix ending in 1, `sufAdm_snoc_true`), and for 10 and 00 the
  parts of a(n) of `sufAdm_ten` (`sufAdm_ten_add`). With L = p2(n), a(n) = C(L, n)/L
  (`p2_mul_card_admSet`) and E = `sufAdm [1, 0] n` (a(n - 1) if p2(n) = p2(n - 1) + 1, else
  0), the occurrences of s in the admissible words of Order n are
  C(L - |s|, n - order s) less: a(n) for 01 and 011; a(n) - E for 001; E for 101; nothing for
  the other subwords of length 1 to 3.
-/

namespace AcceleratedCollatz

/-- An admissible word of Order at least 2 starts with 11. -/
theorem prefix_true_true {a : List Bool} (hA : Admissible a) (ho : 2 ≤ order a) :
    [true, true] <+: a := by
  obtain ⟨u, rfl⟩ := admissible_cons_true _ hA (by omega)
  rcases u with _ | ⟨b, u⟩
  · simp [order] at ho
  cases b
  · exfalso
    have hlen := admissible_length _ hA
    have hp : 4 ≤ p2_of (order (true :: false :: u)) := by
      have h2 := p2_of_mono ho
      have : p2_of 2 = 4 := by decide
      omega
    have h := hA.prefix_gt 2 (by norm_num) (by omega)
    norm_num [seqProduct, factor] at h
  · exact ⟨u, rfl⟩

/-- For a word that starts with 11, a start of at most 2 letters is a start of 11. -/
theorem prefix_iff_of_prefix_true_true {a y : List Bool} (h : [true, true] <+: a)
    (hy : y.length ≤ 2) : y <+: a ↔ y <+: [true, true] := by
  obtain ⟨t, rfl⟩ := h
  rw [prefix_append_iff_cut]
  constructor
  · rintro (h1 | ⟨h1, -⟩)
    · exact h1
    · simp at h1
      omega
  · exact Or.inl

/-- At an upper record Order n ≥ 2, for |s| ≤ 3: the occurrences of s in the admissible words
    of Order n, from C(p2(n) - |s|, n - order s) and suffix counts. -/
theorem occAdm_short_of_upperRecord {n : ℕ} (hn : 2 ≤ n) (hR : UpperRecord n)
    (s : List Bool) (hs3 : s.length ≤ 3) :
    occAdm s n + ∑ j ∈ Finset.Ioo 0 s.length,
        (if s.drop j <+: [true, true] then sufAdm (s.take j) n else 0) =
      pc s (p2_of n) n := by
  have hL : s.length ≤ p2_of n := by
    have := p2_of_mono hn
    have : p2_of 2 = 4 := by decide
    omega
  rw [← occAdm_add_wrap_of_upperRecord (by omega) hR s hL]
  congr 1
  simp only [cross]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_Ioo] at hj
  have hrow : ∀ a ∈ admSet n, (if s.take j <:+ a ∧ s.drop j <+: a then 1 else 0) =
      if s.drop j <+: [true, true] then (if s.take j <:+ a then 1 else 0) else 0 := by
    intro a ha
    obtain ⟨hA, ho⟩ := (mem_admSet n a).mp ha
    have hiff := prefix_iff_of_prefix_true_true (prefix_true_true hA (by omega))
      (show (s.drop j).length ≤ 2 by rw [List.length_drop]; omega)
    simp only [hiff]
    by_cases h1 : s.take j <:+ a <;> by_cases h2 : s.drop j <+: [true, true] <;> simp [h1, h2]
  rw [Finset.sum_congr rfl hrow]
  split_ifs with h
  · rw [sufAdm, Finset.card_filter]
  · simp

/-- Every admissible word ends in 0. -/
theorem sufAdm_false (n : ℕ) : sufAdm [false] n = (admSet n).card := by
  rw [sufAdm, Finset.filter_true_of_mem]
  intro a ha
  obtain ⟨hA, -⟩ := (mem_admSet n a).mp ha
  have hne : a ≠ [] := List.ne_nil_of_length_pos (by
    rw [admissible_length a hA]
    exact one_le_p2_of _)
  rw [← List.dropLast_append_getLast hne, admissible_last_false a hA hne]
  exact List.suffix_append _ _

/-- No admissible word ends in 1. -/
theorem sufAdm_snoc_true (x : List Bool) (n : ℕ) : sufAdm (x ++ [true]) n = 0 := by
  rw [sufAdm, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro a ha ⟨t, ht⟩
  obtain ⟨hA, -⟩ := (mem_admSet n a).mp ha
  have hne : a ≠ [] := by
    rw [← ht]
    simp
  have h := admissible_last_false a hA hne
  simp only [← ht, ← List.append_assoc, List.getLast_append_singleton] at h
  exact Bool.noConfusion h

/-- The admissible words of Order n ≥ 1 end in 10 or in 00. -/
theorem sufAdm_ten_add (n : ℕ) (hn : 1 ≤ n) :
    sufAdm [true, false] n + sufAdm [false, false] n = (admSet n).card := by
  rw [sufAdm, sufAdm]
  rw [← Finset.card_filter_add_card_filter_not (s := admSet n) (fun a => [true, false] <:+ a)]
  congr 2
  apply Finset.filter_congr
  intro a ha
  obtain ⟨hA, ho⟩ := (mem_admSet n a).mp ha
  have hl : 2 ≤ a.length := by
    rw [admissible_length a hA, ho]
    have := p2_of_mono hn
    have : p2_of 1 = 2 := by decide
    omega
  have hne : a ≠ [] := List.ne_nil_of_length_pos (by omega)
  have hsplit := List.dropLast_append_getLast hne
  rw [admissible_last_false a hA hne] at hsplit
  have hne' : a.dropLast ≠ [] := List.ne_nil_of_length_pos (by rw [List.length_dropLast]; omega)
  have hsplit' := List.dropLast_append_getLast hne'
  set c := a.dropLast.getLast hne'
  have ha : a = a.dropLast.dropLast ++ [c, false] := by
    rw [← hsplit]
    conv_lhs => rw [← hsplit']
    simp
  have key : ∀ x : List Bool, x.length = 2 → (x <:+ a ↔ x = [c, false]) := by
    intro x hx
    rw [ha, suffix_append_iff_cut]
    constructor
    · rintro (h | ⟨h, -⟩)
      · exact h.eq_of_length (by simp [hx])
      · simp at h
        omega
    · rintro rfl
      exact Or.inl (List.suffix_refl _)
  rw [key _ rfl, key _ rfl]
  cases c <;> simp

/-! ## Check: Order 5 (upper record; L = 8, a(5) = 7, E = 3) -/

set_option linter.hashCommand false in
#guard occAdm [false, true] 5 = 15 - 7 ∧ occAdm [false, true, true] 5 = 10 - 7 ∧
  occAdm [false, false, true] 5 = 5 - (7 - 3) ∧ occAdm [true, false, true] 5 = 10 - 3

end AcceleratedCollatz
