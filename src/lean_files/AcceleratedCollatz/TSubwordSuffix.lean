-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TSubword
import AcceleratedCollatz.TActive

/-!
  Two suffix counts of the admissible words, from the last-1 decomposition of `TPersistent`.
  An admissible word of Order n that ends in 1 0^j is a persistent word of Order n - 1 and
  length p2(n) - 1 - j, completed (`sufAdm_one_zeros`). The persistent words of Order k and
  the longest length p2(k) - 1 are the admissible words of Order k without their last 0
  (`card_persLen_max`); when p2(k + 1) = p2(k) + 1 those of length p2(k) - 2 are as many
  (`card_persLen_pred`: a longest one cannot end in 1). So, with a(n) = |admSet n|:
  the words of Order n ending in 10 number a(n - 1) if p2(n) = p2(n - 1) + 1, else 0
  (`sufAdm_ten`), and those ending in 100 number a(n - 1) for every n ≥ 2 (`sufAdm_hundred`).
-/

namespace AcceleratedCollatz

/-- Persistent words of Order k and length ℓ. -/
def persLen (k ℓ : ℕ) : Finset (List Bool) := (persSet k).filter (fun p => p.length = ℓ)

/-- Membership in `persLen k ℓ`. -/
theorem mem_persLen (k ℓ : ℕ) (p : List Bool) :
    p ∈ persLen k ℓ ↔ Persistent p ∧ order p = k ∧ p.length = ℓ := by
  simp [persLen, mem_persSet, and_assoc]

/-- A final 0 leaves the Order alone. -/
theorem order_snoc_false (p : List Bool) : order (p ++ [false]) = order p := by
  rw [order_append]
  rfl

/-- p2 grows by at most 2 from one Order to the next. -/
theorem p2_of_succ_le (k : ℕ) : p2_of (k + 1) ≤ p2_of k + 2 := by
  by_contra h
  have h1 : 2 ^ (p2_of k + 2) < 3 ^ (k + 1) :=
    (two_pow_lt_three_pow_iff _ _ (by omega)).mpr (by omega)
  have h2 := p2_of_spec k
  rw [pow_add, pow_succ] at h1
  norm_num at h1
  omega

/-- The persistent words of Order k and the longest length p2(k) - 1 are the admissible
    words of Order k without their last 0. -/
theorem image_persLen_max (k : ℕ) :
    (persLen k (p2_of k - 1)).image (· ++ [false]) = admSet k := by
  ext s
  simp only [Finset.mem_image, mem_persLen, mem_admSet]
  constructor
  · rintro ⟨p, ⟨hp, ho, hl⟩, rfl⟩
    have hp1 := one_le_p2_of k
    refine ⟨⟨?_, ?_⟩, by rw [order_snoc_false, ho]⟩
    · intro m hm1 hm
      rw [List.length_append, List.length_singleton] at hm
      rw [List.take_append_of_le_length (by omega)]
      exact hp m hm1 (by omega)
    · rw [seqProduct_lt_one_iff, order_snoc_false, ho, List.length_append,
        List.length_singleton, hl, show p2_of k - 1 + 1 = p2_of k by omega]
      exact p2_of_spec k
  · rintro ⟨hA, ho⟩
    have hlen := admissible_length s hA
    have hne : s ≠ [] := List.ne_nil_of_length_pos (by have := one_le_p2_of (order s); omega)
    have hs : s.dropLast ++ [false] = s := by
      conv_rhs => rw [← List.dropLast_append_getLast hne]
      rw [admissible_last_false s hA hne]
    refine ⟨s.dropLast, ⟨persistent_dropLast_of_admissible s hA, ?_, ?_⟩, hs⟩
    · have h := order_snoc_false s.dropLast
      rw [hs] at h
      omega
    · rw [List.length_dropLast, hlen, ho]

/-- So they are a(k) in number. -/
theorem card_persLen_max (k : ℕ) : (persLen k (p2_of k - 1)).card = (admSet k).card := by
  rw [← image_persLen_max, Finset.card_image_of_injective _ (List.append_left_injective [false])]

/-- When p2(k + 1) = p2(k) + 1, the persistent words of Order k ≥ 1 and length p2(k) - 2 are
    as many as those of the longest length: a longest one ends in 0, as one ending in 1
    would need a level below 8/9 before that 1. -/
theorem card_persLen_pred (k : ℕ) (hk : 1 ≤ k) (hj : p2_of (k + 1) = p2_of k + 1) :
    (persLen k (p2_of k - 2)).card = (persLen k (p2_of k - 1)).card := by
  have hp2 : 2 ≤ p2_of k := by
    have := p2_of_mono hk
    have := p2_of_lt_succ 0
    have := one_le_p2_of 0
    simp only [zero_add] at *
    omega
  have himg : (persLen k (p2_of k - 2)).image (· ++ [false]) = persLen k (p2_of k - 1) := by
    ext q
    simp only [Finset.mem_image, mem_persLen]
    constructor
    · rintro ⟨p, ⟨hp, ho, hl⟩, rfl⟩
      refine ⟨?_, by rw [order_snoc_false, ho], by
        rw [List.length_append, List.length_singleton]; omega⟩
      intro m hm1 hm
      rw [List.length_append, List.length_singleton] at hm
      rcases Nat.lt_or_ge m (p.length + 1) with hlt | hge
      · rw [List.take_append_of_le_length (by omega)]
        exact hp m hm1 (by omega)
      · rw [show m = (p ++ [false]).length by simp; omega, List.take_length,
          one_lt_seqProduct_iff, order_snoc_false, ho, List.length_append,
          List.length_singleton, hl, show p2_of k - 2 + 1 = p2_of k - 1 by omega]
        exact two_pow_pred_p2_lt k hk
    · rintro ⟨hq, ho, hl⟩
      have hne : q ≠ [] := List.ne_nil_of_length_pos (by omega)
      have hsplit := List.dropLast_append_getLast hne
      have hlast : q.getLast hne = false := by
        by_contra hb
        simp only [Bool.not_eq_false] at hb
        rw [hb] at hsplit
        have hoq : order q.dropLast + 1 = k := by
          have h1 := order_append q.dropLast [true]
          rw [hsplit] at h1
          have h2 : order [true] = 1 := rfl
          omega
        have hlq : q.dropLast.length + 1 = p2_of k - 1 := by
          rw [List.length_dropLast]
          omega
        have hpre : 2 ^ q.dropLast.length ≤ 3 ^ order q.dropLast := by
          rcases Nat.eq_zero_or_pos q.dropLast.length with h0 | hpos
          · rw [h0]
            exact Nat.one_le_pow _ _ (by norm_num)
          · have h := hq q.dropLast.length hpos (by omega)
            have hq' : q.take q.dropLast.length = q.dropLast := by
              rw [List.length_dropLast, List.dropLast_eq_take]
            rw [hq', one_lt_seqProduct_iff] at h
            exact h.le
        have hjump := p2_of_spec (k + 1)
        rw [hj] at hjump
        have e1 : 3 ^ (k + 1) = 3 ^ order q.dropLast * 9 := by
          rw [← hoq]
          ring
        have e2 : 2 ^ (p2_of k + 1) = 2 ^ q.dropLast.length * 8 := by
          rw [show p2_of k + 1 = q.dropLast.length + 3 by omega]
          ring
        rw [e1, e2] at hjump
        omega
      rw [hlast] at hsplit
      refine ⟨q.dropLast, ⟨persistent_dropLast q hq, ?_, ?_⟩, hsplit⟩
      · have h := order_snoc_false q.dropLast
        rw [hsplit] at h
        omega
      · rw [List.length_dropLast]
        omega
  rw [← himg, Finset.card_image_of_injective _ (List.append_left_injective [false])]

/-- The admissible words of Order n ≥ 1 that end in 1 0^j, j + 1 ≤ p2(n): the persistent
    words of Order n - 1 and length p2(n) - 1 - j, completed. -/
theorem sufAdm_one_zeros (n j : ℕ) (hn : 1 ≤ n) (hj : j + 1 ≤ p2_of n) :
    sufAdm (true :: List.replicate j false) n = (persLen (n - 1) (p2_of n - 1 - j)).card := by
  have hn1 : n - 1 + 1 = n := by omega
  have himg : (persLen (n - 1) (p2_of n - 1 - j)).image (complete (n - 1)) =
      (admSet n).filter (fun a => (true :: List.replicate j false) <:+ a) := by
    ext s
    simp only [Finset.mem_image, Finset.mem_filter, mem_persLen, mem_admSet]
    constructor
    · rintro ⟨p, ⟨hp, ho, hl⟩, rfl⟩
      have h := admissible_complete p hp
      rw [ho, hn1] at h
      refine ⟨h, ?_⟩
      rw [complete, hn1, hl, show p2_of n - (p2_of n - 1 - j) - 1 = j by omega]
      exact List.suffix_append _ _
    · rintro ⟨⟨hA, ho⟩, ⟨a, rfl⟩⟩
      have hlen := admissible_length _ hA
      rw [ho] at hlen
      simp only [List.length_append, List.length_cons, List.length_replicate] at hlen
      have hoa : order a = n - 1 := by
        rw [order_append, order_cons, order_replicate_false] at ho
        simp only [↓reduceIte] at ho
        omega
      refine ⟨a, ⟨?_, hoa, by omega⟩, ?_⟩
      · intro m hm1 hml
        have hms : m < (a ++ true :: List.replicate j false).length := by
          simp only [List.length_append, List.length_cons, List.length_replicate]
          omega
        have h := hA.1 m hm1 hms
        rwa [List.take_append_of_le_length hml] at h
      · rw [complete, hn1, show p2_of n - a.length - 1 = j by omega]
  rw [sufAdm, ← himg, Finset.card_image_of_injOn]
  intro p hp p' hp' h
  rw [Finset.mem_coe, mem_persLen] at hp hp'
  simp only [complete, hp.2.2, hp'.2.2] at h
  exact List.append_cancel_right h

/-- The admissible words of Order n ≥ 1 that end in 10: a(n - 1) if p2(n) = p2(n - 1) + 1,
    else none. -/
theorem sufAdm_ten (n : ℕ) (hn : 1 ≤ n) :
    sufAdm [true, false] n =
      if p2_of n = p2_of (n - 1) + 1 then (admSet (n - 1)).card else 0 := by
  have hp := p2_of_lt_succ (n - 1)
  have := one_le_p2_of (n - 1)
  rw [show n - 1 + 1 = n by omega] at hp
  have h : sufAdm [true, false] n = (persLen (n - 1) (p2_of n - 1 - 1)).card :=
    sufAdm_one_zeros n 1 hn (by omega)
  rw [h]
  split_ifs with hj
  · rw [show p2_of n - 1 - 1 = p2_of (n - 1) - 1 by omega, card_persLen_max]
  · rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro p hp'
    rw [mem_persLen] at hp'
    have := length_lt_p2_of_persistent p hp'.1
    rw [hp'.2.1] at this
    omega

/-- The admissible words of Order n ≥ 2 that end in 100: a(n - 1). -/
theorem sufAdm_hundred (n : ℕ) (hn : 2 ≤ n) :
    sufAdm [true, false, false] n = (admSet (n - 1)).card := by
  have hp := p2_of_lt_succ (n - 1)
  have hle := p2_of_succ_le (n - 1)
  rw [show n - 1 + 1 = n by omega] at hp hle
  have h1 : 2 ≤ p2_of (n - 1) := by
    have := p2_of_mono (show 1 ≤ n - 1 by omega)
    have := p2_of_lt_succ 0
    have := one_le_p2_of 0
    simp only [zero_add] at *
    omega
  have h : sufAdm [true, false, false] n = (persLen (n - 1) (p2_of n - 1 - 2)).card :=
    sufAdm_one_zeros n 2 (by omega) (by omega)
  rw [h]
  rcases (show p2_of n = p2_of (n - 1) + 1 ∨ p2_of n = p2_of (n - 1) + 2 by omega) with hj | hj
  · rw [show p2_of n - 1 - 2 = p2_of (n - 1) - 2 by omega,
      card_persLen_pred (n - 1) (by omega) (by rw [show n - 1 + 1 = n by omega]; exact hj),
      card_persLen_max]
  · rw [show p2_of n - 1 - 2 = p2_of (n - 1) - 1 by omega, card_persLen_max]

end AcceleratedCollatz
