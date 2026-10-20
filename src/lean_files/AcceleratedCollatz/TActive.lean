-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TBinomialRange
import AcceleratedCollatz.TPersistent

/-!
  Active words by length (OEIS A076227). An active word of length k followed by
  one more letter is either active or admissible, and every active or admissible
  word of length k + 1 arises this way (`card_active_succ`). Admissible words of
  length p2(n) are those of Order n, so
  a(n) + A076227(p2(n)) = 2 A076227(p2(n) - 1) (`card_admSet_add_active`).
-/

namespace AcceleratedCollatz

/-- Active (persistent) words of length k. -/
def activeSet (k : ℕ) : Finset (List Bool) :=
  (allBits k).toFinset.filter Persistent

/-- Admissible words of length k. -/
def admLenSet (k : ℕ) : Finset (List Bool) :=
  (allBits k).toFinset.filter Admissible

/-- Membership in `activeSet k`. -/
theorem mem_activeSet (k : ℕ) (s : List Bool) :
    s ∈ activeSet k ↔ s.length = k ∧ Persistent s := by
  simp [activeSet, mem_allBits]

/-- Membership in `admLenSet k`. -/
theorem mem_admLenSet (k : ℕ) (s : List Bool) :
    s ∈ admLenSet k ↔ s.length = k ∧ Admissible s := by
  simp [admLenSet, mem_allBits]

/-- An active word followed by one letter is active or admissible. -/
theorem persistent_or_admissible_append (s : List Bool) (b : Bool) (hs : Persistent s) :
    Persistent (s ++ [b]) ∨ Admissible (s ++ [b]) := by
  have hpre : ∀ m, 1 ≤ m → m < (s ++ [b]).length → 1 < seqProduct ((s ++ [b]).take m) := by
    intro m hm1 hm
    rw [List.length_append, List.length_singleton] at hm
    rw [List.take_append_of_le_length (by omega)]
    exact hs m hm1 (by omega)
  have hne : s ++ [b] ≠ [] := by
    simp
  rcases lt_or_gt_of_ne (seqProduct_ne_one (s ++ [b]) hne) with hlt | hgt
  · right
    exact ⟨hpre, hlt⟩
  · left
    intro m hm1 hm
    rcases Nat.lt_or_ge m (s ++ [b]).length with h | h
    · exact hpre m hm1 h
    · have hm' : m = (s ++ [b]).length := by
        omega
      rw [hm', List.take_length]
      exact hgt

/-- Dropping the last letter of an active word leaves an active word. -/
theorem persistent_dropLast (t : List Bool) (ht : Persistent t) : Persistent t.dropLast := by
  intro m hm1 hm
  rw [List.length_dropLast] at hm
  rw [List.dropLast_eq_take, List.take_take, min_eq_left (by omega)]
  exact ht m hm1 (by omega)

/-- Dropping the last letter of an admissible word leaves an active word. -/
theorem persistent_dropLast_of_admissible (t : List Bool) (ht : Admissible t) :
    Persistent t.dropLast := by
  intro m hm1 hm
  rw [List.length_dropLast] at hm
  rw [List.dropLast_eq_take, List.take_take, min_eq_left (by omega)]
  exact ht.prefix_gt m hm1 (by omega)

/-- Active and admissible words are disjoint. -/
theorem not_persistent_of_admissible (t : List Bool) (hA : Admissible t) (hne : t ≠ []) :
    ¬ Persistent t := by
  intro hP
  have hlen : 1 ≤ t.length := List.length_pos_iff.mpr hne
  have h := hP t.length hlen le_rfl
  rw [List.take_length] at h
  have h2 := hA.lt_one
  linarith

/-- A076227 recursion: |active (k+1)| + |admissible (k+1)| = 2 |active k|. -/
theorem card_active_succ (k : ℕ) :
    (activeSet (k + 1)).card + (admLenSet (k + 1)).card = 2 * (activeSet k).card := by
  have hdisj : Disjoint (activeSet (k + 1)) (admLenSet (k + 1)) := by
    rw [Finset.disjoint_left]
    intro t ht ht'
    rw [mem_activeSet] at ht
    rw [mem_admLenSet] at ht'
    have hne : t ≠ [] := by
      intro h
      rw [h] at ht
      simp at ht
    exact not_persistent_of_admissible t ht'.2 hne ht.2
  have himg : (activeSet k ×ˢ (Finset.univ : Finset Bool)).image (fun p => p.1 ++ [p.2]) =
      activeSet (k + 1) ∪ admLenSet (k + 1) := by
    ext t
    simp only [Finset.mem_image, Finset.mem_product, Finset.mem_univ, and_true,
      Finset.mem_union, mem_activeSet, mem_admLenSet, Prod.exists]
    constructor
    · rintro ⟨s, b, ⟨hl, hs⟩, rfl⟩
      have hlen : (s ++ [b]).length = k + 1 := by
        simp [hl]
      rcases persistent_or_admissible_append s b hs with h | h
      · exact Or.inl ⟨hlen, h⟩
      · exact Or.inr ⟨hlen, h⟩
    · intro h
      have hlen : t.length = k + 1 := by
        rcases h with h | h
        · exact h.1
        · exact h.1
      have hne : t ≠ [] := by
        intro h0
        rw [h0] at hlen
        simp at hlen
      have hdl : Persistent t.dropLast := by
        rcases h with h | h
        · exact persistent_dropLast t h.2
        · exact persistent_dropLast_of_admissible t h.2
      refine ⟨t.dropLast, t.getLast hne, ⟨?_, hdl⟩, List.dropLast_append_getLast hne⟩
      rw [List.length_dropLast, hlen]
      rfl
  have hinj : Set.InjOn (fun p : List Bool × Bool => p.1 ++ [p.2])
      ↑(activeSet k ×ˢ (Finset.univ : Finset Bool)) := by
    rintro ⟨s, b⟩ _ ⟨s', b'⟩ _ h
    obtain ⟨h1, h2⟩ := List.append_inj' h rfl
    exact Prod.ext h1 (List.singleton_inj.mp h2)
  rw [← Finset.card_union_of_disjoint hdisj, ← himg, Finset.card_image_of_injOn hinj,
    Finset.card_product, Finset.card_univ, Fintype.card_bool]
  ring

/-- p2 is strictly increasing. -/
theorem p2_of_lt_succ (k : ℕ) : p2_of k < p2_of (k + 1) := by
  have hp : p2_of k = (p2_of k - 1) + 1 := by
    have := one_le_p2_of k
    omega
  have h1 : 2 ^ (p2_of k - 1) ≤ 3 ^ k := p2_of_spec_lower k
  have h2 : 3 ^ (k + 1) < 2 ^ p2_of (k + 1) := p2_of_spec (k + 1)
  have h3 : 2 ^ p2_of k < 2 ^ p2_of (k + 1) := by
    rw [hp, pow_succ]
    rw [pow_succ] at h2
    omega
  exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp h3

/-- The admissible words of length p2(n) are exactly those of Order n. -/
theorem admLenSet_p2 (n : ℕ) : admLenSet (p2_of n) = admSet n := by
  ext s
  rw [mem_admLenSet, mem_admSet]
  constructor
  · rintro ⟨hl, hA⟩
    refine ⟨hA, ?_⟩
    have hlen := admissible_length s hA
    rw [hl] at hlen
    exact (StrictMono.injective (strictMono_nat_of_lt_succ p2_of_lt_succ) hlen).symm
  · rintro ⟨hA, ho⟩
    refine ⟨?_, hA⟩
    rw [admissible_length s hA, ho]

/-- a(n) + A076227(p2(n)) = 2 A076227(p2(n) - 1). -/
theorem card_admSet_add_active (n : ℕ) :
    (admSet n).card + (activeSet (p2_of n)).card = 2 * (activeSet (p2_of n - 1)).card := by
  have hp : p2_of n = (p2_of n - 1) + 1 := by
    have := one_le_p2_of n
    omega
  rw [← card_active_succ, ← hp, admLenSet_p2, add_comm]

-- The first terms of A076227: 1, 1, 1, 2, 3, 4, 8, 13, 19.
set_option linter.hashCommand false in
#guard (List.range 9).map (fun k => (activeSet k).card) = [1, 1, 1, 2, 3, 4, 8, 13, 19]

end AcceleratedCollatz
