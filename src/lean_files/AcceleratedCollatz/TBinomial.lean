-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TCount
import AcceleratedCollatz.TLex

/-!
  First-drop binomial identity for A100982. The C(p2(n) - 1, n - 1) bit strings of
  length p2(n) and Order n that start with 1 split uniquely at their first drop into
  an admissible PV of some Order 1 ≤ i ≤ n and an arbitrary rest of length
  p2(n) - p2(i) and Order n - i (`choose_eq_sum_admSet`).
-/

namespace AcceleratedCollatz

variable (n : ℕ)

/-- Bit strings of length L and Order w. -/
def wordSet (L w : ℕ) : Finset (List Bool) :=
  (allBits L).toFinset.filter (fun s => order s = w)

/-- Membership in `wordSet L w`. -/
theorem mem_wordSet (L w : ℕ) (s : List Bool) :
    s ∈ wordSet L w ↔ s.length = L ∧ order s = w := by
  simp [wordSet, mem_allBits]

/-- Words of `wordSet (L+1) (w+1)` starting with 1: 1 :: `wordSet L w`. -/
theorem wordSet_head_true (L w : ℕ) :
    (wordSet (L + 1) (w + 1)).filter (fun s => s.head? = some true) =
      (wordSet L w).image (List.cons true) := by
  ext s
  cases s with
  | nil =>
    simp
  | cons b t =>
    cases b
    · simp
    · simp [mem_wordSet, order_cons]

/-- No word of Order 0 starts with 1. -/
theorem wordSet_head_true_zero (L : ℕ) :
    (wordSet (L + 1) 0).filter (fun s => s.head? = some true) = ∅ := by
  ext s
  cases s with
  | nil =>
    simp
  | cons b t =>
    cases b
    · simp
    · simp [mem_wordSet, order_cons]

/-- Words of `wordSet (L+1) w` starting with 0: 0 :: `wordSet L w`. -/
theorem wordSet_head_false (L w : ℕ) :
    (wordSet (L + 1) w).filter (fun s => ¬ s.head? = some true) =
      (wordSet L w).image (List.cons false) := by
  ext s
  cases s with
  | nil =>
    simp [mem_wordSet]
  | cons b t =>
    cases b
    · simp [mem_wordSet, order_cons]
    · simp

/-- |`wordSet L w`| = C(L, w). -/
theorem card_wordSet : ∀ L w : ℕ, (wordSet L w).card = L.choose w
  | 0, w => by
    cases w with
    | zero =>
      rfl
    | succ w =>
      rfl
  | L + 1, w => by
    rw [← Finset.card_filter_add_card_filter_not (fun s => s.head? = some true),
      wordSet_head_false, Finset.card_image_of_injective _ (List.cons_injective), card_wordSet L w]
    cases w with
    | zero =>
      rw [wordSet_head_true_zero]
      simp
    | succ w =>
      rw [wordSet_head_true, Finset.card_image_of_injective _ (List.cons_injective),
        card_wordSet L w, Nat.choose_succ_succ']

/-- p2 is monotone. -/
theorem p2_of_mono {i n : ℕ} (h : i ≤ n) : p2_of i ≤ p2_of n :=
  monotone_nat_of_le_succ p2_of_le_succ h

theorem order_take_le (s : List Bool) (m : ℕ) : order (s.take m) ≤ order s := by
  have h := order_append (s.take m) (s.drop m)
  rw [List.take_append_drop] at h
  omega

/-- Strings of length p2(n) and Order n starting with 1. -/
def startWords (n : ℕ) : Finset (List Bool) :=
  (wordSet (p2_of n - 1) (n - 1)).image (List.cons true)

/-- Membership in `startWords n`. -/
theorem mem_startWords (hn : 1 ≤ n) (s : List Bool) :
    s ∈ startWords n ↔ (∃ u, s = true :: u) ∧ s.length = p2_of n ∧ order s = n := by
  have hp : 1 ≤ p2_of n := by
    simp [p2_of]
  simp only [startWords, Finset.mem_image, mem_wordSet]
  constructor
  · rintro ⟨u, ⟨hl, ho⟩, rfl⟩
    refine ⟨⟨u, rfl⟩, ?_, ?_⟩
    · rw [List.length_cons]
      omega
    · rw [order_cons]
      simp only [↓reduceIte]
      omega
  · rintro ⟨⟨u, rfl⟩, hl, ho⟩
    rw [List.length_cons] at hl
    rw [order_cons] at ho
    simp only [↓reduceIte] at ho
    exact ⟨u, ⟨by omega, by omega⟩, rfl⟩

/-- First-drop decomposition domain: Order i, admissible prefix, arbitrary rest. -/
def firstPassageSplits (n : ℕ) : Finset (Σ _ : ℕ, List Bool × List Bool) :=
  (Finset.Icc 1 n).sigma (fun i => admSet i ×ˢ wordSet (p2_of n - p2_of i) (n - i))

/-- Size of the first-passage domain. -/
theorem card_firstPassageSplits :
    (firstPassageSplits n).card =
      ∑ i ∈ Finset.Icc 1 n, (admSet i).card * (p2_of n - p2_of i).choose (n - i) := by
  rw [firstPassageSplits, Finset.card_sigma]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.card_product, card_wordSet]

/-- First drop of a string starting with 1, of length p2(n) and Order n. -/
theorem exists_first_drop (hn : 1 ≤ n) (s : List Bool) (hs : s ∈ startWords n) :
    ∃ m, 1 ≤ m ∧ m ≤ s.length ∧ Admissible (s.take m) := by
  rw [mem_startWords n hn] at hs
  obtain ⟨⟨u, rfl⟩, hl, ho⟩ := hs
  have hex : ∃ m, seqProduct ((true :: u).take m) < 1 := by
    refine ⟨(true :: u).length, ?_⟩
    rw [List.take_length, seqProduct_lt_one_iff, hl, ho]
    exact p2_of_spec n
  classical
  set m := Nat.find hex with hm_def
  have hspec : seqProduct ((true :: u).take m) < 1 := Nat.find_spec hex
  have hm1 : 1 ≤ m := by
    by_contra h0
    have hm0 : m = 0 := by omega
    rw [hm0, List.take_zero] at hspec
    simp [seqProduct] at hspec
  have hmle : m ≤ (true :: u).length := Nat.find_min' hex (by
    rw [List.take_length, seqProduct_lt_one_iff, hl, ho]
    exact p2_of_spec n)
  refine ⟨m, hm1, hmle, ?_, hspec⟩
  intro k hk1 hkl
  rw [List.length_take, min_eq_left hmle] at hkl
  have hnot : ¬ seqProduct ((true :: u).take k) < 1 := Nat.find_min hex hkl
  rw [List.take_take, min_eq_left hkl.le]
  have hne : (true :: u).take k ≠ [] := by
    intro h
    rw [List.take_eq_nil_iff] at h
    rcases h with h | h
    · omega
    · simp at h
  have hne1 := seqProduct_ne_one _ hne
  rcases lt_trichotomy (seqProduct ((true :: u).take k)) 1 with h | h | h
  · exact absurd h hnot
  · exact absurd h hne1
  · exact h

/-- A100982 binomial identity: C(p2(n) - 1, n - 1) = Σ_{i=1..n} a(i) C(p2(n) - p2(i), n - i). -/
theorem choose_eq_sum_admSet (hn : 1 ≤ n) :
    (p2_of n - 1).choose (n - 1) =
      ∑ i ∈ Finset.Icc 1 n, (admSet i).card * (p2_of n - p2_of i).choose (n - i) := by
  have hstart : (startWords n).card = (p2_of n - 1).choose (n - 1) := by
    rw [startWords, Finset.card_image_of_injective _ (List.cons_injective), card_wordSet]
  have himg : (firstPassageSplits n).image (fun p => p.2.1 ++ p.2.2) = startWords n := by
    ext s
    simp only [Finset.mem_image, firstPassageSplits, Finset.mem_sigma, Finset.mem_Icc,
      Finset.mem_product,
      mem_admSet, mem_wordSet, Sigma.exists, Prod.exists]
    constructor
    · rintro ⟨i, a, r, ⟨⟨hi1, hin⟩, ⟨hA, hoa⟩, hlr, hor⟩, rfl⟩
      rw [mem_startWords n hn]
      obtain ⟨u, rfl⟩ := admissible_cons_true a hA (by omega)
      refine ⟨⟨u ++ r, rfl⟩, ?_, ?_⟩
      · have hla := admissible_length _ hA
        rw [hoa] at hla
        have hmono := p2_of_mono hin
        rw [List.length_append, hla, hlr]
        omega
      · rw [order_append, hoa, hor]
        omega
    · intro hs
      obtain ⟨m, hm1, hml, hA⟩ := exists_first_drop n hn s hs
      rw [mem_startWords n hn] at hs
      obtain ⟨⟨u, rfl⟩, hl, ho⟩ := hs
      set a := (true :: u).take m with ha_def
      set r := (true :: u).drop m with hr_def
      have hsplit : a ++ r = true :: u := List.take_append_drop m _
      have hord := order_append a r
      rw [hsplit] at hord
      have hla := admissible_length a hA
      have hlen : a.length + r.length = (true :: u).length := by
        rw [← List.length_append, hsplit]
      have hoa1 : 1 ≤ order a := by
        obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le' hm1
        rw [ha_def, hk, List.take_succ_cons, order_cons]
        simp
      refine ⟨order a, a, r, ⟨⟨hoa1, by omega⟩, ⟨hA, rfl⟩, ?_, by omega⟩, hsplit⟩
      rw [hla] at hlen
      omega
  have hinj : Set.InjOn (fun p : (Σ _ : ℕ, List Bool × List Bool) => p.2.1 ++ p.2.2)
      (firstPassageSplits n) := by
    rintro ⟨i, a, r⟩ hp ⟨i', a', r'⟩ hq h
    simp only [firstPassageSplits, Finset.coe_sigma, Set.mem_sigma_iff, Finset.mem_coe,
      Finset.mem_Icc,
      Finset.mem_product, mem_admSet, mem_wordSet] at hp hq h
    obtain ⟨_, ⟨ha, hoa⟩, _⟩ := hp
    obtain ⟨_, ⟨ha', hoa'⟩, _⟩ := hq
    have hpre : a <+: a ++ r := List.prefix_append a r
    have hpre' : a' <+: a ++ r := by
      rw [h]
      exact List.prefix_append a' r'
    have haa : a = a' := by
      by_contra hne
      rcases le_total a.length a'.length with hle | hle
      · exact admissible_not_prefix a a' ha ha' hne
          (List.prefix_of_prefix_length_le hpre hpre' hle)
      · exact admissible_not_prefix a' a ha' ha (Ne.symm hne)
          (List.prefix_of_prefix_length_le hpre' hpre hle)
    subst haa
    have hrr : r = r' := List.append_cancel_left h
    subst hrr
    have hii : i = i' := by
      rw [← hoa, ← hoa']
    subst hii
    rfl
  rw [← hstart, ← himg, Finset.card_image_of_injOn hinj, card_firstPassageSplits]

end AcceleratedCollatz
