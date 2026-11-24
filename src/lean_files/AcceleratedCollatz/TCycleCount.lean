-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TSubwordCycle
import AcceleratedCollatz.TRulerRecord
import AcceleratedCollatz.TDrop

/-!
  The mass per Order (C83): a(n) = A100982(n) from binomials alone.

  A word v is a ladder word when every proper prefix has a level (`lv`) above the level of the
  whole word. Every word of length p2(n) and Order n is a ladder word v of the same kind turned
  back by r, for exactly one pair (v, r) with r ∈ `tset v` (the first ladder rotation of the word
  is at r; it exists at the lowest level, `exists_ladder_rotate`), so
  C(p2(n), n) = Σ_{v ∈ ladSet n} |tset v| (`card_wordSet_eq_sum_tset`). For an admissible v,
  tset v is all of 0 .. p2(n) - 1 (`tset_of_admissible`); a ladder word that is not admissible
  splits at its first level below 1 into an admissible word d of a split Order m and a ladder
  word w of Order n - m (`exists_ladder_split`), and tset (d ++ w) = tset w (`tset_append`). So

    C(p2(n), n) = p2(n) a(n) + Σ_{m} a(m) C(p2(n - m), n - m)   (`choose_p2_eq_split`),

  the sum over the split Orders 1 ≤ m < n with p2(m) + p2(n - m) = p2(n), that is with
  2^p2(m) 3^n < 2^p2(n) 3^m (`mem_splitOrders_iff`). The sum is A400061(n) (OEIS).
-/

namespace AcceleratedCollatz

/-- The level of the first i letters. -/
abbrev lv (v : List Bool) (i : ℕ) : ℚ := seqProduct (v.take i)

theorem lv_pos (v : List Bool) (i : ℕ) : 0 < lv v i := seqProduct_pos _

theorem lv_zero (v : List Bool) : lv v 0 = 1 := by simp [lv, seqProduct]

theorem lv_length (v : List Bool) : lv v v.length = seqProduct v := by simp [lv]

/-- Distinct prefixes have distinct levels. -/
theorem lv_inj {v : List Bool} {i j : ℕ} (hi : i ≤ v.length) (hj : j ≤ v.length)
    (h : lv v i = lv v j) : i = j := by
  have h1 := seqProduct_mul_pow (v.take i)
  have h2 := seqProduct_mul_pow (v.take j)
  rw [List.length_take, min_eq_left hi] at h1
  rw [List.length_take, min_eq_left hj] at h2
  have key : (3 : ℚ) ^ order (v.take i) * 2 ^ j = 3 ^ order (v.take j) * 2 ^ i := by
    rw [← h1, ← h2]; unfold lv at h; rw [h]; ring
  have keyN : 3 ^ order (v.take i) * 2 ^ j = 3 ^ order (v.take j) * 2 ^ i := by
    exact_mod_cast key
  rcases lt_trichotomy (order (v.take i)) (order (v.take j)) with hlt | heq | hgt
  · exact absurd keyN (three_pow_mul_two_pow_ne hlt _ _)
  · rw [heq] at keyN
    have : 2 ^ j = 2 ^ i := by
      have h3 : 0 < 3 ^ order (v.take j) := by positivity
      exact Nat.eq_of_mul_eq_mul_left h3 keyN
    exact (Nat.pow_right_injective (le_refl 2) this).symm
  · exact absurd keyN.symm (three_pow_mul_two_pow_ne hgt _ _)

/-- A ladder word: its whole level lies below the level of every proper prefix (the empty one
    too). -/
def Ladder (v : List Bool) : Prop := ∀ i < v.length, seqProduct v < lv v i

instance (v : List Bool) : Decidable (Ladder v) := by unfold Ladder; infer_instance

/-- The prefixes of a rotation, in levels of the word itself. -/
theorem lv_rotate_le {u : List Bool} {r t : ℕ} (hr : r ≤ u.length) (ht : t ≤ u.length - r) :
    lv (u.rotate r) t * lv u r = lv u (r + t) := by
  unfold lv
  rw [List.rotate_eq_drop_append_take hr, List.take_append_of_le_length (by simp; omega),
    List.take_add, seqProduct_append, mul_comm]

theorem lv_rotate_gt {u : List Bool} {r t : ℕ} (hr : r ≤ u.length) (ht : u.length - r < t)
    (htL : t ≤ u.length) :
    lv (u.rotate r) t * lv u r = seqProduct u * lv u (t - (u.length - r)) := by
  unfold lv
  have hsplit : u = u.take r ++ u.drop r := (List.take_append_drop r u).symm
  have hP : seqProduct u = seqProduct (u.take r) * seqProduct (u.drop r) := by
    conv_lhs => rw [hsplit]
    rw [seqProduct_append]
  rw [List.rotate_eq_drop_append_take hr, List.take_append, List.length_drop,
    List.take_of_length_le (by simp; omega), List.take_take, min_eq_left (by omega),
    seqProduct_append, hP]
  ring


/-- A rotation is a ladder word iff its start lies below all earlier prefixes, and the whole
    level from there stays below all later ones. -/
theorem ladder_rotate_iff {u : List Bool} {r : ℕ} (hr : r < u.length) :
    Ladder (u.rotate r) ↔ (∀ j < r, lv u r < lv u j) ∧
      ∀ s, r ≤ s → s < u.length → lv u r * seqProduct u < lv u s := by
  set L := u.length with hL
  have hPr := lv_pos u r
  have hP := seqProduct_pos u
  unfold Ladder
  rw [List.length_rotate, seqProduct_rotate]
  constructor
  · intro h
    refine ⟨fun j hj => ?_, fun s hs1 hs2 => ?_⟩
    · rcases Nat.eq_zero_or_pos j with rfl | hj0
      · -- t = L - r
        have ht := h (L - r) (by omega)
        have e := lv_rotate_le (u := u) (r := r) (t := L - r) hr.le le_rfl
        rw [show r + (L - r) = L by omega, hL, lv_length] at e
        rw [lv_zero]
        have : seqProduct u * lv u r < lv (u.rotate r) (L - r) * lv u r :=
          mul_lt_mul_of_pos_right ht hPr
        rw [e] at this
        nlinarith
      · have ht := h (j + (L - r)) (by omega)
        have e := lv_rotate_gt (u := u) (r := r) (t := j + (L - r)) hr.le (by omega) (by omega)
        rw [show j + (L - r) - (L - r) = j by omega] at e
        have : seqProduct u * lv u r < lv (u.rotate r) (j + (L - r)) * lv u r :=
          mul_lt_mul_of_pos_right ht hPr
        rw [e] at this
        nlinarith
    · have ht := h (s - r) (by omega)
      have e := lv_rotate_le (u := u) (r := r) (t := s - r) hr.le (by omega)
      rw [show r + (s - r) = s by omega] at e
      have : seqProduct u * lv u r < lv (u.rotate r) (s - r) * lv u r :=
        mul_lt_mul_of_pos_right ht hPr
      rw [e] at this
      linarith
  · rintro ⟨h1, h2⟩ t ht
    rcases Nat.lt_or_ge (L - r) t with hgt | hle
    · have e := lv_rotate_gt (u := u) (r := r) (t := t) hr.le hgt ht.le
      have hj := h1 (t - (L - r)) (by omega)
      have : seqProduct u * lv u r < lv (u.rotate r) t * lv u r := by
        rw [e]; exact mul_lt_mul_of_pos_left hj hP
      exact lt_of_mul_lt_mul_right this hPr.le
    · have e := lv_rotate_le (u := u) (r := r) (t := t) hr.le hle
      have : seqProduct u * lv u r < lv (u.rotate r) t * lv u r := by
        rw [e]
        rcases Nat.lt_or_ge (r + t) L with hs | hs
        · rw [mul_comm]; exact h2 (r + t) (by omega) hs
        · -- r + t = L, so r > 0 (t < L)
          have hrt : r + t = L := by omega
          rw [hrt, hL, lv_length]
          have h0 := h1 0 (by omega)
          rw [lv_zero] at h0
          nlinarith
      exact lt_of_mul_lt_mul_right this hPr.le

/-- Lemma E: a rotation of a ladder word, by 0 < r < L, is a ladder word iff level r is below all
    earlier levels. -/
theorem ladder_rotate_iff_of_ladder {v : List Bool} (hv : Ladder v) {r : ℕ} (h0 : 0 < r)
    (hr : r < v.length) : Ladder (v.rotate r) ↔ ∀ j < r, lv v r < lv v j := by
  rw [ladder_rotate_iff hr]
  refine ⟨fun h => h.1, fun h => ⟨h, fun s _ hs => ?_⟩⟩
  have h1 : lv v r < 1 := by have := h 0 h0; rwa [lv_zero] at this
  calc lv v r * seqProduct v < 1 * seqProduct v :=
        mul_lt_mul_of_pos_right h1 (seqProduct_pos _)
    _ = seqProduct v := one_mul _
    _ < lv v s := hv s hs

/-- A word with level below 1 has a ladder rotation (at its lowest level). -/
theorem exists_ladder_rotate {u : List Bool} (hu : u ≠ []) (hsp : seqProduct u < 1) :
    ∃ r, r < u.length ∧ Ladder (u.rotate r) := by
  have hL : 0 < u.length := List.length_pos_iff.mpr hu
  obtain ⟨r, hr, hmin⟩ := (Finset.range u.length).exists_min_image (lv u)
    ⟨0, Finset.mem_range.2 hL⟩
  rw [Finset.mem_range] at hr
  refine ⟨r, hr, (ladder_rotate_iff hr).2 ⟨fun j hj => ?_, fun s hrs hs => ?_⟩⟩
  · rcases (hmin j (Finset.mem_range.2 (by omega))).lt_or_eq with h | h
    · exact h
    · exact absurd (lv_inj hr.le (by omega) h) (by omega)
  · calc lv u r * seqProduct u < lv u r * 1 := mul_lt_mul_of_pos_left hsp (lv_pos _ _)
      _ = lv u r := mul_one _
      _ ≤ lv u s := hmin s (Finset.mem_range.2 hs)

/-- The places r < L such that no rotation of v by L - r .. L - 1 is a ladder word: v rotated
    back by r has its first ladder rotation at r. -/
def tset (v : List Bool) : Finset ℕ :=
  (Finset.range v.length).filter
    (fun r => ∀ s ∈ Finset.Ico (v.length - r) v.length, ¬ Ladder (v.rotate s))

/-- The ladder words of length p2(n) and Order n. -/
def ladSet (n : ℕ) : Finset (List Bool) := (wordSet (p2_of n) n).filter Ladder

theorem rotate_sub_rotate (v : List Bool) {r : ℕ} (hr : r ≤ v.length) :
    (v.rotate (v.length - r)).rotate r = v := by
  rw [List.rotate_rotate, Nat.sub_add_cancel hr, List.rotate_length]

/-- For r ∈ tset v, v rotated back by r has its first ladder rotation at r. -/
theorem first_of_tset {v : List Bool} (hv : Ladder v) {r : ℕ} (hr : r ∈ tset v) :
    Ladder ((v.rotate (v.length - r)).rotate r) ∧
      ∀ s < r, ¬ Ladder ((v.rotate (v.length - r)).rotate s) := by
  rw [tset, Finset.mem_filter, Finset.mem_range] at hr
  refine ⟨by rw [rotate_sub_rotate v hr.1.le]; exact hv, fun s hs => ?_⟩
  rw [List.rotate_rotate]
  exact hr.2 _ (Finset.mem_Ico.2 ⟨by omega, by omega⟩)

/-- Every word of length p2(n) and Order n is v rotated back by r, for exactly one ladder word v
    and r ∈ tset v. -/
theorem card_wordSet_eq_sum_tset (n : ℕ) :
    (wordSet (p2_of n) n).card = ∑ v ∈ ladSet n, (tset v).card := by
  rw [← Finset.card_sigma]
  symm
  apply Finset.card_bij (fun (p : Σ _ : List Bool, ℕ) _ => p.1.rotate (p.1.length - p.2))
  · rintro ⟨v, r⟩ hp
    simp only [Finset.mem_sigma, ladSet, Finset.mem_filter, mem_wordSet] at hp ⊢
    exact ⟨by rw [List.length_rotate]; exact hp.1.1.1, by rw [order_rotate]; exact hp.1.1.2⟩
  · rintro ⟨v, r⟩ hp ⟨v', r'⟩ hp' he
    simp only [Finset.mem_sigma, ladSet, Finset.mem_filter, mem_wordSet] at hp hp' he
    obtain ⟨h1, h2⟩ := first_of_tset hp.1.2 hp.2
    obtain ⟨h1', h2'⟩ := first_of_tset hp'.1.2 hp'.2
    rw [he] at h1 h2
    have hrr : r = r' := by
      rcases lt_trichotomy r r' with h | h | h
      · exact absurd h1 (h2' r h)
      · exact h
      · exact absurd h1' (h2 r' h)
    subst hrr
    have hr1 := (Finset.mem_range.1 (Finset.mem_filter.1 hp.2).1).le
    have hr2 := (Finset.mem_range.1 (Finset.mem_filter.1 hp'.2).1).le
    have hvv : v = v' := by
      rw [← rotate_sub_rotate v hr1, ← rotate_sub_rotate v' hr2, he]
    subst hvv
    rfl
  · intro u hu
    rw [mem_wordSet] at hu
    have hLpos : 1 ≤ p2_of n := by unfold p2_of; omega
    have hune : u ≠ [] := by
      intro h; rw [h] at hu; simp at hu; omega
    have hsp : seqProduct u < 1 := by
      rw [seqProduct_lt_one_iff, hu.1, hu.2]; exact p2_of_spec n
    have hex := exists_ladder_rotate hune hsp
    classical
    obtain ⟨hrL, hrlad⟩ := Nat.find_spec hex
    refine ⟨⟨u.rotate (Nat.find hex), Nat.find hex⟩, ?_, ?_⟩
    · simp only [Finset.mem_sigma, ladSet, Finset.mem_filter, mem_wordSet, tset,
        Finset.mem_range, List.length_rotate, order_rotate, Finset.mem_Ico]
      refine ⟨⟨⟨hu.1, hu.2⟩, hrlad⟩, hrL, fun s hs hl => ?_⟩
      rw [List.rotate_rotate, ← List.rotate_mod,
        Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at hl
      exact Nat.find_min hex (show Nat.find hex + s - u.length < Nat.find hex by omega)
        ⟨by omega, hl⟩
    · change (u.rotate (Nat.find hex)).rotate ((u.rotate (Nat.find hex)).length - Nat.find hex) = u
      rw [List.length_rotate, List.rotate_rotate, Nat.add_sub_cancel' hrL.le, List.rotate_length]

theorem lv_append_left {d w : List Bool} {i : ℕ} (hi : i ≤ d.length) : lv (d ++ w) i = lv d i := by
  simp only [lv, List.take_append_of_le_length hi]

theorem lv_append_right (d w : List Bool) (j : ℕ) :
    lv (d ++ w) (d.length + j) = seqProduct d * lv w j := by
  simp only [lv, List.take_length_add_append, seqProduct_append]

theorem one_le_lv_of_admissible {d : List Bool} (hd : Admissible d) {i : ℕ} (hi : i < d.length) :
    1 ≤ lv d i := by
  rcases Nat.eq_zero_or_pos i with h | h
  · rw [h, lv_zero]
  · exact (hd.prefix_gt i h hi).le

theorem ladder_of_admissible {d : List Bool} (hd : Admissible d) : Ladder d :=
  fun _ hi => lt_of_lt_of_le hd.lt_one (one_le_lv_of_admissible hd hi)

theorem seqProduct_lt_one_of_ladder {v : List Bool} (hv : Ladder v) (hne : v ≠ []) :
    seqProduct v < 1 := by
  have := hv 0 (List.length_pos_iff.mpr hne); rwa [lv_zero] at this

/-- No rotation of an admissible word by 0 < s < L is a ladder word. -/
theorem not_ladder_rotate_of_admissible {d : List Bool} (hd : Admissible d) {s : ℕ} (h0 : 0 < s)
    (hs : s < d.length) : ¬ Ladder (d.rotate s) := by
  rw [ladder_rotate_iff_of_ladder (ladder_of_admissible hd) h0 hs]
  intro h
  have h1 := h 0 h0
  rw [lv_zero] at h1
  exact absurd (hd.prefix_gt s h0 hs) (not_lt.2 h1.le)

theorem tset_of_admissible {d : List Bool} (hd : Admissible d) :
    tset d = Finset.range d.length := by
  apply Finset.filter_true_of_mem
  intro r hr s hs
  rw [Finset.mem_range] at hr
  rw [Finset.mem_Ico] at hs
  exact not_ladder_rotate_of_admissible hd (by omega) hs.2

/-- An admissible word followed by a nonempty ladder word is a ladder word. -/
theorem ladder_append {d w : List Bool} (hd : Admissible d) (hw : Ladder w) (hne : w ≠ []) :
    Ladder (d ++ w) := by
  have hw1 := seqProduct_lt_one_of_ladder hw hne
  intro i hi
  rw [seqProduct_append]
  rcases le_or_gt d.length i with h | h
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [lv_append_right]
    rw [List.length_append] at hi
    exact mul_lt_mul_of_pos_left (hw j (by omega)) (seqProduct_pos _)
  · rw [lv_append_left h.le]
    calc seqProduct d * seqProduct w < 1 * 1 :=
          mul_lt_mul'' hd.lt_one hw1 (seqProduct_pos _).le (seqProduct_pos _).le
      _ = 1 := one_mul 1
      _ ≤ lv d i := one_le_lv_of_admissible hd h

/-- The ladder rotations of d ++ w from |d| on are those of w, shifted by |d|. -/
theorem ladder_rotate_append {d w : List Bool} (hd : Admissible d) (hw : Ladder w) (hne : w ≠ [])
    {j : ℕ} (hj : j < w.length) :
    Ladder ((d ++ w).rotate (d.length + j)) ↔ Ladder (w.rotate j) := by
  have hdpos : 0 < d.length := by
    rcases Nat.eq_zero_or_pos d.length with h | h
    · have := hd.lt_one; rw [List.length_eq_zero_iff.1 h] at this; simp [seqProduct] at this
    · exact h
  have hv := ladder_append hd hw hne
  have hlen : d.length + j < (d ++ w).length := by rw [List.length_append]; omega
  rw [ladder_rotate_iff_of_ladder hv (by omega) hlen, lv_append_right]
  rcases Nat.eq_zero_or_pos j with h0 | h0
  · subst h0
    rw [List.rotate_zero, lv_zero, mul_one]
    refine ⟨fun _ => hw, fun _ i hi => ?_⟩
    rw [Nat.add_zero] at hi
    rw [lv_append_left hi.le]
    exact lt_of_lt_of_le hd.lt_one (one_le_lv_of_admissible hd hi)
  rw [ladder_rotate_iff_of_ladder hw h0 hj]
  have hsd := seqProduct_pos d
  constructor
  · intro h i hi
    have := h (d.length + i) (by omega)
    rw [lv_append_right] at this
    exact lt_of_mul_lt_mul_left this hsd.le
  · intro h i hi
    rcases le_or_gt d.length i with hle | hlt
    · obtain ⟨i', rfl⟩ := Nat.exists_eq_add_of_le hle
      rw [lv_append_right]
      exact mul_lt_mul_of_pos_left (h i' (by omega)) hsd
    · rw [lv_append_left hlt.le]
      have h1 := h 0 h0
      rw [lv_zero] at h1
      calc seqProduct d * lv w j < 1 * 1 :=
            mul_lt_mul'' hd.lt_one h1 hsd.le (lv_pos _ _).le
        _ = 1 := one_mul 1
        _ ≤ lv d i := one_le_lv_of_admissible hd hlt

/-- tset (d ++ w) = tset w. -/
theorem tset_append {d w : List Bool} (hd : Admissible d) (hw : Ladder w) (hne : w ≠ []) :
    tset (d ++ w) = tset w := by
  have hdl : (d ++ w).length = d.length + w.length := List.length_append
  have hwpos : 0 < w.length := List.length_pos_iff.mpr hne
  have hat : Ladder ((d ++ w).rotate (d.length + 0)) :=
    (ladder_rotate_append hd hw hne hwpos).2 (by rw [List.rotate_zero]; exact hw)
  ext r
  simp only [tset, Finset.mem_filter, Finset.mem_range, Finset.mem_Ico, hdl]
  constructor
  · rintro ⟨hr, h⟩
    have hrw : r < w.length := by
      by_contra hc
      exact h (d.length + 0) ⟨by omega, by omega⟩ hat
    refine ⟨hrw, fun s hs => ?_⟩
    have := h (d.length + s) ⟨by omega, by omega⟩
    rwa [ladder_rotate_append hd hw hne hs.2] at this
  · rintro ⟨hrw, h⟩
    refine ⟨by omega, fun s hs => ?_⟩
    obtain ⟨s', rfl⟩ := Nat.exists_eq_add_of_le (show d.length ≤ s by omega)
    rw [ladder_rotate_append hd hw hne (by omega)]
    exact h s' ⟨by omega, by omega⟩

/-- The split Orders of n: 1 ≤ m < n with p2(m) + p2(n - m) = p2(n). -/
def splitOrders (n : ℕ) : Finset ℕ :=
  (Finset.Ico 1 n).filter (fun m => p2_of m + p2_of (n - m) = p2_of n)

/-- Admissible words of a split Order m with a ladder word of Order n - m. -/
def splitSet (n : ℕ) : Finset (Σ _ : ℕ, List Bool × List Bool) :=
  (splitOrders n).sigma (fun m => admSet m ×ˢ ladSet (n - m))

theorem admSet_subset_ladSet (n : ℕ) : admSet n ⊆ ladSet n := by
  intro d hd
  rw [mem_admSet] at hd
  simp only [ladSet, Finset.mem_filter, mem_wordSet]
  exact ⟨⟨by rw [admissible_length _ hd.1, hd.2], hd.2⟩, ladder_of_admissible hd.1⟩

theorem append_mem_ladSet {n m : ℕ} (hm : m ∈ splitOrders n) {d w : List Bool}
    (hd : d ∈ admSet m) (hw : w ∈ ladSet (n - m)) : d ++ w ∈ ladSet n \ admSet n := by
  simp only [splitOrders, Finset.mem_filter, Finset.mem_Ico] at hm
  rw [mem_admSet] at hd
  simp only [ladSet, Finset.mem_filter, mem_wordSet] at hw
  have hdl : d.length = p2_of m := by rw [admissible_length _ hd.1, hd.2]
  have hwpos : 0 < w.length := by rw [hw.1.1]; unfold p2_of; omega
  have hwne : w ≠ [] := List.ne_nil_of_length_pos hwpos
  rw [Finset.mem_sdiff, mem_admSet]
  refine ⟨?_, fun h => ?_⟩
  · simp only [ladSet, Finset.mem_filter, mem_wordSet, List.length_append, order_append]
    exact ⟨⟨by rw [hdl, hw.1.1, hm.2], by rw [hd.2, hw.1.2]; omega⟩, ladder_append hd.1 hw.2 hwne⟩
  · have hdpos : 1 ≤ d.length := by rw [hdl]; unfold p2_of; omega
    have h1 := h.1.prefix_gt d.length hdpos (by rw [List.length_append]; omega)
    have e : seqProduct ((d ++ w).take d.length) = seqProduct d :=
      (lv_append_left le_rfl).trans (lv_length d)
    rw [e] at h1
    exact absurd hd.1.lt_one (not_lt.2 h1.le)

/-- A non-admissible ladder word of Order n splits at its first level below 1. -/
theorem exists_ladder_split {n : ℕ} {v : List Bool} (hv : v ∈ ladSet n \ admSet n) :
    ∃ m d w, m ∈ splitOrders n ∧ d ∈ admSet m ∧ w ∈ ladSet (n - m) ∧ d ++ w = v := by
  rw [Finset.mem_sdiff, mem_admSet] at hv
  obtain ⟨hv, hna⟩ := hv
  simp only [ladSet, Finset.mem_filter, mem_wordSet] at hv
  obtain ⟨⟨hvl, hvo⟩, hvlad⟩ := hv
  have hsp : seqProduct v < 1 := by rw [seqProduct_lt_one_iff, hvl, hvo]; exact p2_of_spec n
  have hex : ∃ g, 1 ≤ g ∧ g < v.length ∧ lv v g < 1 := by
    by_contra hc
    apply hna
    refine ⟨⟨fun k hk1 hk2 => ?_, hsp⟩, hvo⟩
    have hge : 1 ≤ lv v k := by
      by_contra h1
      exact hc ⟨k, hk1, hk2, lt_of_not_ge h1⟩
    rcases hge.lt_or_eq with h | h
    · exact h
    · have := lv_inj (v := v) (i := 0) (j := k) (by omega) hk2.le (by rw [lv_zero]; exact h)
      omega
  classical
  obtain ⟨g, ⟨hg1, hgL, hglt⟩, hmin⟩ : ∃ g, (1 ≤ g ∧ g < v.length ∧ lv v g < 1) ∧
      ∀ k < g, ¬ (1 ≤ k ∧ k < v.length ∧ lv v k < 1) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun k hk => Nat.find_min hex hk⟩
  obtain ⟨d, w, hdw, hdl⟩ : ∃ d w, d ++ w = v ∧ d.length = g :=
    ⟨v.take g, v.drop g, List.take_append_drop g v, by rw [List.length_take]; omega⟩
  subst hdw hdl
  rw [List.length_append] at hgL hvl
  rw [order_append] at hvo
  have hwpos : 0 < w.length := by omega
  have hwne : w ≠ [] := List.ne_nil_of_length_pos hwpos
  rw [lv_append_left le_rfl, lv_length] at hglt
  have hdadm : Admissible d := by
    refine ⟨fun k hk1 hk2 => ?_, hglt⟩
    have hk := hmin k hk2
    rw [lv_append_left hk2.le] at hk
    have hge : 1 ≤ lv d k := by
      by_contra h1
      exact hk ⟨hk1, by rw [List.length_append]; omega, lt_of_not_ge h1⟩
    rcases hge.lt_or_eq with h | h
    · exact h
    · have := lv_inj (v := d) (i := 0) (j := k) (by omega) hk2.le (by rw [lv_zero]; exact h)
      omega
  have hwlad : Ladder w := by
    intro j hj
    have h := hvlad (d.length + j) (by rw [List.length_append]; omega)
    rw [seqProduct_append, lv_append_right] at h
    exact lt_of_mul_lt_mul_left h (seqProduct_pos d).le
  have hdl := admissible_length _ hdadm
  have hw3 : 3 ^ order w < 2 ^ w.length :=
    (seqProduct_lt_one_iff w).1 (seqProduct_lt_one_of_ladder hwlad hwne)
  have hd3 : 3 ^ order d < 2 ^ d.length := (seqProduct_lt_one_iff d).1 hdadm.lt_one
  have hlow := p2_of_spec_lower n
  rw [← hvl, ← hvo] at hlow
  have hw2 : 2 ^ (w.length - 1) < 3 ^ order w := by
    have h1 : 2 ^ d.length * 2 ^ (w.length - 1) < 2 ^ d.length * 3 ^ order w := by
      calc 2 ^ d.length * 2 ^ (w.length - 1) = 2 ^ (d.length + w.length - 1) := by
            rw [← pow_add]; congr 1; omega
        _ ≤ 3 ^ (order d + order w) := hlow
        _ = 3 ^ order d * 3 ^ order w := pow_add _ _ _
        _ < 2 ^ d.length * 3 ^ order w :=
            Nat.mul_lt_mul_of_pos_right hd3 (by positivity)
    exact Nat.lt_of_mul_lt_mul_left h1
  have hpw : p2_of (order w) = w.length :=
    le_antisymm (p2_of_le_of_three_pow_lt hw3) (by
      have := (Nat.pow_lt_pow_iff_right (by norm_num)).mp (lt_of_lt_of_le hw2 (p2_of_spec _).le)
      omega)
  have hp1 : 1 ≤ p2_of (order d) := by unfold p2_of; omega
  have hm0 : order d ≠ 0 := by
    intro h0
    have : order w = n := by omega
    rw [this] at hpw
    omega
  have hmn : order d ≠ n := by
    intro h
    rw [h] at hdl
    omega
  refine ⟨order d, d, w, ?_, ?_, ?_, rfl⟩
  · simp only [splitOrders, Finset.mem_filter, Finset.mem_Ico]
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    rw [show n - order d = order w by omega, hpw, ← hdl]
    omega
  · rw [mem_admSet]; exact ⟨hdadm, rfl⟩
  · simp only [ladSet, Finset.mem_filter, mem_wordSet]
    rw [show n - order d = order w by omega, hpw]
    exact ⟨⟨rfl, rfl⟩, hwlad⟩

theorem sum_tset_split (n : ℕ) :
    ∑ v ∈ ladSet n \ admSet n, (tset v).card = ∑ p ∈ splitSet n, (tset p.2.2).card := by
  symm
  apply Finset.sum_bij (fun (p : Σ _ : ℕ, List Bool × List Bool) _ => p.2.1 ++ p.2.2)
  · rintro ⟨m, d, w⟩ hp
    simp only [splitSet, Finset.mem_sigma, Finset.mem_product] at hp
    exact append_mem_ladSet hp.1 hp.2.1 hp.2.2
  · rintro ⟨m, d, w⟩ hp ⟨m', d', w'⟩ hp' h
    simp only [splitSet, Finset.mem_sigma, Finset.mem_product, mem_admSet] at hp hp' h
    have hpre : d <+: d ++ w := List.prefix_append d w
    have hpre' : d' <+: d ++ w := by rw [h]; exact List.prefix_append d' w'
    have hdd : d = d' := by
      by_contra hne
      rcases le_total d.length d'.length with hle | hle
      · exact admissible_not_prefix d d' hp.2.1.1 hp'.2.1.1 hne
          (List.prefix_of_prefix_length_le hpre hpre' hle)
      · exact admissible_not_prefix d' d hp'.2.1.1 hp.2.1.1 (Ne.symm hne)
          (List.prefix_of_prefix_length_le hpre' hpre hle)
    subst hdd
    have hww : w = w' := List.append_cancel_left h
    subst hww
    have hmm : m = m' := by rw [← hp.2.1.2, ← hp'.2.1.2]
    subst hmm
    rfl
  · intro v hv
    obtain ⟨m, d, w, hm, hd, hw, rfl⟩ := exists_ladder_split hv
    refine ⟨⟨m, d, w⟩, ?_, rfl⟩
    simp only [splitSet, Finset.mem_sigma, Finset.mem_product]
    exact ⟨hm, hd, hw⟩
  · rintro ⟨m, d, w⟩ hp
    simp only [splitSet, Finset.mem_sigma, Finset.mem_product, mem_admSet, ladSet,
      Finset.mem_filter, mem_wordSet] at hp
    have hwne : w ≠ [] := List.ne_nil_of_length_pos (by rw [hp.2.2.1.1]; unfold p2_of; omega)
    rw [tset_append hp.2.1.1 hp.2.2.2 hwne]

/-- Theorem C83: C(p2(n), n) = p2(n) a(n) + Σ_{m split} a(m) C(p2(n - m), n - m), where
    a = A100982 and the split Orders are 1 ≤ m < n with p2(m) + p2(n - m) = p2(n). -/
theorem choose_p2_eq_split (n : ℕ) :
    (p2_of n).choose n = p2_of n * (admSet n).card +
      ∑ m ∈ splitOrders n, (admSet m).card * (p2_of (n - m)).choose (n - m) := by
  rw [← card_wordSet, card_wordSet_eq_sum_tset,
    ← Finset.sum_sdiff (admSet_subset_ladSet n), add_comm, sum_tset_split]
  congr 1
  · rw [Finset.sum_congr rfl (g := fun _ => p2_of n), Finset.sum_const, smul_eq_mul, mul_comm]
    intro d hd
    rw [mem_admSet] at hd
    rw [tset_of_admissible hd.1, Finset.card_range, admissible_length _ hd.1, hd.2]
  · rw [splitSet, Finset.sum_sigma]
    apply Finset.sum_congr rfl
    intro m _
    rw [Finset.sum_product]
    simp only
    rw [Finset.sum_congr rfl (g := fun _ => (p2_of (n - m)).choose (n - m)), Finset.sum_const,
      smul_eq_mul]
    intro _ _
    rw [← card_wordSet_eq_sum_tset, card_wordSet]

/-- The split Orders by the floors: for 1 ≤ m < n, p2(m) + p2(n - m) = p2(n) iff
    2^p2(m) 3^n < 2^p2(n) 3^m (the floor of m above the floor of n). -/
theorem mem_splitOrders_iff {n m : ℕ} (hm1 : 1 ≤ m) (hmn : m < n) :
    m ∈ splitOrders n ↔ 2 ^ p2_of m * 3 ^ n < 2 ^ p2_of n * 3 ^ m := by
  simp only [splitOrders, Finset.mem_filter, Finset.mem_Ico]
  obtain ⟨k, rfl⟩ : ∃ k, n = m + k := ⟨n - m, by omega⟩
  rw [Nat.add_sub_cancel_left]
  have e : 2 ^ p2_of m * 3 ^ (m + k) = (2 ^ p2_of m * 3 ^ k) * 3 ^ m := by ring
  rw [e, Nat.mul_lt_mul_right (by positivity)]
  have ha1 : 1 ≤ p2_of m := by unfold p2_of; omega
  have hb1 : 1 ≤ p2_of k := by unfold p2_of; omega
  have h3a := p2_of_spec m
  have h3b := p2_of_spec k
  have hla := p2_of_spec_lower m
  have hlb := p2_of_spec_lower k
  have hL := p2_of_spec (m + k)
  have hup : p2_of (m + k) ≤ p2_of m + p2_of k :=
    p2_of_le_of_three_pow_lt (by
      rw [pow_add, pow_add]
      exact mul_lt_mul'' h3a h3b (by positivity) (by positivity))
  have hlow : p2_of m + p2_of k - 2 < p2_of (m + k) := by
    have : 2 ^ (p2_of m + p2_of k - 2) < 2 ^ p2_of (m + k) :=
      calc 2 ^ (p2_of m + p2_of k - 2) = 2 ^ (p2_of m - 1) * 2 ^ (p2_of k - 1) := by
            rw [← pow_add]; congr 1; omega
        _ ≤ 3 ^ m * 3 ^ k := Nat.mul_le_mul hla hlb
        _ = 3 ^ (m + k) := (pow_add _ _ _).symm
        _ < 2 ^ p2_of (m + k) := hL
    exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp this
  constructor
  · rintro ⟨_, h⟩
    rw [← h, pow_add]
    exact Nat.mul_lt_mul_of_pos_left h3b (by positivity)
  · intro h
    refine ⟨⟨hm1, by omega⟩, ?_⟩
    by_contra hne
    have hL' : p2_of (m + k) = p2_of m + (p2_of k - 1) := by omega
    rw [hL', pow_add] at h
    exact absurd h (not_lt.2 (Nat.mul_le_mul_left _ hlb))

end AcceleratedCollatz
