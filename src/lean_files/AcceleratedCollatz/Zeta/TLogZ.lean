-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.Zeta.TCycleCount

/-!
  The coefficients of log Z (zeta paper, Theorem thm:logz; C192).

  With P(x, y) = Σ_{m ≥ 0} N(m) x^p2(m) y^m (N(m) = |admSet m|), the theorem says
  -log(1 - P) = Σ_{3^n < 2^L} C(L, n)/L x^L y^n. Apply x ∂/∂x to both sides: with
  B = Σ_{3^n < 2^L} C(L, n) x^L y^n it is x P_x = B (1 - P), that is, coefficient by coefficient,

    C(L, n) = [p2(n) = L] L N(n) + Σ_m N(m) C(L - p2(m), n - m),

  the sum over the m ≤ n with p2(m) < L and 3^(n-m) < 2^(L-p2(m)),
  for every L, n with 3^n < 2^L (`choose_eq_logz`); and x ∂/∂x is injective on series without
  x^0 terms, so this is the whole theorem. The proof is C83's (`choose_p2_eq_split`) for any length
  L: every word of length L and Order n is a ladder word v turned back by one r ∈ `tset v`
  (`card_wordSet_eq_sum_tsetL`); an admissible v has |tset v| = L, and any other ladder word is a
  drop word d followed by a nonempty ladder word w, with tset (d ++ w) = tset w.
-/

namespace AcceleratedCollatz

/-- The ladder words of length L and Order n. -/
def ladSetL (L n : ℕ) : Finset (List Bool) := (wordSet L n).filter Ladder

theorem mem_ladSetL {L n : ℕ} {v : List Bool} :
    v ∈ ladSetL L n ↔ (v.length = L ∧ order v = n) ∧ Ladder v := by
  simp only [ladSetL, Finset.mem_filter, mem_wordSet]

theorem one_le_of_three_pow_lt {L n : ℕ} (h : 3 ^ n < 2 ^ L) : 1 ≤ L := by
  rcases Nat.eq_zero_or_pos L with rfl | hL
  · have : 1 ≤ 3 ^ n := Nat.one_le_pow _ _ (by norm_num)
    simp at h
  · exact hL

/-- Every word of length L and Order n, 3^n < 2^L, is v rotated back by r, for exactly one
    ladder word v and r ∈ tset v. -/
theorem card_wordSet_eq_sum_tsetL {L n : ℕ} (h : 3 ^ n < 2 ^ L) :
    (wordSet L n).card = ∑ v ∈ ladSetL L n, (tset v).card := by
  rw [← Finset.card_sigma]
  symm
  apply Finset.card_bij (fun (p : Σ _ : List Bool, ℕ) _ => p.1.rotate (p.1.length - p.2))
  · rintro ⟨v, r⟩ hp
    simp only [Finset.mem_sigma, mem_ladSetL, mem_wordSet] at hp ⊢
    exact ⟨by rw [List.length_rotate]; exact hp.1.1.1, by rw [order_rotate]; exact hp.1.1.2⟩
  · rintro ⟨v, r⟩ hp ⟨v', r'⟩ hp' he
    simp only [Finset.mem_sigma, mem_ladSetL] at hp hp' he
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
    have hLpos := one_le_of_three_pow_lt h
    have hune : u ≠ [] := by
      intro h0; rw [h0] at hu; simp at hu; omega
    have hsp : seqProduct u < 1 := by
      rw [seqProduct_lt_one_iff, hu.1, hu.2]; exact h
    have hex := exists_ladder_rotate hune hsp
    classical
    obtain ⟨hrL, hrlad⟩ := Nat.find_spec hex
    refine ⟨⟨u.rotate (Nat.find hex), Nat.find hex⟩, ?_, ?_⟩
    · simp only [Finset.mem_sigma, mem_ladSetL, tset,
        Finset.mem_filter, Finset.mem_range, List.length_rotate, order_rotate, Finset.mem_Ico]
      refine ⟨⟨⟨hu.1, hu.2⟩, hrlad⟩, hrL, fun s hs hl => ?_⟩
      rw [List.rotate_rotate, ← List.rotate_mod,
        Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at hl
      exact Nat.find_min hex (show Nat.find hex + s - u.length < Nat.find hex by omega)
        ⟨by omega, hl⟩
    · change (u.rotate (Nat.find hex)).rotate ((u.rotate (Nat.find hex)).length - Nat.find hex) = u
      rw [List.length_rotate, List.rotate_rotate, Nat.add_sub_cancel' hrL.le, List.rotate_length]

/-- The admissible ladder words of length L and Order n: the drop words of Order n if
    p2(n) = L, else none. -/
theorem filter_admissible_ladSetL (L n : ℕ) :
    (ladSetL L n).filter Admissible = if p2_of n = L then admSet n else ∅ := by
  ext v
  rw [Finset.mem_filter, mem_ladSetL]
  split_ifs with hp
  · rw [mem_admSet]
    constructor
    · rintro ⟨⟨⟨_, ho⟩, _⟩, ha⟩; exact ⟨ha, ho⟩
    · rintro ⟨ha, ho⟩
      exact ⟨⟨⟨by rw [admissible_length _ ha, ho, hp], ho⟩, ladder_of_admissible ha⟩, ha⟩
  · simp only [Finset.notMem_empty, iff_false]
    rintro ⟨⟨⟨hl, ho⟩, _⟩, ha⟩
    exact hp (by rw [← ho, ← admissible_length _ ha, hl])

/-- Drop words of Order m ≤ n with ladder words of length L - p2(m) and Order n - m. -/
def splitSetL (L n : ℕ) : Finset (Σ _ : ℕ, List Bool × List Bool) :=
  ((Finset.range (n + 1)).filter (fun m => p2_of m < L)).sigma
    (fun m => admSet m ×ˢ ladSetL (L - p2_of m) (n - m))

theorem append_mem_ladSetL {L n m : ℕ} (hmn : m ≤ n) (hmL : p2_of m < L) {d w : List Bool}
    (hd : d ∈ admSet m) (hw : w ∈ ladSetL (L - p2_of m) (n - m)) :
    d ++ w ∈ (ladSetL L n).filter (fun v => ¬ Admissible v) := by
  rw [mem_admSet] at hd
  rw [mem_ladSetL] at hw
  have hdl : d.length = p2_of m := by rw [admissible_length _ hd.1, hd.2]
  have hwpos : 0 < w.length := by rw [hw.1.1]; omega
  have hwne : w ≠ [] := List.ne_nil_of_length_pos hwpos
  rw [Finset.mem_filter, mem_ladSetL, List.length_append, order_append]
  refine ⟨⟨⟨by rw [hdl, hw.1.1]; omega, by rw [hd.2, hw.1.2]; omega⟩,
    ladder_append hd.1 hw.2 hwne⟩, fun h => ?_⟩
  have hdpos : 1 ≤ d.length := by rw [hdl]; unfold p2_of; omega
  have h1 := h.prefix_gt d.length hdpos (by rw [List.length_append]; omega)
  have e : seqProduct ((d ++ w).take d.length) = seqProduct d :=
    (lv_append_left le_rfl).trans (lv_length d)
  rw [e] at h1
  exact absurd hd.1.lt_one (not_lt.2 h1.le)

/-- A ladder word of length L ≥ 1 that is not a drop word splits at its first level below 1. -/
theorem exists_ladder_splitL {L n : ℕ} (hL : 1 ≤ L) {v : List Bool}
    (hv : v ∈ (ladSetL L n).filter (fun v => ¬ Admissible v)) :
    ∃ m d w, m ≤ n ∧ p2_of m < L ∧ d ∈ admSet m ∧ w ∈ ladSetL (L - p2_of m) (n - m) ∧
      d ++ w = v := by
  rw [Finset.mem_filter, mem_ladSetL] at hv
  obtain ⟨⟨⟨hvl, hvo⟩, hvlad⟩, hna⟩ := hv
  have hvne : v ≠ [] := List.ne_nil_of_length_pos (by omega)
  have hsp := seqProduct_lt_one_of_ladder hvlad hvne
  have hex : ∃ g, 1 ≤ g ∧ g < v.length ∧ lv v g < 1 := by
    by_contra hc
    apply hna
    refine ⟨fun k hk1 hk2 => ?_, hsp⟩
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
  refine ⟨order d, d, w, by omega, by omega, ?_, ?_, rfl⟩
  · rw [mem_admSet]; exact ⟨hdadm, rfl⟩
  · rw [mem_ladSetL]
    exact ⟨⟨by omega, by omega⟩, hwlad⟩

theorem sum_tset_splitL {L n : ℕ} (hL : 1 ≤ L) :
    ∑ v ∈ (ladSetL L n).filter (fun v => ¬ Admissible v), (tset v).card =
      ∑ p ∈ splitSetL L n, (tset p.2.2).card := by
  symm
  apply Finset.sum_bij (fun (p : Σ _ : ℕ, List Bool × List Bool) _ => p.2.1 ++ p.2.2)
  · rintro ⟨m, d, w⟩ hp
    simp only [splitSetL, Finset.mem_sigma, Finset.mem_product, Finset.mem_filter,
      Finset.mem_range] at hp
    exact append_mem_ladSetL (by omega) hp.1.2 hp.2.1 hp.2.2
  · rintro ⟨m, d, w⟩ hp ⟨m', d', w'⟩ hp' h
    simp only [splitSetL, Finset.mem_sigma, Finset.mem_product, mem_admSet] at hp hp' h
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
    obtain ⟨m, d, w, hmn, hmL, hd, hw, rfl⟩ := exists_ladder_splitL hL hv
    refine ⟨⟨m, d, w⟩, ?_, rfl⟩
    simp only [splitSetL, Finset.mem_sigma, Finset.mem_product, Finset.mem_filter,
      Finset.mem_range]
    exact ⟨⟨by omega, hmL⟩, hd, hw⟩
  · rintro ⟨m, d, w⟩ hp
    simp only [splitSetL, Finset.mem_sigma, Finset.mem_product, mem_admSet, mem_ladSetL,
      Finset.mem_filter] at hp
    have hwne : w ≠ [] := List.ne_nil_of_length_pos (by rw [hp.2.2.1.1]; omega)
    rw [tset_append hp.2.1.1 hp.2.2.2 hwne]

/-- The ladder count of length L' ≥ 1 and Order n': C(L', n') when 3^n' < 2^L', else 0. -/
theorem sum_tset_ladSetL {L' n' : ℕ} (hL : 1 ≤ L') :
    ∑ w ∈ ladSetL L' n', (tset w).card = if 3 ^ n' < 2 ^ L' then L'.choose n' else 0 := by
  split_ifs with h
  · rw [← card_wordSet_eq_sum_tsetL h, card_wordSet]
  · rw [Finset.sum_eq_zero]
    intro w hw
    rw [mem_ladSetL] at hw
    have hwne : w ≠ [] := List.ne_nil_of_length_pos (by omega)
    have := (seqProduct_lt_one_iff w).1 (seqProduct_lt_one_of_ladder hw.2 hwne)
    rw [hw.1.1, hw.1.2] at this
    exact absurd this h

/-- Theorem thm:logz, coefficient form (C192): for 3^n < 2^L,
    C(L, n) = [p2(n) = L] L N(n) + Σ_m N(m) C(L - p2(m), n - m), the sum over the m ≤ n with
    p2(m) < L and 3^(n-m) < 2^(L-p2(m)), where N(m) = |admSet m| = A100982(m). With x ∂/∂x this
    is -log(1 - P(x, y)) = Σ_{3^n < 2^L} C(L, n)/L x^L y^n. -/
theorem choose_eq_logz {L n : ℕ} (h : 3 ^ n < 2 ^ L) :
    L.choose n = (if p2_of n = L then L * (admSet n).card else 0) +
      ∑ m ∈ (Finset.range (n + 1)).filter
          (fun m => p2_of m < L ∧ 3 ^ (n - m) < 2 ^ (L - p2_of m)),
        (admSet m).card * (L - p2_of m).choose (n - m) := by
  have hL := one_le_of_three_pow_lt h
  rw [← card_wordSet, card_wordSet_eq_sum_tsetL h,
    ← Finset.sum_filter_add_sum_filter_not (ladSetL L n) Admissible, sum_tset_splitL hL]
  congr 1
  · rw [Finset.sum_congr rfl (g := fun _ => L), Finset.sum_const, smul_eq_mul,
      filter_admissible_ladSetL]
    · split_ifs <;> simp [mul_comm]
    · intro d hd
      rw [Finset.mem_filter, mem_ladSetL] at hd
      rw [tset_of_admissible hd.2, Finset.card_range, hd.1.1.1]
  · rw [splitSetL, Finset.sum_sigma, ← Finset.filter_filter,
      Finset.sum_filter (p := fun m => 3 ^ (n - m) < 2 ^ (L - p2_of m))]
    apply Finset.sum_congr rfl
    intro m hm
    rw [Finset.mem_filter] at hm
    rw [Finset.sum_product]
    simp only
    rw [Finset.sum_congr rfl (g := fun _ => ∑ w ∈ ladSetL (L - p2_of m) (n - m), (tset w).card),
      Finset.sum_const, smul_eq_mul, sum_tset_ladSetL (by omega)]
    · split_ifs <;> simp
    · intro _ _; rfl

end AcceleratedCollatz
