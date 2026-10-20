-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TStartSweepPermQ

/-!
  The start sweep of the q-family is one-to-one on the admissible words of every Order
  (odd q ≥ 3), under Thomas and Williams, Thm 6.3 (`SweepBijective`: the integer sweep
  permutes the words of each content). The start sweep of a word is the sweep of the
  reversed word (`startSweepQ_eq_sweepQ_reverse`). A word of Order n whose endpoint levels
  are all below 1 has the integer sweep as its sweep (`sweepQ_eq_sweepZ_of_lt_one`), and
  the reverse of an admissible word is such a word (`lvlQ_reverse_lt_one`). So two
  admissible words of one Order with the same start sweep are equal
  (`startSweepQ_injOn`).
-/

namespace AcceleratedCollatz

variable {q : ℕ}

/-- The flip around the end of a word is the reversed word. -/
theorem peakFlip_length (s : List Bool) : peakFlip s s.length = s.reverse := by
  unfold peakFlip
  rw [List.take_length, List.drop_length, List.reverse_nil, List.append_nil]

/-- The start sweep of a word is the sweep of the reversed word. -/
theorem startSweepQ_eq_sweepQ_reverse (hodd : Odd q) (hq0 : 0 < q) (s : List Bool) :
    startSweepQ q s = sweepQ q s.reverse := by
  rw [← peakFlip_length s]
  apply startSweepQ_eq_sweepQ_peakFlip hodd hq0 le_rfl
  · intro i j _ hkj hj
    exact absurd hj (Nat.not_lt.mpr hkj)
  · intro i j _ hkj hj
    exact absurd hj (Nat.not_lt.mpr hkj)

/-- A word of Order n whose endpoint levels are all below 1 sorts like its integer
    sweep. -/
theorem sweepIdxQ_eq_of_lt_one (hodd : Odd q) (hq : 3 ≤ q) {n : ℕ} {c d : ℤ} (hd : 0 < d)
    (hcd : ∀ a : ℕ, 1 ≤ a → a ≤ n + 1 →
      d * ((p2Q q a : ℤ) - 1) < c * a ∧ c * a < d * p2Q q a)
    {t : List Bool} (hord : order t = n)
    (hlt : ∀ m, 1 ≤ m → m ≤ t.length → lvlQ q t m < 1) :
    sweepIdxQ q t = sweepIdxZ (c - d) (-d) t := by
  have hmemZ : ∀ {i}, i ∈ sweepIdxZ (c - d) (-d) t → i < t.length := by
    intro i hi
    rw [(sweepIdxZ_perm _ _ t).mem_iff, List.mem_range] at hi
    exact hi
  have hneg : ∀ {m}, 1 ≤ m → m ≤ t.length → lvlZ (c - d) (-d) t m < 0 := by
    intro m hm1 hm
    have hiff := lvlQ_lt_iff_lvlZ hodd hq hd hcd hord (s := t) (i := m) (k := 0) hm
      (Nat.zero_le _)
    rw [lvlQ_zero, lvlZ_zero] at hiff
    exact hiff.mp (hlt m hm1 hm)
  apply List.Perm.eq_of_pairwise (le := fun i k => lvlQ q t (k + 1) < lvlQ q t (i + 1))
  · intro a b _ _ hab hba
    exact (lt_asymm hab hba).elim
  · refine ((sweepIdxQ_pairwise q t).and (sweepIdxQ_nodup q t)).imp_of_mem ?_
    intro a b ha hb h
    have ha' := mem_sweepIdxQ.mp ha
    have hb' := mem_sweepIdxQ.mp hb
    exact lt_of_le_of_ne h.1 (lvlQ_ne_of_ne hodd (by omega) (by omega) (by omega))
  · refine ((sweepIdxZ_pairwise _ _ t).and (sweepIdxZ_nodup _ _ t)).imp_of_mem ?_
    intro a b ha hb h
    have ha' := hmemZ ha
    have hb' := hmemZ hb
    have hna := hneg (m := a + 1) (by omega) (by omega)
    have hnb := hneg (m := b + 1) (by omega) (by omega)
    have hkey := h.1
    unfold twKey at hkey
    have hfa : decide (lvlZ (c - d) (-d) t (a + 1) < 0) = true := by
      simp only [decide_eq_true_eq]
      exact hna
    have hfb : decide (lvlZ (c - d) (-d) t (b + 1) < 0) = true := by
      simp only [decide_eq_true_eq]
      exact hnb
    rw [hfa, hfb, Prod.Lex.toLex_le_toLex] at hkey
    simp only [lt_self_iff_false, true_and, false_or] at hkey
    rw [Prod.Lex.toLex_le_toLex] at hkey
    have hiff := lvlQ_lt_iff_lvlZ hodd hq hd hcd hord (s := t) (i := b + 1) (k := a + 1)
      (by omega) (by omega)
    rcases hkey with hlt' | ⟨heq, _⟩
    · exact hiff.mpr hlt'
    · exfalso
      have hiff' := lvlQ_lt_iff_lvlZ hodd hq hd hcd hord (s := t) (i := a + 1) (k := b + 1)
        (by omega) (by omega)
      have hne := lvlQ_ne_of_ne hodd (s := t) (i := a + 1) (k := b + 1) (by omega) (by omega)
        (by omega)
      rcases lt_or_gt_of_ne hne with h1 | h1
      · have := hiff'.mp h1
        omega
      · have := hiff.mp h1
        omega
  · exact (sweepIdxQ_perm q t).trans (sweepIdxZ_perm (c - d) (-d) t).symm

/-- The sweep of a word of Order n whose endpoint levels are all below 1 is its integer
    sweep. -/
theorem sweepQ_eq_sweepZ_of_lt_one (hodd : Odd q) (hq : 3 ≤ q) {n : ℕ} {c d : ℤ}
    (hd : 0 < d)
    (hcd : ∀ a : ℕ, 1 ≤ a → a ≤ n + 1 →
      d * ((p2Q q a : ℤ) - 1) < c * a ∧ c * a < d * p2Q q a)
    {t : List Bool} (hord : order t = n)
    (hlt : ∀ m, 1 ≤ m → m ≤ t.length → lvlQ q t m < 1) :
    sweepQ q t = sweepZ (c - d) (-d) t := by
  unfold sweepQ sweepZ
  rw [sweepIdxQ_eq_of_lt_one hodd hq hd hcd hord hlt]

/-- Every endpoint level of the reverse of an admissible word is below 1. -/
theorem lvlQ_reverse_lt_one (hq0 : 0 < q) {s : List Bool} (hA : AdmissibleQ q s) {m : ℕ}
    (hm1 : 1 ≤ m) (hm : m ≤ s.length) : lvlQ q s.reverse m < 1 := by
  have h := lvlQ_peakFlip_le (q := q) (s := s) (k := s.length) (m := m) le_rfl hm
  rw [peakFlip_length, lvlQ_length] at h
  have hpos : 0 < lvlQ q s.reverse m := lvlQ_pos hq0 _ _
  have hge : 1 ≤ lvlQ q s (s.length - m) := by
    rcases Nat.eq_zero_or_pos (s.length - m) with h0 | hpos'
    · rw [h0, lvlQ_zero]
    · exact le_of_lt (hA.prefix_gt (s.length - m) hpos' (by omega))
  have hlt := hA.lt_one
  by_contra hx
  push Not at hx
  have hmul := mul_le_mul hx hge zero_le_one (le_of_lt hpos)
  linarith

/-- Under Thomas and Williams, Thm 6.3, the start sweep is one-to-one on the admissible
    words of every Order. -/
theorem startSweepQ_injOn (hodd : Odd q) (hq : 3 ≤ q) (hTW : SweepBijective) (n : ℕ) :
    Set.InjOn (startSweepQ q) (admSetQ q n : Set (List Bool)) := by
  obtain ⟨c, d, hd, hcd⟩ := exists_weightsQ hq n
  have hq0 : 0 < q := by omega
  have key : ∀ {s : List Bool}, s ∈ admSetQ q n →
      startSweepQ q s = sweepZ (c - d) (-d) s.reverse ∧
        s.reverse ∈ contentSet n (p2Q q n - n) := by
    intro s hs
    obtain ⟨hA, hord⟩ := (mem_admSetQ (by omega) _ _).mp hs
    have hordr : order s.reverse = n := by
      rw [order_perm (List.reverse_perm s), hord]
    have hlt : ∀ m, 1 ≤ m → m ≤ s.reverse.length → lvlQ q s.reverse m < 1 := by
      intro m hm1 hm
      rw [List.length_reverse] at hm
      exact lvlQ_reverse_lt_one hq0 hA hm1 hm
    refine ⟨?_, ?_, ?_⟩
    · rw [startSweepQ_eq_sweepQ_reverse hodd hq0,
        sweepQ_eq_sweepZ_of_lt_one hodd hq hd hcd hordr hlt]
    · rw [← order_eq_count_true, hordr]
    · have hc := count_true_add_count_false s.reverse
      have hl := admissibleQ_length (by omega) hA
      rw [← order_eq_count_true, hordr, List.length_reverse, hl, hord] at hc
      omega
  intro s hs s' hs' heq
  obtain ⟨h1, hm1⟩ := key hs
  obtain ⟨h2, hm2⟩ := key hs'
  rw [h1, h2] at heq
  exact List.reverse_injective ((hTW (c - d) (-d) n (p2Q q n - n)).injOn hm1 hm2 heq)

end AcceleratedCollatz
