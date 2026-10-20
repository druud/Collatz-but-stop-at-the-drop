-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TStartSweepPermQ

/-!
  Cut sweep for the q-family (odd q ≥ 3): the start sweep of a word without its final
  step, followed by a halving (`cutSweepQ`); for a word that ends in a halving, a
  rearrangement of its steps (`cutSweepQ_perm`). The steps that start below a level c
  multiply to at least c or to at least the level of the whole word
  (`min_le_prod_of_lower`), so the cut sweep maps admissible words of Order n to
  admissible words of Order n (`cutSweepQ_mem_admSetQ`). At a lower record Order the
  cut sweep of an admissible word is the sweep of the flip of its cut part around its
  highest point, with the halving (`cutSweepQ_eq_sweepQ_of_lowerRecordQ`); under
  `SweepBijective` it permutes the admissible words there (`cutSweepQ_bijOn`). At
  every other Order some admissible word is not a cut sweep
  (`not_surjOn_cutSweepQ`).
-/

namespace AcceleratedCollatz

variable {q : ℕ}

/-- Cut sweep: the start sweep of s without its final step, then a halving. -/
def cutSweepQ (q : ℕ) (s : List Bool) : List Bool := startSweepQ q s.dropLast ++ [false]

theorem cutSweepQ_append_false (q : ℕ) (w : List Bool) :
    cutSweepQ q (w ++ [false]) = startSweepQ q w ++ [false] := by
  unfold cutSweepQ
  rw [List.dropLast_concat]

theorem cutSweepQ_perm (q : ℕ) (w : List Bool) :
    (cutSweepQ q (w ++ [false])).Perm (w ++ [false]) := by
  rw [cutSweepQ_append_false]
  exact (startSweepQ_perm q w).append_right [false]

theorem lvlQ_append_left (q : ℕ) {w t : List Bool} {m : ℕ} (hm : m ≤ w.length) :
    lvlQ q (w ++ t) m = lvlQ q w m := by
  unfold lvlQ
  rw [List.take_append_of_le_length hm]

/-- The inner points of the cut part of an admissible word have level above 1. -/
theorem one_lt_lvlQ_cut (hq : 3 ≤ q) {n : ℕ} {w : List Bool} (hs : w ++ [false] ∈ admSetQ q n)
    {j : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ w.length) : 1 < lvlQ q w j := by
  have hA := ((mem_admSetQ (by omega) _ _).mp hs).1
  have hjL : j < (w ++ [false]).length := by
    rw [List.length_append, List.length_singleton]
    omega
  have h := hA.prefix_gt j hj1 hjL
  rwa [List.take_append_of_le_length hj] at h

theorem order_cut {n : ℕ} (hq : 3 ≤ q) {w : List Bool} (hs : w ++ [false] ∈ admSetQ q n) :
    order w = n := by
  have h := ((mem_admSetQ (by omega) _ _).mp hs).2
  unfold order at h ⊢
  simpa using h

theorem length_cut {n : ℕ} (hq : 3 ≤ q) {w : List Bool} (hs : w ++ [false] ∈ admSetQ q n) :
    w.length + 1 = p2Q q n := by
  obtain ⟨hA, hord⟩ := (mem_admSetQ (by omega) _ _).mp hs
  have h := admissibleQ_length (by omega) hA
  rw [hord, List.length_append, List.length_singleton] at h
  exact h

/-! ### The cut sweep of an admissible word is admissible -/

/-- The steps that start below c, and no others, multiply to at least c or to at least
    the level of the whole word. -/
theorem min_le_prod_of_lower (hq0 : 0 < q) (s : List Bool) (T : Finset ℕ) {c : ℚ}
    (hT : ∀ i ∈ T, i < s.length ∧ lvlQ q s i < c)
    (hN : ∀ i < s.length, i ∉ T → c ≤ lvlQ q s i) :
    min (lvlQ q s s.length) c ≤ ∏ i ∈ T, factorQ q (s.getD i false) := by
  let g : ℕ → ℚ := fun m => ∏ i ∈ (Finset.range m).filter (· ∈ T), factorQ q (s.getD i false)
  have hg_succ_mem : ∀ m, m ∈ T → g (m + 1) = g m * factorQ q (s.getD m false) := by
    intro m hm
    change ∏ i ∈ (Finset.range (m + 1)).filter (· ∈ T), factorQ q (s.getD i false) =
      (∏ i ∈ (Finset.range m).filter (· ∈ T), factorQ q (s.getD i false)) *
        factorQ q (s.getD m false)
    rw [Finset.range_add_one, Finset.filter_insert]
    simp only [hm, ↓reduceIte]
    rw [Finset.prod_insert (by simp), mul_comm]
  have hg_succ_not : ∀ m, m ∉ T → g (m + 1) = g m := by
    intro m hm
    change ∏ i ∈ (Finset.range (m + 1)).filter (· ∈ T), factorQ q (s.getD i false) =
      ∏ i ∈ (Finset.range m).filter (· ∈ T), factorQ q (s.getD i false)
    rw [Finset.range_add_one, Finset.filter_insert]
    simp only [hm, ↓reduceIte]
  have inv : ∀ m ≤ s.length, min (lvlQ q s m) c ≤ g m := by
    intro m
    induction m with
    | zero =>
      intro _
      have hg0 : g 0 = 1 := by
        change ∏ i ∈ (Finset.range 0).filter (· ∈ T), factorQ q (s.getD i false) = 1
        simp
      rw [lvlQ_zero, hg0]
      exact min_le_left _ _
    | succ m ih =>
      intro hm
      have ihm := ih (by omega)
      have hlt : m < s.length := by omega
      have hget : s[m]? = some (s.getD m false) := by
        simp [List.getD_eq_getElem?_getD, hlt]
      have hstep := lvlQ_succ q s hget
      have hf := factorQ_pos hq0 (s.getD m false)
      by_cases hmT : m ∈ T
      · rw [hg_succ_mem m hmT, hstep]
        have hlow := (hT m hmT).2
        rw [min_eq_left hlow.le] at ihm
        exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_right ihm hf.le)
      · rw [hg_succ_not m hmT]
        have hhigh := hN m hlt hmT
        rw [min_eq_right hhigh] at ihm
        exact (min_le_right _ _).trans ihm
  have hfilter : (Finset.range s.length).filter (· ∈ T) = T := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨(hT k h).1, h⟩
  have h1 := inv s.length le_rfl
  change min (lvlQ q s s.length) c ≤
    ∏ i ∈ (Finset.range s.length).filter (· ∈ T), factorQ q (s.getD i false) at h1
  rwa [hfilter] at h1

/-- A proper prefix of the start sweep of the cut part of an admissible word: its set T
    of steps, a step k outside T, and the bound of `min_le_prod_of_lower` at the level
    at which k starts. -/
theorem exists_startSweepQ_prefix_bound (hodd : Odd q) (hq : 3 ≤ q) {n : ℕ} {w : List Bool}
    (hs : w ++ [false] ∈ admSetQ q n) {m : ℕ} (hm1 : 1 ≤ m) (hm : m < w.length) :
    ∃ (T : Finset ℕ) (k : ℕ), T.card = m ∧ 0 ∈ T ∧ k ∉ T ∧ 1 ≤ k ∧ k < w.length ∧
      (∀ i ∈ T, i < w.length ∧ lvlQ q w i < lvlQ q w k) ∧
      min (lvlQ q w w.length) (lvlQ q w k) ≤ seqProductQ q ((startSweepQ q w).take m) := by
  obtain ⟨T, hcard, hT, hlow, hprod⟩ := exists_startSweepQ_prefix_set hodd w hm.le
  have hq0 : 0 < q := by omega
  set C := Finset.range w.length \ T with hC
  have hCne : C.Nonempty := by
    rw [← Finset.card_pos, hC, Finset.card_sdiff_of_subset
      (fun i hi => Finset.mem_range.mpr (hT i hi)), Finset.card_range]
    omega
  obtain ⟨k, hkC, hk⟩ := Finset.exists_mem_eq_inf' hCne (lvlQ q w)
  rw [hC, Finset.mem_sdiff, Finset.mem_range] at hkC
  have hTne : T.Nonempty := by
    rw [← Finset.card_pos]
    omega
  have h0T : 0 ∈ T := by
    by_contra h0
    obtain ⟨i, hi⟩ := hTne
    have hi0 : i ≠ 0 := fun h => h0 (h ▸ hi)
    have hlt := hlow i hi 0 (by omega) h0
    rw [lvlQ_zero] at hlt
    have hgt := one_lt_lvlQ_cut hq hs (j := i) (by omega) (hT i hi).le
    linarith
  have hk1 : 1 ≤ k := by
    by_contra h0
    have hk0 : k = 0 := by omega
    exact hkC.2 (hk0 ▸ h0T)
  have hTk : ∀ i ∈ T, i < w.length ∧ lvlQ q w i < lvlQ q w k :=
    fun i hi => ⟨hT i hi, hlow i hi k hkC.1 hkC.2⟩
  have hN : ∀ i < w.length, i ∉ T → lvlQ q w k ≤ lvlQ q w i := by
    intro i hi hiT
    have hiC : i ∈ C := by
      rw [hC, Finset.mem_sdiff, Finset.mem_range]
      exact ⟨hi, hiT⟩
    rw [← hk]
    exact Finset.inf'_le _ hiC
  refine ⟨T, k, hcard, h0T, hkC.2, hk1, hkC.1, hTk, ?_⟩
  rw [hprod]
  exact min_le_prod_of_lower hq0 w T hTk hN

/-- The cut sweep maps admissible words of Order n to admissible words of Order n. -/
theorem cutSweepQ_mem_admSetQ (hodd : Odd q) (hq : 3 ≤ q) {n : ℕ} {s : List Bool}
    (hs : s ∈ admSetQ q n) : cutSweepQ q s ∈ admSetQ q n := by
  obtain ⟨w, rfl⟩ := exists_eq_append_falseQ hq hs
  obtain ⟨hA, hord⟩ := (mem_admSetQ (by omega) _ _).mp hs
  rw [mem_admSetQ (by omega)]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro m hm1 hmL
    rw [(cutSweepQ_perm q w).length_eq, List.length_append, List.length_singleton] at hmL
    have hmw : m ≤ (startSweepQ q w).length := by
      rw [length_startSweepQ]
      omega
    rw [cutSweepQ_append_false, List.take_append_of_le_length hmw]
    have hE : 1 < lvlQ q w w.length := one_lt_lvlQ_cut hq hs (by omega) le_rfl
    rcases Nat.lt_or_ge m w.length with hlt | hge
    · obtain ⟨T, k, _, _, _, hk1, hkL, _, hmin⟩ :=
        exists_startSweepQ_prefix_bound hodd hq hs hm1 hlt
      have hk := one_lt_lvlQ_cut hq hs hk1 hkL.le
      exact lt_of_lt_of_le (lt_min hE hk) hmin
    · have hwm : (startSweepQ q w).length ≤ m := by
        rw [length_startSweepQ]
        omega
      rw [List.take_of_length_le hwm, seqProductQ_startSweepQ, ← lvlQ_length]
      exact hE
  · rw [seqProductQ_perm q (cutSweepQ_perm q w)]
    exact hA.lt_one
  · rw [order_perm (cutSweepQ_perm q w), hord]

/-! ### Lower record Orders -/

/-- The sweep of an admissible word keeps the final halving last. -/
theorem sweepQ_append_false (hodd : Odd q) (hq : 3 ≤ q) {n : ℕ} {t : List Bool}
    (hs : t ++ [false] ∈ admSetQ q n) :
    sweepQ q (t ++ [false]) = sweepQ q t ++ [false] := by
  obtain ⟨hA, hord⟩ := (mem_admSetQ (by omega) _ _).mp hs
  set s := t ++ [false] with hsdef
  have hlen : s.length = t.length + 1 := by simp [hsdef]
  have hlvl : ∀ m, m ≤ t.length → lvlQ q s m = lvlQ q t m :=
    fun m hm => lvlQ_append_left q hm
  have hidx : sweepIdxQ q s = sweepIdxQ q t ++ [t.length] := by
    apply List.Perm.eq_of_pairwise (le := fun i k => lvlQ q s (k + 1) < lvlQ q s (i + 1))
    · intro a b _ _ hab hba
      exact (lt_asymm hab hba).elim
    · refine ((sweepIdxQ_pairwise q s).and (sweepIdxQ_nodup q s)).imp_of_mem ?_
      intro a b ha hb h
      have ha' := mem_sweepIdxQ.mp ha
      have hb' := mem_sweepIdxQ.mp hb
      exact lt_of_le_of_ne h.1 (lvlQ_ne_of_ne hodd (by omega) (by omega) (by omega))
    · rw [List.pairwise_append]
      refine ⟨?_, List.pairwise_singleton _ _, ?_⟩
      · refine ((sweepIdxQ_pairwise q t).and (sweepIdxQ_nodup q t)).imp_of_mem ?_
        intro a b ha hb h
        have ha' := mem_sweepIdxQ.mp ha
        have hb' := mem_sweepIdxQ.mp hb
        rw [hlvl _ (by omega), hlvl _ (by omega)]
        exact lt_of_le_of_ne h.1 (lvlQ_ne_of_ne hodd (by omega) (by omega) (by omega))
      · intro a ha b hb
        rw [List.mem_singleton] at hb
        rw [hb]
        have ha' := mem_sweepIdxQ.mp ha
        have hgt : 1 < lvlQ q s (a + 1) := hA.prefix_gt (a + 1) (by omega) (by omega)
        have hend : lvlQ q s (t.length + 1) < 1 := by
          rw [← hlen, lvlQ_length]
          exact hA.lt_one
        linarith
    · have h := (sweepIdxQ_perm q t).append_right [t.length]
      have h2 := sweepIdxQ_perm q s
      rw [hlen, List.range_succ] at h2
      exact h2.trans h.symm
  unfold sweepQ
  rw [hidx, List.map_append]
  congr 1
  · apply List.map_congr_left
    intro i hi
    have hi' : i < t.length := mem_sweepIdxQ.mp hi
    simp [hsdef, List.getD_eq_getElem?_getD, List.getElem?_append_left hi']
  · simp [hsdef]

/-- At a lower record Order a later point of the cut part above an earlier one is above
    it by at least the level of the cut part. -/
theorem lvlQ_mul_le_of_lowerRecordQ (hodd : Odd q) (hq : 3 ≤ q) {n : ℕ}
    (hR : LowerRecordQ q n) {w : List Bool} (hs : w ++ [false] ∈ admSetQ q n) {i j : ℕ}
    (hij : i < j) (hj : j < w.length) (hlt : lvlQ q w i < lvlQ q w j) :
    lvlQ q w i * lvlQ q w w.length ≤ lvlQ q w j := by
  have hord := order_cut hq hs
  have hlen := length_cut hq hs
  have hmono := order_take_mono w hij.le
  have hjn : order (w.take j) ≤ n := hord ▸ order_take_le w j
  obtain ⟨a, ha⟩ : ∃ a, order (w.take j) = order (w.take i) + a :=
    ⟨order (w.take j) - order (w.take i), by omega⟩
  obtain ⟨d, rfl⟩ : ∃ d, j = i + d := ⟨j - i, by omega⟩
  have hlt' := (lvlQ_lt_iff q (by omega) (by omega)).mp hlt
  rw [ha, pow_add, pow_add] at hlt'
  have hqa : 2 ^ d < q ^ a := by
    have hc : 0 < q ^ order (w.take i) * 2 ^ i := by positivity
    by_contra hge
    push Not at hge
    have := Nat.mul_le_mul_left (q ^ order (w.take i) * 2 ^ i) hge
    nlinarith
  have ha1 : 1 ≤ a := by
    by_contra h0
    have ha0 : a = 0 := by omega
    rw [ha0, pow_zero] at hqa
    have := Nat.one_le_two_pow (n := d)
    omega
  have hda := (two_pow_lt_q_pow_iff hodd hq ha1).mp hqa
  have hkey : q ^ n * 2 ^ d ≤ q ^ a * 2 ^ w.length := by
    rcases Nat.lt_or_ge a n with han | han
    · have hbf := (lowerRecordQ_iff_blockFactorQ hq n).mp hR a ha1 han
      rw [blockFactorQ_lt_iff, ← hlen, pow_succ] at hbf
      have hpow : 2 ^ (d + 1) ≤ 2 ^ p2Q q a := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h1 : q ^ n * 2 ^ (d + 1) ≤ q ^ n * 2 ^ p2Q q a := Nat.mul_le_mul_left _ hpow
      rw [pow_succ] at h1
      nlinarith
    · have han' : a = n := by omega
      rw [han']
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by omega))
  rw [← not_lt, lvlQ_lt_mul_iff q (by omega) (by omega), ha, hord, not_lt]
  calc q ^ order (w.take i) * q ^ n * 2 ^ (i + d)
      = q ^ order (w.take i) * 2 ^ i * (q ^ n * 2 ^ d) := by
        rw [pow_add]
        ring
    _ ≤ q ^ order (w.take i) * 2 ^ i * (q ^ a * 2 ^ w.length) :=
        Nat.mul_le_mul_left _ hkey
    _ = q ^ (order (w.take i) + a) * 2 ^ i * 2 ^ w.length := by
        rw [pow_add]
        ring

/-- The flip of the cut part of an admissible word around its highest point, with the
    halving, is admissible. -/
theorem peakFlip_append_false_mem_admSetQ (hodd : Odd q) (hq : 3 ≤ q) {n : ℕ} {w : List Bool}
    (hs : w ++ [false] ∈ admSetQ q n) {k : ℕ} (hk : k ≤ w.length)
    (hmax : ∀ j, j ≤ w.length → lvlQ q w j ≤ lvlQ q w k) :
    peakFlip w k ++ [false] ∈ admSetQ q n := by
  obtain ⟨hA, hord⟩ := (mem_admSetQ (by omega) _ _).mp hs
  have hq0 : 0 < q := by omega
  have hperm : (peakFlip w k ++ [false]).Perm (w ++ [false]) :=
    (peakFlip_perm w k).append_right [false]
  rw [mem_admSetQ (by omega)]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro m hm1 hmL
    rw [hperm.length_eq, List.length_append, List.length_singleton] at hmL
    have hmf : m ≤ (peakFlip w k).length := by
      rw [length_peakFlip]
      omega
    rw [List.take_append_of_le_length hmf]
    change 1 < lvlQ q (peakFlip w k) m
    have hE : 1 < lvlQ q w w.length := one_lt_lvlQ_cut hq hs (by omega) le_rfl
    rcases Nat.le_total m k with hmk | hkm
    · have h := lvlQ_peakFlip_le (q := q) hk hmk
      have hlt : lvlQ q w (k - m) < lvlQ q w k :=
        lt_of_le_of_ne (hmax _ (by omega)) (lvlQ_ne_of_ne hodd (by omega) hk (by omega))
      have hp := lvlQ_pos hq0 w (k - m)
      by_contra hle
      push Not at hle
      nlinarith
    · have h := lvlQ_peakFlip_ge (q := q) hk hkm (by omega)
      have hle := hmax (w.length + k - m) (by omega)
      have hp := lvlQ_pos hq0 w (w.length + k - m)
      have hpk := lvlQ_pos hq0 w k
      by_contra hle1
      push Not at hle1
      nlinarith
  · rw [seqProductQ_perm q hperm]
    exact hA.lt_one
  · rw [order_perm hperm, hord]

/-- At a lower record Order the cut sweep of an admissible word is the sweep of the flip
    of its cut part around its highest point, with the halving. -/
theorem cutSweepQ_eq_sweepQ_of_lowerRecordQ (hodd : Odd q) (hq : 3 ≤ q) {n : ℕ}
    (hR : LowerRecordQ q n) {w : List Bool} (hs : w ++ [false] ∈ admSetQ q n) {k : ℕ}
    (hk : k ≤ w.length) (hmax : ∀ j, j ≤ w.length → lvlQ q w j ≤ lvlQ q w k) :
    cutSweepQ q (w ++ [false]) = sweepQ q (peakFlip w k ++ [false]) := by
  have hq0 : 0 < q := by omega
  rw [cutSweepQ_append_false,
    sweepQ_append_false hodd hq (peakFlip_append_false_mem_admSetQ hodd hq hs hk hmax)]
  congr 1
  apply startSweepQ_eq_sweepQ_peakFlip hodd hq0 hk
  · intro i j hik hkj hj hlt
    have hE : 1 < lvlQ q w w.length := one_lt_lvlQ_cut hq hs (by omega) le_rfl
    have hp := lvlQ_pos hq0 w i
    nlinarith
  · intro i j hik hkj hj hlt
    by_contra hge
    push Not at hge
    have hne := lvlQ_ne_of_ne hodd (s := w) (i := i) (k := j) (by omega) hj.le (by omega)
    have hlow := lvlQ_mul_le_of_lowerRecordQ hodd hq hR hs (by omega : i < j) hj
      (lt_of_le_of_ne hge hne)
    linarith

/-- At a lower record Order two admissible words whose cut parts are rotations of each
    other are equal. -/
theorem append_comm_of_lowerRecordQ (hodd : Odd q) (hq : 3 ≤ q) {n : ℕ}
    (hR : LowerRecordQ q n) {z u : List Bool} (h1 : z ++ u ++ [false] ∈ admSetQ q n)
    (h2 : u ++ z ++ [false] ∈ admSetQ q n) : z ++ u = u ++ z := by
  rcases List.eq_nil_or_concat' z with hz | hz
  · rw [hz]
    simp
  rcases List.eq_nil_or_concat' u with hu | hu
  · rw [hu]
    simp
  exfalso
  have hq0 : 0 < q := by omega
  have hzl : 1 ≤ z.length := by
    obtain ⟨_, _, rfl⟩ := hz
    simp
  have hul : 1 ≤ u.length := by
    obtain ⟨_, _, rfl⟩ := hu
    simp
  have hlen : (z ++ u).length = z.length + u.length := List.length_append
  have hzgt : 1 < lvlQ q (z ++ u) z.length :=
    one_lt_lvlQ_cut hq h1 hzl (by omega)
  have hz0 : lvlQ q (z ++ u) 0 < lvlQ q (z ++ u) z.length := by
    rw [lvlQ_zero]
    exact hzgt
  have hlow := lvlQ_mul_le_of_lowerRecordQ hodd hq hR h1 (i := 0) (j := z.length)
    (by omega) (by omega) hz0
  rw [lvlQ_zero, one_mul, lvlQ_length, seqProductQ_append] at hlow
  have hzz : lvlQ q (z ++ u) z.length = seqProductQ q z := by
    unfold lvlQ
    rw [List.take_left]
  rw [hzz] at hlow
  have huL : u.length ≤ (u ++ z).length := by
    rw [List.length_append]
    omega
  have hugt : 1 < lvlQ q (u ++ z) u.length := one_lt_lvlQ_cut hq h2 hul huL
  have huu : lvlQ q (u ++ z) u.length = seqProductQ q u := by
    unfold lvlQ
    rw [List.take_left]
  rw [huu] at hugt
  have hzpos := seqProductQ_pos hq0 z
  nlinarith

/-- Under Thomas and Williams, Thm 6.3, the cut sweep permutes the admissible words of a
    lower record Order. -/
theorem cutSweepQ_bijOn (hodd : Odd q) (hq : 3 ≤ q) (hTW : SweepBijective) {n : ℕ}
    (hR : LowerRecordQ q n) :
    Set.BijOn (cutSweepQ q) (admSetQ q n : Set (List Bool)) (admSetQ q n) := by
  have hmaps : Set.MapsTo (cutSweepQ q) (admSetQ q n : Set (List Bool)) (admSetQ q n) :=
    fun s hs => cutSweepQ_mem_admSetQ hodd hq hs
  refine ((admSetQ q n).finite_toSet.injOn_iff_bijOn_of_mapsTo hmaps).mp ?_
  intro s hs t ht heq
  have hs1 : s ∈ admSetQ q n := hs
  have ht1 : t ∈ admSetQ q n := ht
  obtain ⟨w, rfl⟩ := exists_eq_append_falseQ hq hs1
  obtain ⟨v, rfl⟩ := exists_eq_append_falseQ hq ht1
  obtain ⟨k, hk, hkmax⟩ := exists_peak q w
  obtain ⟨m, hm, hmmax⟩ := exists_peak q v
  rw [cutSweepQ_eq_sweepQ_of_lowerRecordQ hodd hq hR hs1 hk hkmax,
    cutSweepQ_eq_sweepQ_of_lowerRecordQ hodd hq hR ht1 hm hmmax] at heq
  have hfl := (sweepQ_bijOn hodd hq hTW n).injOn
    (peakFlip_append_false_mem_admSetQ hodd hq hs1 hk hkmax)
    (peakFlip_append_false_mem_admSetQ hodd hq ht1 hm hmmax) heq
  obtain ⟨z, u, rfl, rfl⟩ := exists_rotation_of_peakFlip_eq (List.append_cancel_right hfl)
  rw [append_comm_of_lowerRecordQ hodd hq hR hs1 ht1]

/-! ### Orders that are no lower record -/

/-- Two cut parts in a row, with the halving: admissible when
    p2Q(a + b) + 1 = p2Q(a) + p2Q(b). -/
theorem append_cut_mem_admSetQ (hq : 3 ≤ q) {a b : ℕ} {x y : List Bool}
    (hx : x ++ [false] ∈ admSetQ q a) (hy : y ++ [false] ∈ admSetQ q b)
    (hp : p2Q q (a + b) + 1 = p2Q q a + p2Q q b) :
    x ++ y ++ [false] ∈ admSetQ q (a + b) := by
  have hox := order_cut hq hx
  have hoy := order_cut hq hy
  have hlx := length_cut hq hx
  have hly := length_cut hq hy
  have hq0 : 0 < q := by omega
  have hord : order (x ++ y ++ [false]) = a + b := by
    unfold order at hox hoy ⊢
    simp [List.filter_append, hox, hoy]
  have hlen : (x ++ y ++ [false]).length = p2Q q (a + b) := by
    rw [List.length_append, List.length_append, List.length_singleton]
    omega
  rw [mem_admSetQ (by omega)]
  refine ⟨⟨?_, ?_⟩, hord⟩
  · intro m hm1 hmL
    rw [List.length_append, List.length_append, List.length_singleton] at hmL
    change 1 < lvlQ q (x ++ y ++ [false]) m
    rcases Nat.lt_or_ge x.length m with hxm | hmx
    · obtain ⟨e, rfl⟩ : ∃ e, m = x.length + e := ⟨m - x.length, by omega⟩
      have hsplit : lvlQ q (x ++ y ++ [false]) (x.length + e) =
          seqProductQ q x * lvlQ q y e := by
        unfold lvlQ
        rw [List.append_assoc, List.take_length_add_append, seqProductQ_append,
          List.take_append_of_le_length (by omega)]
      rw [hsplit]
      have hxge : 1 ≤ seqProductQ q x := by
        rcases Nat.eq_zero_or_pos x.length with h0 | hpos
        · rw [List.length_eq_zero_iff.mp h0]
          simp [seqProductQ]
        · have h := one_lt_lvlQ_cut hq hx hpos le_rfl
          rw [lvlQ_length] at h
          exact h.le
      have hy1 := one_lt_lvlQ_cut hq hy (j := e) (by omega) (by omega)
      nlinarith
    · rw [List.append_assoc, lvlQ_append_left q hmx]
      exact one_lt_lvlQ_cut hq hx hm1 hmx
  · have h := seqProductQ_mul_pow q (x ++ y ++ [false])
    rw [hord, hlen] at h
    have hspec : (q : ℚ) ^ (a + b) < 2 ^ p2Q q (a + b) := by
      exact_mod_cast p2Q_spec hq (a + b)
    have hpos : (0 : ℚ) < 2 ^ p2Q q (a + b) := by positivity
    by_contra hge
    push Not at hge
    have := mul_le_mul_of_nonneg_right hge hpos.le
    linarith

theorem p2Q_three_one : p2Q 3 1 = 2 := by
  unfold p2Q
  rw [Nat.log_eq_of_pow_le_of_lt_pow (m := 1) (by norm_num) (by norm_num)]

theorem p2Q_three_two : p2Q 3 2 = 4 := by
  unfold p2Q
  rw [Nat.log_eq_of_pow_le_of_lt_pow (m := 3) (by norm_num) (by norm_num)]

/-- At an Order that is no lower record some admissible word is not a cut sweep. -/
theorem not_surjOn_cutSweepQ (hodd : Odd q) (hq : 3 ≤ q) {n : ℕ} (hR : ¬LowerRecordQ q n) :
    ¬Set.SurjOn (cutSweepQ q) (admSetQ q n : Set (List Bool)) (admSetQ q n) := by
  have hq0 : 0 < q := by omega
  rw [lowerRecordQ_iff_blockFactorQ hq] at hR
  push Not at hR
  obtain ⟨a0, ha01, ha0n, ha0⟩ := hR
  have ha0I : a0 ∈ Finset.Icc 1 (n - 1) := Finset.mem_Icc.mpr ⟨ha01, by omega⟩
  obtain ⟨a, haI, hmin⟩ := Finset.exists_min_image (Finset.Icc 1 (n - 1)) (blockFactorQ q)
    ⟨a0, ha0I⟩
  rw [Finset.mem_Icc] at haI
  have han : blockFactorQ q a ≤ blockFactorQ q n := (hmin a0 ha0I).trans ha0
  obtain ⟨b, rfl⟩ : ∃ b, n = a + b := ⟨n - a, by omega⟩
  have hb1 : 1 ≤ b := by omega
  have hp : p2Q q (a + b) + 1 = p2Q q a + p2Q q b := by
    have h1 := p2Q_add_le hq a b
    have h2 := p2Q_add_le_succ hq a b
    have h3 := (blockFactorQ_add_lt_iff hq a b).not.mp (not_lt.mpr han)
    omega
  have hlt : blockFactorQ q a < blockFactorQ q (a + b) :=
    (blockFactorQ_lt_add_iff hodd hq a hb1).mpr hp
  rw [blockFactorQ_lt_iff] at hlt
  have hminN : ∀ o, 1 ≤ o → o < a + b → q ^ a * 2 ^ p2Q q o ≤ q ^ o * 2 ^ p2Q q a := by
    intro o ho1 hon
    have h := hmin o (Finset.mem_Icc.mpr ⟨ho1, by omega⟩)
    exact not_lt.mp ((blockFactorQ_lt_iff q o a).not.mp (not_lt.mpr h))
  have hp3 : 3 ≤ p2Q q a := by
    by_contra hsmall
    have hpow : q ^ a < 2 ^ 2 := (q_pow_lt_two_pow_iff hq).mpr (by omega)
    have hqa : q ≤ q ^ a := Nat.le_self_pow (by omega) q
    have hq3 : q = 3 := by omega
    subst hq3
    have ha1 : a = 1 := by
      by_contra hne
      have h9 : 3 ^ 2 ≤ 3 ^ a := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    subst ha1
    rcases Nat.lt_or_ge b 2 with hb | hb
    · have hb' : b = 1 := by omega
      subst hb'
      rw [p2Q_three_two, p2Q_three_one] at hp
      omega
    · have h := hminN 2 (by omega) (by omega)
      rw [p2Q_three_two, p2Q_three_one] at h
      omega
  have hxa := upDownQ_mem_admSetQ hodd hq a
  have hyb := upDownQ_mem_admSetQ hodd hq b
  obtain ⟨x, hx⟩ := exists_eq_append_falseQ hq hxa
  obtain ⟨y, hy⟩ := exists_eq_append_falseQ hq hyb
  rw [hx] at hxa
  rw [hy] at hyb
  have ht0 := append_cut_mem_admSetQ hq hxa hyb hp
  intro hsurj
  obtain ⟨s, hs, hst⟩ := hsurj ht0
  have hs1 : s ∈ admSetQ q (a + b) := hs
  obtain ⟨w, rfl⟩ := exists_eq_append_falseQ hq hs1
  rw [cutSweepQ_append_false] at hst
  have hsw : startSweepQ q w = x ++ y := List.append_cancel_right hst
  have hlx := length_cut hq hxa
  have hly := length_cut hq hyb
  have hlw := length_cut hq hs1
  have hbp := lt_p2Q hq b
  obtain ⟨T, k, hcard, h0T, hkT, hk1, hkL, hTk, hbound⟩ :=
    exists_startSweepQ_prefix_bound hodd hq hs1 (m := x.length) (by omega) (by omega)
  rw [hsw, List.take_left] at hbound
  have hmu := seqProductQ_mul_pow q x
  rw [order_cut hq hxa] at hmu
  have hE := lvlQ_mul_pow q (s := w) (j := w.length) le_rfl
  rw [List.take_length, order_cut hq hs1] at hE
  have hltN : q ^ a * 2 ^ w.length < q ^ (a + b) * 2 ^ x.length := by
    rw [← hlw, ← hlx, pow_succ, pow_succ, ← mul_assoc, ← mul_assoc] at hlt
    exact Nat.lt_of_mul_lt_mul_right hlt
  have hltQ : (q : ℚ) ^ a * 2 ^ w.length < (q : ℚ) ^ (a + b) * 2 ^ x.length := by
    exact_mod_cast hltN
  have hmuE : seqProductQ q x < lvlQ q w w.length := by
    have hpos : (0 : ℚ) < 2 ^ x.length * 2 ^ w.length := by positivity
    have h1 : seqProductQ q x * (2 ^ x.length * 2 ^ w.length) =
        (q : ℚ) ^ a * 2 ^ w.length := by
      rw [← hmu]
      ring
    have h2 : lvlQ q w w.length * (2 ^ x.length * 2 ^ w.length) =
        (q : ℚ) ^ (a + b) * 2 ^ x.length := by
      rw [← hE]
      ring
    apply lt_of_mul_lt_mul_right _ hpos.le
    rw [h1, h2]
    exact hltQ
  have hc : lvlQ q w k ≤ seqProductQ q x := by
    rcases min_le_iff.mp hbound with h | h
    · linarith
    · exact h
  have hlow : ∀ j, 1 ≤ j → j < w.length → seqProductQ q x ≤ lvlQ q w j := by
    intro j hj1 hjL
    have hj := lvlQ_mul_pow q (s := w) (j := j) hjL.le
    have hgt := one_lt_lvlQ_cut hq hs1 hj1 hjL.le
    have hon : order (w.take j) ≤ a + b := order_cut hq hs1 ▸ order_take_le w j
    have h2j : 2 ^ j < q ^ order (w.take j) := by
      have h2pos : (0 : ℚ) < 2 ^ j := by positivity
      have hQ : (2 : ℚ) ^ j < (q : ℚ) ^ order (w.take j) := by
        rw [← hj]
        nlinarith
      exact_mod_cast hQ
    have ho1 : 1 ≤ order (w.take j) := by
      by_contra h0
      have ho0 : order (w.take j) = 0 := by omega
      rw [ho0, pow_zero] at h2j
      have := Nat.one_le_two_pow (n := j)
      omega
    have hjo := (two_pow_lt_q_pow_iff hodd hq ho1).mp h2j
    have hkey : q ^ a * 2 ^ j ≤ q ^ order (w.take j) * 2 ^ x.length := by
      rcases Nat.lt_or_ge (order (w.take j)) (a + b) with hlt' | hge'
      · have h1 := hminN _ ho1 hlt'
        rw [← hlx, pow_succ, ← mul_assoc] at h1
        have hpow : 2 ^ (j + 1) ≤ 2 ^ p2Q q (order (w.take j)) :=
          Nat.pow_le_pow_right (by norm_num) (by omega)
        have h2 : q ^ a * 2 ^ (j + 1) ≤ q ^ a * 2 ^ p2Q q (order (w.take j)) :=
          Nat.mul_le_mul_left _ hpow
        rw [pow_succ, ← mul_assoc] at h2
        exact Nat.le_of_mul_le_mul_right (h2.trans h1) (by norm_num)
      · have heq : order (w.take j) = a + b := by omega
        rw [heq]
        have hpow : 2 ^ j ≤ 2 ^ w.length := Nat.pow_le_pow_right (by norm_num) hjL.le
        exact (Nat.mul_le_mul_left _ hpow).trans hltN.le
    have hkeyQ : (q : ℚ) ^ a * 2 ^ j ≤ (q : ℚ) ^ order (w.take j) * 2 ^ x.length := by
      exact_mod_cast hkey
    have hpos : (0 : ℚ) < 2 ^ x.length * 2 ^ j := by positivity
    have h1 : seqProductQ q x * (2 ^ x.length * 2 ^ j) = (q : ℚ) ^ a * 2 ^ j := by
      rw [← hmu]
      ring
    have h2 : lvlQ q w j * (2 ^ x.length * 2 ^ j) =
        (q : ℚ) ^ order (w.take j) * 2 ^ x.length := by
      rw [← hj]
      ring
    apply le_of_mul_le_mul_right _ hpos
    rw [h1, h2]
    exact hkeyQ
  have hS : (insert k T).card = x.length + 1 := by
    rw [Finset.card_insert_of_notMem hkT, hcard]
  have h2 : 1 < ((insert k T).erase 0).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_insert_of_mem h0T), hS]
    omega
  obtain ⟨i1, hi1, i2, hi2, hne⟩ := Finset.one_lt_card.mp h2
  have hall : ∀ i ∈ (insert k T).erase 0,
      1 ≤ i ∧ i < w.length ∧ lvlQ q w i ≤ seqProductQ q x := by
    intro i hi
    rw [Finset.mem_erase, Finset.mem_insert] at hi
    refine ⟨by omega, ?_, ?_⟩
    · rcases hi.2 with rfl | hiT
      · exact hkL
      · exact (hTk i hiT).1
    · rcases hi.2 with rfl | hiT
      · exact hc
      · exact ((hTk i hiT).2.le).trans hc
  obtain ⟨h11, h12, h13⟩ := hall i1 hi1
  obtain ⟨h21, h22, h23⟩ := hall i2 hi2
  have e1 := le_antisymm h13 (hlow i1 h11 h12)
  have e2 := le_antisymm h23 (hlow i2 h21 h22)
  exact lvlQ_ne_of_ne hodd h12.le h22.le hne (e1.trans e2.symm)

/-- At an Order that is no lower record two admissible words have the same cut sweep. -/
theorem not_injOn_cutSweepQ (hodd : Odd q) (hq : 3 ≤ q) {n : ℕ} (hR : ¬LowerRecordQ q n) :
    ¬Set.InjOn (cutSweepQ q) (admSetQ q n : Set (List Bool)) := by
  have hmaps : Set.MapsTo (cutSweepQ q) (admSetQ q n : Set (List Bool)) (admSetQ q n) :=
    fun s hs => cutSweepQ_mem_admSetQ hodd hq hs
  intro hinj
  exact not_surjOn_cutSweepQ hodd hq hR
    (((admSetQ q n).finite_toSet.injOn_iff_bijOn_of_mapsTo hmaps).mp hinj).surjOn

/-- Under Thomas and Williams, Thm 6.3, the cut sweep permutes the admissible words of
    Order n exactly at the lower record Orders. -/
theorem cutSweepQ_bijOn_iff (hodd : Odd q) (hq : 3 ≤ q) (hTW : SweepBijective) (n : ℕ) :
    Set.BijOn (cutSweepQ q) (admSetQ q n : Set (List Bool)) (admSetQ q n) ↔
      LowerRecordQ q n := by
  constructor
  · intro h
    by_contra hR
    exact not_surjOn_cutSweepQ hodd hq hR h.surjOn
  · exact cutSweepQ_bijOn hodd hq hTW

end AcceleratedCollatz
