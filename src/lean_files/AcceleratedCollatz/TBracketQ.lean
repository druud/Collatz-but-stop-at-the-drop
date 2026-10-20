-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TBracket
import AcceleratedCollatz.TSplitQ

/-!
  Bracket words of the q-family (q ≥ 3). An odd step multiplies the level by q/2,
  which lies in [2^(e-1), 2^e) for e = `bracketsQ q`, the largest e with 2^e ≤ q. So an
  odd position i opens e brackets, with the thresholds 2^m lvlQ q s i for m < e;
  bracket m closes at the first j > i whose level is below its threshold (`LvlDropQ`).
  Closes are counted per column, the positions k < j ≤ k' from an odd position k to the
  next odd position k' (or the end); the bracket word lists these counts, one per odd
  position. For every level t with 1 < t ≤ lvlQ q s p some open bracket has its
  threshold in (t/2, t] (`lvlQ_gap`), so every halving inside an admissible word closes
  a bracket (`closesAtQ_pos_of_halving`), and the bracket word determines the word
  (`bracketWordQ_injective`). For q = 3 an odd step opens one bracket and this is the
  bracket word of TBracket (`bracketWordQ_three`). With one bracket per odd step
  (`colCountOne`) the close counts do not determine the word for q = 5: the checks at the
  end show two admissible words with the same counts; for every odd q ≥ 5 this is
  `not_injOn_bracketWordOneQ` (TBracketClashQ).
-/

namespace AcceleratedCollatz

variable {q : ℕ}

/-- Number of brackets an odd step opens: the largest e with 2^e ≤ q. -/
def bracketsQ (q : ℕ) : ℕ := Nat.log 2 q

/-- Bracket m of position i closes at j: j is the first index after i whose level is
    below 2^m lvlQ q s i. -/
def LvlDropQ (q : ℕ) (s : List Bool) (i m j : ℕ) : Prop :=
  i < j ∧ lvlQ q s j < 2 ^ m * lvlQ q s i ∧ ∀ k < j, i < k → 2 ^ m * lvlQ q s i ≤ lvlQ q s k

instance (q : ℕ) (s : List Bool) (i m j : ℕ) : Decidable (LvlDropQ q s i m j) := by
  unfold LvlDropQ
  infer_instance

/-- Number of brackets, opened at odd positions, closing at j. -/
def closesAtQ (q : ℕ) (s : List Bool) (j : ℕ) : ℕ :=
  ((Finset.range j ×ˢ Finset.range (bracketsQ q)).filter
    (fun x => s[x.1]? = some true ∧ LvlDropQ q s x.1 x.2 j)).card

/-- Closes in the column of k: positions k < j ≤ nextOdd s k. -/
def colCountQ (q : ℕ) (s : List Bool) (k : ℕ) : ℕ :=
  ∑ j ∈ Finset.Ioc k (nextOdd s k), closesAtQ q s j

/-- Bracket word: close counts per column, one entry per odd position. -/
def bracketWordQ (q : ℕ) (s : List Bool) : List ℕ := (oddPos s).map (colCountQ q s)

/-- q/2 < 2^e for e = `bracketsQ q`. -/
theorem half_lt_two_pow_bracketsQ (q : ℕ) : (q : ℚ) / 2 < 2 ^ bracketsQ q := by
  have hnat : q < 2 ^ (bracketsQ q + 1) := Nat.lt_pow_succ_log_self (by norm_num) q
  have hcast : (q : ℚ) < 2 ^ (bracketsQ q + 1) := by
    exact_mod_cast hnat
  rw [pow_succ] at hcast
  linarith

/-- A level t in [L, 2^e L) lies in one band [2^m L, 2^(m+1) L) with m < e. -/
theorem exists_pow_band : ∀ (e : ℕ) (L t : ℚ), L ≤ t → t < 2 ^ e * L →
    ∃ m < e, 2 ^ m * L ≤ t ∧ t < 2 ^ (m + 1) * L
  | 0, L, t, h1, h2 => by
    rw [pow_zero, one_mul] at h2
    linarith
  | e + 1, L, t, h1, h2 => by
    by_cases h : t < 2 ^ e * L
    · obtain ⟨m, hm, h3, h4⟩ := exists_pow_band e L t h1 h
      exact ⟨m, by omega, h3, h4⟩
    · exact ⟨e, by omega, not_lt.mp h, h2⟩

/-- Open brackets at p: for every level 1 < t ≤ lvlQ q s p some bracket m of an odd
    i < p, still open at p, has 2^m lvlQ q s i ≤ t < 2^(m+1) lvlQ q s i. -/
theorem lvlQ_gap (hq : 3 ≤ q) (s : List Bool) :
    ∀ p, p ≤ s.length → ∀ t : ℚ, 1 < t → t ≤ lvlQ q s p →
      ∃ i < p, ∃ m < bracketsQ q, s[i]? = some true ∧
        (∀ j, i < j → j ≤ p → 2 ^ m * lvlQ q s i ≤ lvlQ q s j) ∧
          2 ^ m * lvlQ q s i ≤ t ∧ t < 2 ^ (m + 1) * lvlQ q s i := by
  intro p
  induction p with
  | zero =>
    intro _ t h1 ht
    rw [lvlQ_zero] at ht
    linarith
  | succ p ih =>
    intro hp t h1 ht
    have hlt : p < s.length := by omega
    have hsb : s[p]? = some s[p] := List.getElem?_eq_getElem hlt
    have hpos := lvlQ_pos (by omega : 0 < q) s p
    cases hb : s[p] with
    | true =>
      rw [hb] at hsb
      have hstep : lvlQ q s (p + 1) = lvlQ q s p * ((q : ℚ) / 2) := by
        rw [lvlQ_succ q s hsb]
        simp [factorQ]
      by_cases htp : t ≤ lvlQ q s p
      · obtain ⟨i, hip, m, hm, hodd, hmin, hle, hlt2⟩ := ih (by omega) t h1 htp
        refine ⟨i, by omega, m, hm, hodd, ?_, hle, hlt2⟩
        intro j hij hj
        rcases (by omega : j ≤ p ∨ j = p + 1) with hjp | rfl
        · exact hmin j hij hjp
        · linarith
      · push Not at htp
        have hband : t < 2 ^ bracketsQ q * lvlQ q s p := by
          have hmul := mul_lt_mul_of_pos_left (half_lt_two_pow_bracketsQ q) hpos
          rw [hstep] at ht
          linarith
        obtain ⟨m, hm, h3, h4⟩ := exists_pow_band (bracketsQ q) (lvlQ q s p) t htp.le hband
        refine ⟨p, by omega, m, hm, hsb, ?_, h3, h4⟩
        intro j hij hj
        have hj' : j = p + 1 := by
          omega
        rw [hj']
        linarith
    | false =>
      rw [hb] at hsb
      have hstep : lvlQ q s (p + 1) = lvlQ q s p * (1 / 2) := by
        rw [lvlQ_succ q s hsb]
        simp [factorQ]
      have htp : t ≤ lvlQ q s p := by
        rw [hstep] at ht
        linarith
      obtain ⟨i, hip, m, hm, hodd, hmin, hle, hlt2⟩ := ih (by omega) t h1 htp
      refine ⟨i, by omega, m, hm, hodd, ?_, hle, hlt2⟩
      intro j hij hj
      rcases (by omega : j ≤ p ∨ j = p + 1) with hjp | rfl
      · exact hmin j hij hjp
      · linarith

/-- A halving at p with level > 1 closes a bracket opened at an odd i < p. -/
theorem exists_lvlDropQ_of_halving (hq : 3 ≤ q) (s : List Bool) {p : ℕ} (hp : p < s.length)
    (hf : s[p]? = some false) (h1 : 1 < lvlQ q s p) :
    ∃ i < p, ∃ m < bracketsQ q, s[i]? = some true ∧ LvlDropQ q s i m (p + 1) := by
  obtain ⟨i, hip, m, hm, hodd, hmin, _, hlt⟩ := lvlQ_gap hq s p hp.le (lvlQ q s p) h1 le_rfl
  have hstep : lvlQ q s (p + 1) = lvlQ q s p * (1 / 2) := by
    rw [lvlQ_succ q s hf]
    simp [factorQ]
  have hdrop : lvlQ q s (p + 1) < 2 ^ m * lvlQ q s i := by
    rw [hstep]
    rw [pow_succ] at hlt
    linarith
  refine ⟨i, hip, m, hm, hodd, by omega, hdrop, ?_⟩
  intro k hk hik
  exact hmin k hik (by omega)

/-- Every halving at 1 ≤ p inside an admissible word closes a bracket at p + 1. -/
theorem closesAtQ_pos_of_halving (hq : 3 ≤ q) {s : List Bool} (hA : AdmissibleQ q s) {p : ℕ}
    (hp1 : 1 ≤ p) (hp : p < s.length) (hf : s[p]? = some false) :
    0 < closesAtQ q s (p + 1) := by
  obtain ⟨i, hip, m, hm, hodd, hdrop⟩ :=
    exists_lvlDropQ_of_halving hq s hp hf (hA.prefix_gt p hp1 hp)
  exact Finset.card_pos.mpr ⟨(i, m), Finset.mem_filter.mpr
    ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr hm⟩,
      hodd, hdrop⟩⟩

theorem lvlQ_eq_of_take {s s' : List Bool} {p j : ℕ} (h : s.take p = s'.take p)
    (hj : j ≤ p) : lvlQ q s j = lvlQ q s' j := by
  have := congrArg (List.take j) h
  simp only [List.take_take, min_eq_left hj] at this
  simp [lvlQ, this]

theorem closesAtQ_eq_of_take {s s' : List Bool} {p j : ℕ} (h : s.take p = s'.take p)
    (hj : j ≤ p) : closesAtQ q s j = closesAtQ q s' j := by
  have hl : ∀ r, r ≤ j → lvlQ q s r = lvlQ q s' r := fun r hr => lvlQ_eq_of_take h (by omega)
  unfold closesAtQ
  congr 1
  apply Finset.filter_congr
  rintro ⟨i, m⟩ hx
  have hi' := Finset.mem_range.mp (Finset.mem_product.mp hx).1
  change (s[i]? = some true ∧ LvlDropQ q s i m j) ↔ (s'[i]? = some true ∧ LvlDropQ q s' i m j)
  rw [getElem?_eq_of_take h (by omega)]
  unfold LvlDropQ
  rw [hl j le_rfl, hl i (by omega)]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨h1, h2, h3, fun k hk1 hk2 => ?_⟩
    rw [← hl k (by omega)]
    exact h4 k hk1 hk2
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨h1, h2, h3, fun k hk1 hk2 => ?_⟩
    rw [hl k (by omega)]
    exact h4 k hk1 hk2

/-- An admissible word starting with a halving is [false]. -/
theorem eq_single_of_admissibleQ_false {s : List Bool} (hA : AdmissibleQ q s)
    (h0 : s[0]? = some false) : s = [false] := by
  rcases s with _ | ⟨b, t⟩
  · simp at h0
  · simp only [List.getElem?_cons_zero, Option.some.injEq] at h0
    subst h0
    rcases t with _ | ⟨c, u⟩
    · rfl
    · exfalso
      have h := hA.prefix_gt 1 le_rfl (by simp)
      norm_num [seqProductQ, factorQ] at h

theorem bracketWordQ_singleton_false (q : ℕ) : bracketWordQ q [false] = [] := by
  have h : oddPos [false] = [] := by
    decide
  simp [bracketWordQ, h]

/-- Two admissible words that agree before p, with a halving at p in s and an odd step
    at p in s', have different bracket words. -/
theorem bracketWordQ_ne_of_split (hq : 3 ≤ q) {s s' : List Bool} (hA : AdmissibleQ q s)
    (hA' : AdmissibleQ q s') {p : ℕ} (htake : s.take p = s'.take p)
    (hf : s[p]? = some false) (ht : s'[p]? = some true) :
    bracketWordQ q s ≠ bracketWordQ q s' := by
  intro hw
  have hpN : p < s.length := (List.getElem?_eq_some_iff.mp hf).1
  have hpN' : p < s'.length := (List.getElem?_eq_some_iff.mp ht).1
  rcases Nat.eq_zero_or_pos p with hp0 | hp1
  · subst hp0
    have hs := eq_single_of_admissibleQ_false hA hf
    have h0 : 0 ∈ oddPos s' := List.mem_filter.mpr ⟨List.mem_range.mpr hpN', by simp [ht]⟩
    have hne : bracketWordQ q s' ≠ [] := by
      simp only [bracketWordQ, ne_eq, List.map_eq_nil_iff]
      exact List.ne_nil_of_mem h0
    apply hne
    rw [← hw, hs]
    exact bracketWordQ_singleton_false q
  -- s' starts with an odd step, hence so does s
  have hs'0 : s'[0]? = some true := by
    rcases hb : s'[0]? with _ | b
    · rw [List.getElem?_eq_none_iff] at hb
      omega
    · cases b
      · have := eq_single_of_admissibleQ_false hA' hb
        subst this
        simp at hpN'
        omega
      · rfl
  have hs0 : s[0]? = some true := by
    rw [getElem?_eq_of_take htake hp1]
    exact hs'0
  -- k: last odd position before p
  set P : ℕ → Prop := fun i => s[i]? = some true with hP
  set k := Nat.findGreatest P (p - 1) with hk
  have hPk : P k := Nat.findGreatest_spec (m := 0) (by omega) hs0
  have hkp : k < p := by
    have := Nat.findGreatest_le (P := P) (p - 1)
    omega
  have hgt : ∀ m, k < m → m < p → ¬ P m :=
    fun m hkm hmp => Nat.findGreatest_is_greatest hkm (by omega)
  -- column counts at k agree
  have hA_eq : (List.range p).filter (fun i => s'[i]? = some true) =
      (List.range p).filter (fun i => s[i]? = some true) := by
    apply List.filter_congr
    intro i hi
    rw [getElem?_eq_of_take htake (List.mem_range.mp hi)]
  have hcol : colCountQ q s k = colCountQ q s' k := by
    have e1 := oddPos_split s hpN.le
    have e2 := oddPos_split s' hpN'.le
    rw [hA_eq] at e2
    set A := (List.range p).filter (fun i => s[i]? = some true)
    have hmap : A.map (colCountQ q s) = A.map (colCountQ q s') := by
      have := congrArg (List.take A.length) hw
      unfold bracketWordQ at this
      rw [e1, e2, List.map_append, List.map_append, List.take_left' (by simp),
        List.take_left' (by simp)] at this
      exact this
    have hkA : k ∈ A := List.mem_filter.mpr ⟨List.mem_range.mpr hkp, by simpa [hP] using hPk⟩
    exact List.map_inj_left.mp hmap k hkA
  -- next odd positions
  have hn' : nextOdd s' k = p := by
    have hex : ∃ m, m < s'.length ∧ k < m ∧ s'[m]? = some true := ⟨p, hpN', hkp, ht⟩
    unfold nextOdd
    split_ifs
    rw [Nat.find_eq_iff]
    refine ⟨⟨hpN', hkp, ht⟩, ?_⟩
    rintro n hn ⟨_, hkn, hodd⟩
    have hsn : s[n]? = some true := by
      rw [getElem?_eq_of_take htake hn]
      exact hodd
    exact hgt n hkn hn hsn
  have hn : p + 1 ≤ nextOdd s k := by
    unfold nextOdd
    split_ifs with hex
    · apply Nat.succ_le_of_lt
      rw [Nat.lt_find_iff]
      rintro m hm ⟨_, hkm, hodd⟩
      rcases hm.lt_or_eq with hmp | rfl
      · exact hgt m hkm hmp hodd
      · rw [hf] at hodd
        simp at hodd
    · omega
  -- compare the sums
  have hsum' : colCountQ q s' k = ∑ j ∈ Finset.Ioc k p, closesAtQ q s j := by
    unfold colCountQ
    rw [hn']
    apply Finset.sum_congr rfl
    intro j hj
    exact (closesAtQ_eq_of_take htake (Finset.mem_Ioc.mp hj).2).symm
  have hsum : ∑ j ∈ Finset.Ioc k p, closesAtQ q s j + closesAtQ q s (p + 1) ≤
      colCountQ q s k := by
    unfold colCountQ
    rw [← Finset.sum_Ioc_succ_top hkp.le]
    exact Finset.sum_le_sum_of_subset (Finset.Ioc_subset_Ioc_right hn)
  have hpos := closesAtQ_pos_of_halving hq hA hp1 hpN hf
  omega

/-- The bracket word determines an admissible word. -/
theorem bracketWordQ_injective (hq : 3 ≤ q) {s s' : List Bool} (hA : AdmissibleQ q s)
    (hA' : AdmissibleQ q s') (hw : bracketWordQ q s = bracketWordQ q s') : s = s' := by
  by_contra hne
  have hex : ∃ p : ℕ, s[p]? ≠ s'[p]? := by
    by_contra hall
    push Not at hall
    exact hne (List.ext_getElem? hall)
  set p := Nat.find hex
  have hp : s[p]? ≠ s'[p]? := Nat.find_spec hex
  have htake : s.take p = s'.take p := by
    apply List.ext_getElem?
    intro i
    by_cases hi : i < p
    · simp only [List.getElem?_take, hi, ite_true]
      by_contra h
      exact Nat.find_min hex hi h
    · simp [hi]
  -- an admissible word is not a proper prefix of another one
  have hpre : ∀ {u v : List Bool}, AdmissibleQ q u → AdmissibleQ q v → u.length < v.length →
      v.take u.length ≠ u := by
    intro u v hu hv hlt heq
    have hu1 : 1 ≤ u.length := List.length_pos_iff.mpr (ne_nil_of_admissibleQ hu)
    have h := hv.prefix_gt u.length hu1 hlt
    rw [heq] at h
    linarith [hu.lt_one]
  rcases hsp : s[p]? with _ | b
  · rcases hsp' : s'[p]? with _ | b'
    · exact hp (by rw [hsp, hsp'])
    · have hle : s.length ≤ p := List.getElem?_eq_none_iff.mp hsp
      have hlt : p < s'.length := (List.getElem?_eq_some_iff.mp hsp').1
      apply hpre hA hA' (by omega)
      calc s'.take s.length = (s'.take p).take s.length := by rw [List.take_take, min_eq_left hle]
        _ = (s.take p).take s.length := by rw [htake]
        _ = s := by rw [List.take_take, min_eq_left hle, List.take_length]
  · rcases hsp' : s'[p]? with _ | b'
    · have hle : s'.length ≤ p := List.getElem?_eq_none_iff.mp hsp'
      have hlt : p < s.length := (List.getElem?_eq_some_iff.mp hsp).1
      apply hpre hA' hA (by omega)
      calc s.take s'.length = (s.take p).take s'.length := by rw [List.take_take, min_eq_left hle]
        _ = (s'.take p).take s'.length := by rw [htake]
        _ = s' := by rw [List.take_take, min_eq_left hle, List.take_length]
    · have hbb : b ≠ b' := by
        intro h
        subst h
        exact hp (by rw [hsp, hsp'])
      cases b
      · cases b'
        · exact hbb rfl
        · exact bracketWordQ_ne_of_split hq hA hA' htake hsp hsp' hw
      · cases b'
        · exact bracketWordQ_ne_of_split hq hA' hA htake.symm hsp' hsp hw.symm
        · exact hbb rfl

/-! ### q = 3 -/

theorem bracketsQ_three : bracketsQ 3 = 1 := by
  decide

/-- For q = 3 the one bracket of an odd step is the bracket of TBracket. -/
theorem lvlDropQ_three (s : List Bool) (i j : ℕ) : LvlDropQ 3 s i 0 j ↔ LvlDrop s i j := by
  unfold LvlDropQ LvlDrop
  simp only [pow_zero, one_mul, lvlQ_three]

theorem closesAtQ_three (s : List Bool) (j : ℕ) : closesAtQ 3 s j = closesAt s j := by
  unfold closesAtQ closesAt
  rw [bracketsQ_three]
  apply Finset.card_bij (fun x _ => x.1)
  · intro x hx
    obtain ⟨hmem, hodd, hdrop⟩ := Finset.mem_filter.mp hx
    obtain ⟨h1, h2⟩ := Finset.mem_product.mp hmem
    have hm : x.2 = 0 := by
      have := Finset.mem_range.mp h2
      omega
    rw [hm, lvlDropQ_three] at hdrop
    exact Finset.mem_filter.mpr ⟨h1, hodd, hdrop⟩
  · intro x hx y hy hxy
    have hx2 := Finset.mem_range.mp (Finset.mem_product.mp (Finset.mem_filter.mp hx).1).2
    have hy2 := Finset.mem_range.mp (Finset.mem_product.mp (Finset.mem_filter.mp hy).1).2
    exact Prod.ext hxy (by omega)
  · intro i hi
    obtain ⟨h1, hodd, hdrop⟩ := Finset.mem_filter.mp hi
    refine ⟨(i, 0), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨h1, by simp⟩, hodd, ?_⟩, rfl⟩
    exact (lvlDropQ_three s i j).mpr hdrop

/-- For q = 3 the bracket word is that of TBracket. -/
theorem bracketWordQ_three (s : List Bool) : bracketWordQ 3 s = bracketWord s := by
  unfold bracketWordQ bracketWord
  apply List.map_congr_left
  intro k _
  unfold colCountQ colCount
  exact Finset.sum_congr rfl (fun j _ => closesAtQ_three s j)

/-! ### One bracket per odd step is not enough for q = 5 -/

/-- Closes in the column of k when an odd step opens the bracket m = 0 only. -/
def colCountOne (q : ℕ) (s : List Bool) (k : ℕ) : ℕ :=
  ∑ j ∈ Finset.Ioc k (nextOdd s k),
    ((Finset.range j).filter (fun i => s[i]? = some true ∧ LvlDropQ q s i 0 j)).card

-- q = 5: with one bracket per odd step the admissible words 10100 and 11000 get the same
-- close counts; their bracket words differ, as those of all 14 words of Order 4 do.
set_option linter.hashCommand false in
#guard [[true, false, true, false, false], [true, true, false, false, false]].map
    (fun s => decide (AdmissibleQ 5 s)) = [true, true]

set_option linter.hashCommand false in
#guard [[true, false, true, false, false], [true, true, false, false, false]].map
    (fun s => (oddPos s).map (colCountOne 5 s)) = [[0, 2], [0, 2]]

set_option linter.hashCommand false in
#guard [[true, false, true, false, false], [true, true, false, false, false]].map
    (bracketWordQ 5) = [[1, 3], [0, 4]]

set_option linter.hashCommand false in
#guard ((admSetQ 5 4).image (bracketWordQ 5)).card = 14

end AcceleratedCollatz
