-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TChain

/-!
  Bracket words. The level of a word s after j steps is `lvl s j`, the product
  of its first j factors. A bracket opens at every odd position i and closes at
  its first drop j (`LvlDrop`): the first j > i with a level below `lvl s i`.
  Closes are counted per column, the positions k < j ≤ k' from an odd position k
  to the next odd position k' (or the end); the bracket word lists these counts,
  one per odd position. The open brackets keep consecutive levels within a
  factor 2 (`lvl_gap`), so every halving inside an admissible word closes a
  bracket (`closesAt_pos_of_halving`), and the bracket word determines the word
  (`bracketWord_injective`).
-/

namespace AcceleratedCollatz

/-- Level of s after j steps. -/
def lvl (s : List Bool) (j : ℕ) : ℚ := seqProduct (s.take j)

/-- j is the first index after i whose level is below lvl s i. -/
def LvlDrop (s : List Bool) (i j : ℕ) : Prop :=
  i < j ∧ lvl s j < lvl s i ∧ ∀ k < j, i < k → lvl s i ≤ lvl s k

instance (s : List Bool) (i j : ℕ) : Decidable (LvlDrop s i j) := by
  unfold LvlDrop
  infer_instance

/-- Number of brackets, opened at odd positions, closing at j. -/
def closesAt (s : List Bool) (j : ℕ) : ℕ :=
  ((Finset.range j).filter (fun i => s[i]? = some true ∧ LvlDrop s i j)).card

/-- Next odd position after k, or the length of s. -/
def nextOdd (s : List Bool) (k : ℕ) : ℕ :=
  if h : ∃ m, m < s.length ∧ k < m ∧ s[m]? = some true then Nat.find h else s.length

/-- Closes in the column of k: positions k < j ≤ nextOdd s k. -/
def colCount (s : List Bool) (k : ℕ) : ℕ :=
  ∑ j ∈ Finset.Ioc k (nextOdd s k), closesAt s j

/-- Odd positions of s, increasing. -/
def oddPos (s : List Bool) : List ℕ :=
  (List.range s.length).filter (fun i => s[i]? = some true)

/-- Bracket word: close counts per column, one entry per odd position. -/
def bracketWord (s : List Bool) : List ℕ := (oddPos s).map (colCount s)

/-- For q = 3 the level of the q-family is `lvl`. -/
theorem lvlQ_three : lvlQ 3 = lvl := by
  funext s j
  simp [lvlQ, lvl, seqProductQ_three]

theorem lvl_zero (s : List Bool) : lvl s 0 = 1 := by
  simp [lvl, seqProduct]

theorem lvl_pos (s : List Bool) (j : ℕ) : 0 < lvl s j := seqProduct_pos _

theorem lvl_succ (s : List Bool) {p : ℕ} {b : Bool} (h : s[p]? = some b) :
    lvl s (p + 1) = lvl s p * factor b := by
  unfold lvl
  rw [List.take_add_one, h, seqProduct_append]
  simp [seqProduct]

/-- Open brackets at p: for every level 1 < t ≤ lvl s p some odd i ≤ p, still
    open at p, has lvl s i ≤ t < 2 lvl s i. -/
theorem lvl_gap (s : List Bool) :
    ∀ p, p ≤ s.length → ∀ t : ℚ, 1 < t → t ≤ lvl s p →
      ∃ i ≤ p, s[i]? = some true ∧ (∀ j, i ≤ j → j ≤ p → lvl s i ≤ lvl s j) ∧
        lvl s i ≤ t ∧ t < 2 * lvl s i := by
  intro p
  induction p with
  | zero =>
    intro _ t h1 ht
    rw [lvl_zero] at ht
    linarith
  | succ p ih =>
    intro hp t h1 ht
    have hlt : p < s.length := by omega
    have hsb : s[p]? = some s[p] := List.getElem?_eq_getElem hlt
    have hpos := lvl_pos s p
    cases hb : s[p] with
    | true =>
      rw [hb] at hsb
      have hstep : lvl s (p + 1) = lvl s p * (3 / 2) := by
        rw [lvl_succ s hsb]
        simp [factor]
      by_cases htp : t ≤ lvl s p
      · obtain ⟨i, hip, hodd, hmin, hle, hlt2⟩ := ih (by omega) t h1 htp
        refine ⟨i, by omega, hodd, ?_, hle, hlt2⟩
        intro j hij hj
        rcases (by omega : j ≤ p ∨ j = p + 1) with hjp | rfl
        · exact hmin j hij hjp
        · rw [hstep]
          linarith
      · refine ⟨p, by omega, hsb, ?_, by linarith, by linarith⟩
        intro j hij hj
        rcases (by omega : j = p ∨ j = p + 1) with rfl | rfl
        · exact le_rfl
        · rw [hstep]
          linarith
    | false =>
      rw [hb] at hsb
      have hstep : lvl s (p + 1) = lvl s p * (1 / 2) := by
        rw [lvl_succ s hsb]
        simp [factor]
      obtain ⟨i, hip, hodd, hmin, hle, hlt2⟩ := ih (by omega) t h1 (by linarith)
      refine ⟨i, by omega, hodd, ?_, hle, hlt2⟩
      intro j hij hj
      rcases (by omega : j ≤ p ∨ j = p + 1) with hjp | rfl
      · exact hmin j hij hjp
      · linarith

/-- A halving at p with level > 1 closes a bracket opened at an odd i < p. -/
theorem exists_lvlDrop_of_halving (s : List Bool) {p : ℕ} (hp : p < s.length)
    (hf : s[p]? = some false) (h1 : 1 < lvl s p) :
    ∃ i < p, s[i]? = some true ∧ LvlDrop s i (p + 1) := by
  obtain ⟨i, hip, hodd, hmin, _, hlt⟩ := lvl_gap s p hp.le (lvl s p) h1 le_rfl
  have hne : i ≠ p := by
    rintro rfl
    rw [hf] at hodd
    simp at hodd
  have hstep : lvl s (p + 1) = lvl s p * (1 / 2) := by
    rw [lvl_succ s hf]
    simp [factor]
  have hdrop : lvl s (p + 1) < lvl s i := by
    rw [hstep]
    linarith
  refine ⟨i, by omega, hodd, by omega, hdrop, ?_⟩
  intro k hk hik
  exact hmin k hik.le (by omega)

/-- Every halving at 1 ≤ p inside an admissible word closes a bracket at p + 1. -/
theorem closesAt_pos_of_halving {s : List Bool} (hA : Admissible s) {p : ℕ} (hp1 : 1 ≤ p)
    (hp : p < s.length) (hf : s[p]? = some false) : 0 < closesAt s (p + 1) := by
  obtain ⟨i, hip, hodd, hdrop⟩ := exists_lvlDrop_of_halving s hp hf (hA.prefix_gt p hp1 hp)
  exact Finset.card_pos.mpr
    ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hodd, hdrop⟩⟩

theorem getElem?_eq_of_take {s s' : List Bool} {p i : ℕ} (h : s.take p = s'.take p)
    (hi : i < p) : s[i]? = s'[i]? := by
  have := congrArg (fun l : List Bool => l[i]?) h
  simpa [List.getElem?_take, hi] using this

theorem lvl_eq_of_take {s s' : List Bool} {p j : ℕ} (h : s.take p = s'.take p)
    (hj : j ≤ p) : lvl s j = lvl s' j := by
  have := congrArg (List.take j) h
  simp only [List.take_take, min_eq_left hj] at this
  simp [lvl, this]

theorem closesAt_eq_of_take {s s' : List Bool} {p j : ℕ} (h : s.take p = s'.take p)
    (hj : j ≤ p) : closesAt s j = closesAt s' j := by
  have hl : ∀ q, q ≤ j → lvl s q = lvl s' q := fun q hq => lvl_eq_of_take h (by omega)
  unfold closesAt
  congr 1
  apply Finset.filter_congr
  intro i hi
  have hi' := Finset.mem_range.mp hi
  rw [getElem?_eq_of_take h (by omega)]
  unfold LvlDrop
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
theorem eq_single_of_admissible_false {s : List Bool} (hA : Admissible s)
    (h0 : s[0]? = some false) : s = [false] := by
  rcases s with _ | ⟨b, t⟩
  · simp at h0
  · simp only [List.getElem?_cons_zero, Option.some.injEq] at h0
    subst h0
    rcases t with _ | ⟨c, u⟩
    · rfl
    · exfalso
      have h := hA.prefix_gt 1 le_rfl (by simp)
      simp [seqProduct, factor] at h
      norm_num at h

theorem oddPos_split (s : List Bool) {p : ℕ} (hp : p ≤ s.length) :
    oddPos s = (List.range p).filter (fun i => s[i]? = some true) ++
      (List.range' p (s.length - p)).filter (fun i => s[i]? = some true) := by
  unfold oddPos
  rw [← List.filter_append, List.range_eq_range', List.range_eq_range']
  congr 1
  have := List.range'_append (s := 0) (m := p) (n := s.length - p) (step := 1)
  simp only [Nat.zero_add, one_mul] at this
  rw [this]
  congr 1
  omega

/-- Two admissible words that agree before p, with a halving at p in s and a
    tripling at p in s', have different bracket words. -/
theorem bracketWord_ne_of_split {s s' : List Bool} (hA : Admissible s) (hA' : Admissible s')
    {p : ℕ} (htake : s.take p = s'.take p) (hf : s[p]? = some false)
    (ht : s'[p]? = some true) : bracketWord s ≠ bracketWord s' := by
  intro hw
  have hpN : p < s.length := (List.getElem?_eq_some_iff.mp hf).1
  have hpN' : p < s'.length := (List.getElem?_eq_some_iff.mp ht).1
  rcases Nat.eq_zero_or_pos p with hp0 | hp1
  · subst hp0
    have hs := eq_single_of_admissible_false hA hf
    have h0 : 0 ∈ oddPos s' := List.mem_filter.mpr ⟨List.mem_range.mpr hpN', by simp [ht]⟩
    have hne : bracketWord s' ≠ [] := by
      simp only [bracketWord, ne_eq, List.map_eq_nil_iff]
      exact List.ne_nil_of_mem h0
    apply hne
    rw [← hw, hs]
    decide
  -- s' starts with a tripling, hence so does s
  have hs'0 : s'[0]? = some true := by
    rcases hb : s'[0]? with _ | b
    · rw [List.getElem?_eq_none_iff] at hb
      omega
    · cases b
      · have := eq_single_of_admissible_false hA' hb
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
  have hcol : colCount s k = colCount s' k := by
    have e1 := oddPos_split s hpN.le
    have e2 := oddPos_split s' hpN'.le
    rw [hA_eq] at e2
    set A := (List.range p).filter (fun i => s[i]? = some true)
    have hmap : A.map (colCount s) = A.map (colCount s') := by
      have := congrArg (List.take A.length) hw
      unfold bracketWord at this
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
  have hsum' : colCount s' k = ∑ j ∈ Finset.Ioc k p, closesAt s j := by
    unfold colCount
    rw [hn']
    apply Finset.sum_congr rfl
    intro j hj
    exact (closesAt_eq_of_take htake (Finset.mem_Ioc.mp hj).2).symm
  have hsum : ∑ j ∈ Finset.Ioc k p, closesAt s j + closesAt s (p + 1) ≤ colCount s k := by
    unfold colCount
    rw [← Finset.sum_Ioc_succ_top hkp.le]
    exact Finset.sum_le_sum_of_subset (Finset.Ioc_subset_Ioc_right hn)
  have hpos := closesAt_pos_of_halving hA hp1 hpN hf
  omega

/-- The bracket word determines an admissible word. -/
theorem bracketWord_injective {s s' : List Bool} (hA : Admissible s) (hA' : Admissible s')
    (hw : bracketWord s = bracketWord s') : s = s' := by
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
  -- a proper prefix of an admissible word is not admissible
  have hpre : ∀ {u v : List Bool}, Admissible u → Admissible v → u.length < v.length →
      v.take u.length ≠ u := by
    intro u v hu hv hlt heq
    have hu1 : 1 ≤ u.length := by
      rcases u with _ | _
      · exact absurd hu not_admissible_nil
      · simp
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
        · exact bracketWord_ne_of_split hA hA' htake hsp hsp' hw
      · cases b'
        · exact bracketWord_ne_of_split hA' hA htake.symm hsp' hsp hw.symm
        · exact hbb rfl

end AcceleratedCollatz
