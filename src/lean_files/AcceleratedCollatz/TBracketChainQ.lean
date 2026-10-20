-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TBracketChain
import AcceleratedCollatz.TBracketDyckQ
import AcceleratedCollatz.TChainEquivQ
import AcceleratedCollatz.TCutSweepQ
import AcceleratedCollatz.TRecordLowQ

/-!
  Bracket words of the q-family (q ≥ 3) along the chain decomposition. A word whose
  brackets all close inside it (`BracketsCloseQ`, e.g. an admissible word) contributes
  its own bracket word to any word it is a prefix of (`bracketWordQ_append`), so the
  blocks B1 .. Bm of 1 :: (B1 ++ ... ++ Bm) contribute their bracket words
  (`bracketWordQ_flatten`). The brackets of the leading 1 are added column by column:
  the bracket word of true :: r is the count of leading brackets closing in the first
  column, followed by the bracket word of r plus the leading brackets closing in each
  further column (`bracketWordQ_cons`). For admissible 1 :: (B1 ++ ... ++ Bm), bracket
  m of the leading 1 closes at the first cut whose level is below 2^m
  (`lvlDropQ_zero_iff_cut`); together: `bracketWordQ_chainWordQ`.
-/

namespace AcceleratedCollatz

variable {q : ℕ}

theorem lvlQ_append_right (u v : List Bool) (j : ℕ) :
    lvlQ q (u ++ v) (u.length + j) = seqProductQ q u * lvlQ q v j := by
  unfold lvlQ
  rw [List.take_length_add_append, seqProductQ_append]

/-- Closes of a bracket depend only on the levels up to the close. -/
theorem lvlDropQ_congr {s s' : List Bool} {i m j : ℕ}
    (h : ∀ r, r ≤ j → lvlQ q s r = lvlQ q s' r) (hd : LvlDropQ q s i m j) :
    LvlDropQ q s' i m j := by
  obtain ⟨hij, hlt, hmin⟩ := hd
  refine ⟨hij, ?_, fun k hk hik => ?_⟩
  · rw [← h j le_rfl, ← h i hij.le]
    exact hlt
  · rw [← h i hij.le, ← h k hk.le]
    exact hmin k hk hik

theorem lvlDropQ_append_left {u : List Bool} (v : List Bool) {i m j : ℕ} (hj : j ≤ u.length) :
    LvlDropQ q (u ++ v) i m j ↔ LvlDropQ q u i m j :=
  ⟨lvlDropQ_congr fun _ hr => lvlQ_append_left q (hr.trans hj),
    lvlDropQ_congr fun _ hr => (lvlQ_append_left q (hr.trans hj)).symm⟩

theorem lvlDropQ_append_right (hq0 : 0 < q) (u v : List Bool) (i m j : ℕ) :
    LvlDropQ q (u ++ v) (u.length + i) m (u.length + j) ↔ LvlDropQ q v i m j := by
  have hc := seqProductQ_pos hq0 u
  have hlt : ∀ a b : ℚ, seqProductQ q u * a < 2 ^ m * (seqProductQ q u * b) ↔
      a < 2 ^ m * b := by
    intro a b
    rw [show (2 : ℚ) ^ m * (seqProductQ q u * b) = seqProductQ q u * (2 ^ m * b) by ring]
    exact ⟨fun h => lt_of_mul_lt_mul_left h hc.le, fun h => mul_lt_mul_of_pos_left h hc⟩
  have hle : ∀ a b : ℚ, 2 ^ m * (seqProductQ q u * b) ≤ seqProductQ q u * a ↔
      2 ^ m * b ≤ a := by
    intro a b
    rw [show (2 : ℚ) ^ m * (seqProductQ q u * b) = seqProductQ q u * (2 ^ m * b) by ring]
    exact ⟨fun h => le_of_mul_le_mul_left h hc, fun h => mul_le_mul_of_nonneg_left h hc.le⟩
  constructor
  · rintro ⟨hij, hd, hmin⟩
    refine ⟨by omega, ?_, fun k hk hik => ?_⟩
    · rw [lvlQ_append_right, lvlQ_append_right] at hd
      exact (hlt _ _).mp hd
    · have h := hmin (u.length + k) (by omega) (by omega)
      rw [lvlQ_append_right, lvlQ_append_right] at h
      exact (hle _ _).mp h
  · rintro ⟨hij, hd, hmin⟩
    refine ⟨by omega, ?_, fun k hk hik => ?_⟩
    · rw [lvlQ_append_right, lvlQ_append_right]
      exact (hlt _ _).mpr hd
    · obtain ⟨k', rfl⟩ : ∃ k', k = u.length + k' := ⟨k - u.length, by omega⟩
      rw [lvlQ_append_right, lvlQ_append_right]
      exact (hle _ _).mpr (hmin k' (by omega) (by omega))

/-- A bracket opened inside s closes inside s. -/
theorem lvlDropQ_le_length {s : List Bool} {i m j : ℕ} (hi : i < s.length)
    (h : LvlDropQ q s i m j) : j ≤ s.length := by
  by_contra hlt
  push Not at hlt
  obtain ⟨_, hd, hmin⟩ := h
  have h1 := hmin s.length hlt hi
  have h2 : lvlQ q s j = lvlQ q s s.length := by
    unfold lvlQ
    rw [List.take_of_length_le hlt.le, List.take_length]
  linarith

/-- Brackets closing in the column of k: the close lies after k, with no odd
    position in between. -/
theorem mem_colSetQ_iff {s : List Bool} {x : ℕ × ℕ} {k : ℕ} (hk : k < s.length) :
    x ∈ colSetQ q s k ↔ x.2 < bracketsQ q ∧ s[x.1]? = some true ∧
      ∃ j, LvlDropQ q s x.1 x.2 j ∧ k < j ∧ ∀ r, k < r → r < j → s[r]? ≠ some true := by
  rw [mem_colSetQ]
  constructor
  · rintro ⟨j, ⟨hkj, hjn⟩, hm, hodd, hd⟩
    refine ⟨hm, hodd, j, hd, hkj, fun r hkr hrj hr => ?_⟩
    have := nextOdd_le_of_mem (mem_oddSet.mpr hr) hkr
    omega
  · rintro ⟨hm, hodd, j, hd, hkj, hno⟩
    have hjL := lvlDropQ_le_length (List.getElem?_eq_some_iff.mp hodd).1 hd
    refine ⟨j, ⟨hkj, ?_⟩, hm, hodd, hd⟩
    by_contra hlt
    push Not at hlt
    have hmem := nextOdd_mem (s := s) (k := k) (by omega)
    exact hno _ (lt_nextOdd hk) hlt (mem_oddSet.mp hmem)

/-- Every bracket of u closes inside u. -/
def BracketsCloseQ (q : ℕ) (u : List Bool) : Prop :=
  ∀ i m, u[i]? = some true → m < bracketsQ q → ∃ j, LvlDropQ q u i m j

theorem bracketsCloseQ_of_admissibleQ {u : List Bool} (hA : AdmissibleQ q u) :
    BracketsCloseQ q u := by
  intro i m hi _
  obtain ⟨j, hd, _⟩ := exists_lvlDropQ_of_mem hA (mem_oddSet.mpr hi) m
  exact ⟨j, hd⟩

/-- A bracket of a closed prefix u closes in u ++ v where it closes in u. -/
theorem lvlDropQ_of_bracketsCloseQ {u : List Bool} (v : List Bool) (hu : BracketsCloseQ q u)
    {i m j : ℕ} (hi : i < u.length) (hodd : (u ++ v)[i]? = some true) (hm : m < bracketsQ q)
    (hd : LvlDropQ q (u ++ v) i m j) : LvlDropQ q u i m j ∧ j ≤ u.length := by
  rw [List.getElem?_append_left hi] at hodd
  obtain ⟨j0, hd0⟩ := hu i m hodd hm
  have hj0 := lvlDropQ_le_length hi hd0
  have hjj := lvlDropQ_unique hd ((lvlDropQ_append_left v hj0).mpr hd0)
  subst hjj
  exact ⟨hd0, hj0⟩

theorem colSetQ_append_left {u : List Bool} (v : List Bool) (hu : BracketsCloseQ q u) {k : ℕ}
    (hk : k < u.length) : colSetQ q (u ++ v) k = colSetQ q u k := by
  have hk' : k < (u ++ v).length := by
    rw [List.length_append]
    omega
  ext x
  constructor
  · intro h
    have hik := le_of_mem_colSetQ h
    obtain ⟨hm, hi, j, hd, hkj, hno⟩ := (mem_colSetQ_iff hk').mp h
    obtain ⟨hd0, hj0⟩ := lvlDropQ_of_bracketsCloseQ v hu (by omega) hi hm hd
    rw [List.getElem?_append_left (by omega)] at hi
    refine (mem_colSetQ_iff hk).mpr ⟨hm, hi, j, hd0, hkj, fun r hkr hrj hr => ?_⟩
    apply hno r hkr hrj
    rw [List.getElem?_append_left (by omega)]
    exact hr
  · intro h
    have hik := le_of_mem_colSetQ h
    obtain ⟨hm, hi, j, hd, hkj, hno⟩ := (mem_colSetQ_iff hk).mp h
    have hjL := lvlDropQ_le_length (by omega) hd
    refine (mem_colSetQ_iff hk').mpr ⟨hm, ?_, j, (lvlDropQ_append_left v hjL).mpr hd, hkj,
      fun r hkr hrj hr => ?_⟩
    · rw [List.getElem?_append_left (by omega)]
      exact hi
    · rw [List.getElem?_append_left (by omega)] at hr
      exact hno r hkr hrj hr

/-- Shift of a bracket (i, m) by a positions. -/
def shiftQ (a : ℕ) : ℕ × ℕ ↪ ℕ × ℕ :=
  ⟨fun x => (a + x.1, x.2), fun x y h => by
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (by omega) h.2⟩

theorem colSetQ_append_right (hq0 : 0 < q) {u : List Bool} (v : List Bool)
    (hu : BracketsCloseQ q u) {k : ℕ} (hk : k < v.length) :
    colSetQ q (u ++ v) (u.length + k) = (colSetQ q v k).map (shiftQ u.length) := by
  have hk' : u.length + k < (u ++ v).length := by
    rw [List.length_append]
    omega
  ext x
  rw [Finset.mem_map]
  constructor
  · intro h
    obtain ⟨hm, hi, j, hd, hkj, hno⟩ := (mem_colSetQ_iff hk').mp h
    have hui : u.length ≤ x.1 := by
      by_contra hlt
      push Not at hlt
      have := (lvlDropQ_of_bracketsCloseQ v hu hlt hi hm hd).2
      omega
    obtain ⟨i', m⟩ := x
    have hui' : u.length ≤ i' := hui
    obtain ⟨i, rfl⟩ : ∃ i, i' = u.length + i := ⟨i' - u.length, by omega⟩
    obtain ⟨j', rfl⟩ : ∃ j', j = u.length + j' := ⟨j - u.length, by omega⟩
    refine ⟨(i, m), (mem_colSetQ_iff hk).mpr ⟨hm, ?_, j',
      (lvlDropQ_append_right hq0 u v i m j').mp hd, by omega, fun r hkr hrj hr => ?_⟩, rfl⟩
    · change (u ++ v)[u.length + i]? = some true at hi
      rw [getElem?_length_add_append] at hi
      exact hi
    · apply hno (u.length + r) (by omega) (by omega)
      rw [getElem?_length_add_append]
      exact hr
  · rintro ⟨⟨i, m⟩, h, rfl⟩
    obtain ⟨hm, hi, j', hd, hkj, hno⟩ := (mem_colSetQ_iff hk).mp h
    refine (mem_colSetQ_iff hk').mpr ⟨hm, ?_, u.length + j',
      (lvlDropQ_append_right hq0 u v i m j').mpr hd, by omega, fun r hkr hrj hr => ?_⟩
    · change (u ++ v)[u.length + i]? = some true
      rw [getElem?_length_add_append]
      exact hi
    · obtain ⟨r', rfl⟩ : ∃ r', r = u.length + r' := ⟨r - u.length, by omega⟩
      rw [getElem?_length_add_append] at hr
      exact hno r' (by omega) (by omega) hr

/-- A prefix whose brackets all close contributes its own bracket word. -/
theorem bracketWordQ_append (hq0 : 0 < q) {u : List Bool} (v : List Bool)
    (hu : BracketsCloseQ q u) :
    bracketWordQ q (u ++ v) = bracketWordQ q u ++ bracketWordQ q v := by
  unfold bracketWordQ
  rw [oddPos_append, List.map_append, List.map_map]
  congr 1
  · apply List.map_congr_left
    intro k hk
    have hkL := (List.getElem?_eq_some_iff.mp (mem_oddPos.mp hk)).1
    rw [colCountQ_eq, colCountQ_eq, colSetQ_append_left v hu hkL]
  · apply List.map_congr_left
    intro k hk
    have hkL := (List.getElem?_eq_some_iff.mp (mem_oddPos.mp hk)).1
    rw [Function.comp_apply, colCountQ_eq, colCountQ_eq, colSetQ_append_right hq0 v hu hkL,
      Finset.card_map]

/-- Admissible blocks contribute their bracket words. -/
theorem bracketWordQ_flatten (hq0 : 0 < q) (bs : List (List Bool))
    (h : ∀ b ∈ bs, AdmissibleQ q b) :
    bracketWordQ q bs.flatten = (bs.map (bracketWordQ q)).flatten := by
  induction bs with
  | nil =>
    simp [bracketWordQ, oddPos]
  | cons b bs ih =>
    rw [List.flatten_cons, bracketWordQ_append hq0 _
      (bracketsCloseQ_of_admissibleQ (h b List.mem_cons_self)),
      ih (fun c hc => h c (List.mem_cons_of_mem b hc)), List.map_cons, List.flatten_cons]

/-! ### The leading odd step -/

/-- Number of brackets of the leading position closing in the column of c. -/
def leadCountQ (q : ℕ) (s : List Bool) (c : ℕ) : ℕ :=
  ((colSetQ q s c).filter (fun x => x.1 = 0)).card

theorem oddPos_true_cons (r : List Bool) :
    oddPos (true :: r) = 0 :: (oddPos r).map (1 + ·) := by
  have h := oddPos_append [true] r
  have h1 : oddPos [true] = [0] := by
    decide
  rw [h1] at h
  exact h

/-- The next odd position after 1 + k in b :: r. -/
theorem nextOdd_cons (b : Bool) {r : List Bool} {k : ℕ} (hk : k < r.length) :
    nextOdd (b :: r) (1 + k) = 1 + nextOdd r k := by
  have hk' : 1 + k < (b :: r).length := by
    rw [List.length_cons]
    omega
  have hshift : ∀ i, (b :: r)[1 + i]? = r[i]? := getElem?_cons_one_add b r
  rcases (nextOdd_le r k).lt_or_eq with hlt | heq
  · have hmem := nextOdd_mem hlt
    have hmem' : 1 + nextOdd r k ∈ oddSet (b :: r) := by
      rw [mem_oddSet, hshift]
      exact mem_oddSet.mp hmem
    have hkn := lt_nextOdd (s := r) hk
    have hle1 := nextOdd_le_of_mem hmem' (by omega : 1 + k < 1 + nextOdd r k)
    apply le_antisymm hle1
    rcases (nextOdd_le (b :: r) (1 + k)).lt_or_eq with hlt' | heq'
    · have hN := nextOdd_mem hlt'
      have hgt := lt_nextOdd hk'
      obtain ⟨N, hN'⟩ : ∃ N, nextOdd (b :: r) (1 + k) = 1 + N :=
        ⟨nextOdd (b :: r) (1 + k) - 1, by omega⟩
      rw [hN', mem_oddSet, hshift] at hN
      have := nextOdd_le_of_mem (mem_oddSet.mpr hN) (by omega : k < N)
      omega
    · rw [heq', List.length_cons]
      have := nextOdd_le r k
      omega
  · have hnone := (nextOdd_eq_length_iff hk).mp heq
    have hnone' : ∀ r', 1 + k < r' → (b :: r)[r']? ≠ some true := by
      intro r' hr' h
      obtain ⟨i, rfl⟩ : ∃ i, r' = 1 + i := ⟨r' - 1, by omega⟩
      rw [hshift] at h
      exact hnone i (by omega) h
    rw [(nextOdd_eq_length_iff hk').mpr hnone', heq, List.length_cons]
    omega

/-- Column of 1 + k in true :: r: the closes of r in the column of k, shifted by one,
    and the brackets of the leading 1 that close there. -/
theorem colCountQ_true_cons (hq0 : 0 < q) {r : List Bool} {k : ℕ} (hk : k < r.length) :
    colCountQ q (true :: r) (1 + k) = colCountQ q r k + leadCountQ q (true :: r) (1 + k) := by
  rw [colCountQ_eq, colCountQ_eq, leadCountQ,
    ← Finset.card_filter_add_card_filter_not (s := colSetQ q (true :: r) (1 + k))
      (fun x : ℕ × ℕ => x.1 = 0), Nat.add_comm]
  congr 1
  rw [← Finset.card_map (s := colSetQ q r k) (shiftQ 1)]
  congr 1
  ext x
  rw [Finset.mem_filter, Finset.mem_map]
  have hk' : 1 + k < (true :: r).length := by
    rw [List.length_cons]
    omega
  constructor
  · rintro ⟨h, hx0⟩
    obtain ⟨hm, hi, j, hd, hkj, hno⟩ := (mem_colSetQ_iff hk').mp h
    obtain ⟨i', m⟩ := x
    simp only at hx0 hm hi hd
    obtain ⟨i, rfl⟩ : ∃ i, i' = 1 + i := ⟨i' - 1, by omega⟩
    obtain ⟨j', rfl⟩ : ∃ j', j = 1 + j' := ⟨j - 1, by omega⟩
    refine ⟨(i, m), (mem_colSetQ_iff hk).mpr ⟨hm, ?_, j',
      (lvlDropQ_append_right hq0 [true] r i m j').mp hd, by omega, fun r' hkr hrj hr => ?_⟩,
      rfl⟩
    · rw [getElem?_cons_one_add] at hi
      exact hi
    · apply hno (1 + r') (by omega) (by omega)
      rw [getElem?_cons_one_add]
      exact hr
  · rintro ⟨⟨i, m⟩, h, rfl⟩
    obtain ⟨hm, hi, j', hd, hkj, hno⟩ := (mem_colSetQ_iff hk).mp h
    refine ⟨(mem_colSetQ_iff hk').mpr ⟨hm, ?_, 1 + j',
      (lvlDropQ_append_right hq0 [true] r i m j').mpr hd, by omega,
      fun r' hkr hrj hr => ?_⟩, ?_⟩
    · change (true :: r)[1 + i]? = some true
      rw [getElem?_cons_one_add]
      exact hi
    · obtain ⟨r'', rfl⟩ : ∃ r'', r' = 1 + r'' := ⟨r' - 1, by omega⟩
      rw [getElem?_cons_one_add] at hr
      exact hno r'' (by omega) (by omega) hr
    · change ¬(1 + i = 0)
      omega

/-- Column of the leading 1: only brackets of the leading 1 close there. -/
theorem colCountQ_true_cons_zero (r : List Bool) :
    colCountQ q (true :: r) 0 = leadCountQ q (true :: r) 0 := by
  rw [colCountQ_eq, leadCountQ, Finset.filter_true_of_mem]
  intro x hx
  have := le_of_mem_colSetQ hx
  omega

theorem map_add_eq_zipWith (l : List ℕ) (f g : ℕ → ℕ) :
    l.map (fun k => f k + g k) = List.zipWith (· + ·) (l.map f) (l.map g) := by
  induction l with
  | nil =>
    rfl
  | cons a t ih =>
    simp only [List.map_cons, List.zipWith_cons_cons, ih]

/-- The bracket word of true :: r: the leading brackets closing in the first column,
    then the bracket word of r plus the leading brackets closing in each further
    column. -/
theorem bracketWordQ_cons (hq0 : 0 < q) (r : List Bool) :
    bracketWordQ q (true :: r) = leadCountQ q (true :: r) 0 ::
      List.zipWith (· + ·) (bracketWordQ q r)
        ((oddPos r).map (fun k => leadCountQ q (true :: r) (1 + k))) := by
  unfold bracketWordQ
  rw [oddPos_true_cons, List.map_cons, colCountQ_true_cons_zero, List.map_map,
    ← map_add_eq_zipWith]
  congr 1
  apply List.map_congr_left
  intro k hk
  have hkL := (List.getElem?_eq_some_iff.mp (mem_oddPos.mp hk)).1
  exact colCountQ_true_cons hq0 hkL

/-! ### Where the brackets of the leading 1 close -/

/-- Cuts of 1 :: (B1 ++ ... ++ Bm) increase with the number of blocks before them. -/
theorem length_take_flatten_lt {bs : List (List Bool)} (h : ∀ b ∈ bs, b ≠ [])
    {i i' : ℕ} (hii : i' < i) (hi : i ≤ bs.length) :
    (bs.take i').flatten.length < (bs.take i).flatten.length := by
  have hsplit : bs.take i = bs.take i' ++ (bs.take i).drop i' := by
    conv_lhs => rw [← List.take_append_drop i' (bs.take i)]
    rw [List.take_take, min_eq_left hii.le]
  rw [hsplit, List.flatten_append, List.length_append]
  have hne : (bs.take i).drop i' ≠ [] := by
    rw [ne_eq, List.drop_eq_nil_iff, List.length_take]
    omega
  obtain ⟨c, hc⟩ : ∃ c, c ∈ (bs.take i).drop i' := ⟨_, List.head_mem hne⟩
  have hcne := h c (List.mem_of_mem_take (List.mem_of_mem_drop hc))
  have hpos : 0 < ((bs.take i).drop i').flatten.length := by
    rw [List.length_flatten]
    have hcl := List.length_pos_iff.mpr hcne
    have := List.le_sum_of_mem (List.mem_map_of_mem (f := List.length) hc)
    omega
  omega

/-- Bracket m of the leading 1 of an admissible 1 :: (B1 ++ ... ++ Bm) closes at the
    end of the blocks B1 .. Bi, i the least number whose level there is below 2^m. -/
theorem lvlDropQ_zero_cut (hq : 3 ≤ q) {bs : List (List Bool)}
    (hbs : ∀ b ∈ bs, AdmissibleQ q b) {m j : ℕ} (hd : LvlDropQ q (true :: bs.flatten) 0 m j) :
    ∃ i, i ≤ bs.length ∧ j = 1 + (bs.take i).flatten.length ∧
      lvlQ q (true :: bs.flatten) j < 2 ^ m ∧
        ∀ i', i' < i → 2 ^ m ≤ lvlQ q (true :: bs.flatten) (1 + (bs.take i').flatten.length) := by
  obtain ⟨h0j, hlt, hmin⟩ := hd
  rw [lvlQ_zero, mul_one] at hlt hmin
  have hjL := lvlDropQ_le_length (s := true :: bs.flatten) (by simp) ⟨h0j, by
    rw [lvlQ_zero, mul_one]
    exact hlt, fun k hk hk0 => by
      rw [lvlQ_zero, mul_one]
      exact hmin k hk hk0⟩
  have hrec : IsRecordLowQ q (true :: bs.flatten) j := by
    refine ⟨h0j, hjL, fun k hk1 hkj => ?_⟩
    have h1 := hmin k hkj (by omega)
    unfold lvlQ at hlt h1
    linarith
  obtain ⟨i, hi, rfl⟩ := (isRecordLowQ_iff_cut (by omega) bs hbs j).mp hrec
  refine ⟨i, hi, rfl, hlt, fun i' hii => ?_⟩
  have hne : ∀ b ∈ bs, b ≠ [] := fun b hb => ne_nil_of_admissibleQ (hbs b hb)
  have := length_take_flatten_lt hne hii hi
  exact hmin _ (by omega) (by omega)

/-- The close of bracket m of the leading 1 is the first cut whose level is below 2^m. -/
theorem lvlDropQ_zero_iff_cut (hq : 3 ≤ q) {bs : List (List Bool)}
    (hbs : ∀ b ∈ bs, AdmissibleQ q b) (hA : AdmissibleQ q (true :: bs.flatten)) {m j : ℕ} :
    LvlDropQ q (true :: bs.flatten) 0 m j ↔
      ∃ i, i ≤ bs.length ∧ j = 1 + (bs.take i).flatten.length ∧
        lvlQ q (true :: bs.flatten) j < 2 ^ m ∧
          ∀ i', i' < i →
            2 ^ m ≤ lvlQ q (true :: bs.flatten) (1 + (bs.take i').flatten.length) := by
  constructor
  · exact lvlDropQ_zero_cut hq hbs
  · rintro ⟨i, hi, rfl, hlt, hmin⟩
    have h0 : (0 : ℕ) ∈ oddSet (true :: bs.flatten) := by
      rw [mem_oddSet]
      rfl
    obtain ⟨J, hJ, _⟩ := exists_lvlDropQ_of_mem hA h0 m
    obtain ⟨i2, hi2, rfl, hlt2, hmin2⟩ := lvlDropQ_zero_cut hq hbs hJ
    have heq : i = i2 := by
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with h | h
      · have := hmin2 i h
        linarith
      · have := hmin i2 h
        linarith
    subst heq
    exact hJ

/-- Chain form of the bracket word: for admissible blocks B1 .. Bm with 1 :: (B1 ++ ... ++ Bm)
    admissible, its bracket word is the count of leading brackets closing in the first
    column, followed by the bracket words of the blocks plus, column by column, the
    brackets of the leading 1 that close there (each at its cut, `lvlDropQ_zero_iff_cut`). -/
theorem bracketWordQ_chainWordQ (hq : 3 ≤ q) {bs : List (List Bool)}
    (hbs : ∀ b ∈ bs, AdmissibleQ q b) :
    bracketWordQ q (chainWordQ bs) = leadCountQ q (chainWordQ bs) 0 ::
      List.zipWith (· + ·) (bs.map (bracketWordQ q)).flatten
        ((oddPos bs.flatten).map (fun k => leadCountQ q (chainWordQ bs) (1 + k))) := by
  unfold chainWordQ
  rw [bracketWordQ_cons (by omega), bracketWordQ_flatten (by omega) bs hbs]

-- q = 5: the leading 1 of 1 | 100 | 0 (11000) has two brackets, closing at the cuts 4 and 5,
-- both in the column of the second 1.
set_option linter.hashCommand false in
#guard bracketWordQ 5 [true, true, false, false, false] =
  0 :: List.zipWith (· + ·) (bracketWordQ 5 [true, false, false] ++ bracketWordQ 5 [false])
    ((oddPos [true, false, false, false]).map
      (fun k => leadCountQ 5 [true, true, false, false, false] (1 + k)))

end AcceleratedCollatz
