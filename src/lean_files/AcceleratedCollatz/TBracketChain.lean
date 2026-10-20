-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TBracketDyck
import AcceleratedCollatz.TChainEquiv

/-!
  Bracket words along the chain decomposition. A word whose brackets all close
  inside it (`BracketsClose`, e.g. an admissible word) contributes its own bracket
  word to any word it is a prefix of (`bracketWord_append`). In an admissible word
  true :: r the bracket of the leading 1 closes at the end, in the last column
  (`bracketWord_cons`). Hence the bracket word of 1 :: (A1 ++ ... ++ Ak ++ t) is
  0 :: (the bracket words of the blocks), with 1 added to the last entry
  (`bracketWord_chain`).
-/

namespace AcceleratedCollatz

/-- Add p to the last entry. -/
def addLast (p : ℕ) : List ℕ → List ℕ
  | [] => []
  | [a] => [a + p]
  | a :: b :: l => a :: addLast p (b :: l)

theorem addLast_concat (p : ℕ) (l : List ℕ) (a : ℕ) : addLast p (l ++ [a]) = l ++ [a + p] := by
  induction l with
  | nil => rfl
  | cons b t ih =>
    cases t with
    | nil => rfl
    | cons c t' =>
      change b :: addLast p (c :: t' ++ [a]) = _
      rw [ih]
      rfl

theorem addLast_cons (p a : ℕ) {l : List ℕ} (hl : l ≠ []) :
    addLast p (a :: l) = a :: addLast p l := by
  cases l with
  | nil => exact absurd rfl hl
  | cons b t => rfl

theorem lvl_append_left (u v : List Bool) {j : ℕ} (hj : j ≤ u.length) :
    lvl (u ++ v) j = lvl u j := by
  unfold lvl
  rw [List.take_append_of_le_length hj]

theorem lvl_append_right (u v : List Bool) (j : ℕ) :
    lvl (u ++ v) (u.length + j) = seqProduct u * lvl v j := by
  unfold lvl
  rw [List.take_length_add_append, seqProduct_append]

/-- Level drops depend only on the levels up to the drop. -/
theorem lvlDrop_congr {s s' : List Bool} {i j : ℕ} (h : ∀ q, q ≤ j → lvl s q = lvl s' q)
    (hd : LvlDrop s i j) : LvlDrop s' i j := by
  obtain ⟨hij, hlt, hmin⟩ := hd
  refine ⟨hij, ?_, fun k hk hik => ?_⟩
  · rw [← h j le_rfl, ← h i hij.le]
    exact hlt
  · rw [← h i hij.le, ← h k hk.le]
    exact hmin k hk hik

theorem lvlDrop_append_left {u : List Bool} (v : List Bool) {i j : ℕ} (hj : j ≤ u.length) :
    LvlDrop (u ++ v) i j ↔ LvlDrop u i j :=
  ⟨lvlDrop_congr fun _ hq => lvl_append_left u v (hq.trans hj),
    lvlDrop_congr fun _ hq => (lvl_append_left u v (hq.trans hj)).symm⟩

theorem lvlDrop_append_right (u v : List Bool) (i j : ℕ) :
    LvlDrop (u ++ v) (u.length + i) (u.length + j) ↔ LvlDrop v i j := by
  have hc := seqProduct_pos u
  constructor
  · rintro ⟨hij, hlt, hmin⟩
    refine ⟨by omega, ?_, fun k hk hik => ?_⟩
    · rw [lvl_append_right, lvl_append_right] at hlt
      exact lt_of_mul_lt_mul_left hlt hc.le
    · have h := hmin (u.length + k) (by omega) (by omega)
      rw [lvl_append_right, lvl_append_right] at h
      exact le_of_mul_le_mul_left h hc
  · rintro ⟨hij, hlt, hmin⟩
    refine ⟨by omega, ?_, fun k hk hik => ?_⟩
    · rw [lvl_append_right, lvl_append_right]
      exact mul_lt_mul_of_pos_left hlt hc
    · obtain ⟨k', rfl⟩ : ∃ k', k = u.length + k' := ⟨k - u.length, by omega⟩
      rw [lvl_append_right, lvl_append_right]
      exact mul_le_mul_of_nonneg_left (hmin k' (by omega) (by omega)) hc.le

/-- A bracket opened inside s closes inside s. -/
theorem lvlDrop_le_length {s : List Bool} {i j : ℕ} (hi : i < s.length) (h : LvlDrop s i j) :
    j ≤ s.length := by
  by_contra hlt
  push Not at hlt
  obtain ⟨_, hd, hmin⟩ := h
  have h1 := hmin s.length hlt hi
  have h2 : lvl s j = lvl s s.length := by
    unfold lvl
    rw [List.take_of_length_le hlt.le, List.take_length]
  linarith

theorem mem_oddPos {s : List Bool} {i : ℕ} : i ∈ oddPos s ↔ s[i]? = some true := by
  unfold oddPos
  rw [List.mem_filter, List.mem_range, decide_eq_true_eq]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨(List.getElem?_eq_some_iff.mp h).1, h⟩

theorem getElem?_length_add_append (u v : List Bool) (i : ℕ) :
    (u ++ v)[u.length + i]? = v[i]? := by
  rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]

theorem oddPos_append (u v : List Bool) :
    oddPos (u ++ v) = oddPos u ++ (oddPos v).map (u.length + ·) := by
  unfold oddPos
  rw [List.length_append, List.range_add, List.filter_append, List.filter_map]
  congr 1
  · apply List.filter_congr
    intro i hi
    rw [List.getElem?_append_left (List.mem_range.mp hi)]
  · congr 1
    apply List.filter_congr
    intro i _
    rw [Function.comp_apply, getElem?_length_add_append]

/-- The next odd position after k is the end iff no odd position follows k. -/
theorem nextOdd_eq_length_iff {s : List Bool} {k : ℕ} (hk : k < s.length) :
    nextOdd s k = s.length ↔ ∀ m, k < m → s[m]? ≠ some true := by
  constructor
  · intro h m hkm hm
    have hle := nextOdd_le_of_mem (mem_oddSet.mpr hm) hkm
    have hmL := (List.getElem?_eq_some_iff.mp hm).1
    omega
  · intro h
    by_contra hne
    have hlt : nextOdd s k < s.length := lt_of_le_of_ne (nextOdd_le s k) hne
    exact h _ (lt_nextOdd hk) (mem_oddSet.mp (nextOdd_mem hlt))

/-- Brackets closing in the column of k: the close lies after k, with no odd
    position in between. -/
theorem mem_colSet_iff {s : List Bool} {i k : ℕ} (hk : k < s.length) :
    i ∈ colSet s k ↔ s[i]? = some true ∧ ∃ j, LvlDrop s i j ∧ k < j ∧
      ∀ m, k < m → m < j → s[m]? ≠ some true := by
  rw [mem_colSet]
  constructor
  · rintro ⟨j, ⟨hkj, hjn⟩, hodd, hd⟩
    refine ⟨hodd, j, hd, hkj, fun m hkm hmj hm => ?_⟩
    have := nextOdd_le_of_mem (mem_oddSet.mpr hm) hkm
    omega
  · rintro ⟨hodd, j, hd, hkj, hno⟩
    have hjL := lvlDrop_le_length (List.getElem?_eq_some_iff.mp hodd).1 hd
    refine ⟨j, ⟨hkj, ?_⟩, hodd, hd⟩
    by_contra hlt
    push Not at hlt
    have hmem := nextOdd_mem (s := s) (k := k) (by omega)
    exact hno _ (lt_nextOdd hk) hlt (mem_oddSet.mp hmem)

/-- Every bracket of u closes. -/
def BracketsClose (u : List Bool) : Prop :=
  ∀ i, u[i]? = some true → ∃ j, LvlDrop u i j

theorem bracketsClose_of_admissible {u : List Bool} (hA : Admissible u) : BracketsClose u := by
  intro i hi
  obtain ⟨j, hd, _⟩ := exists_lvlDrop_of_mem hA (mem_oddSet.mpr hi)
  exact ⟨j, hd⟩

/-- A bracket of a closed prefix u closes in u ++ v where it closes in u. -/
theorem lvlDrop_of_bracketsClose {u : List Bool} (v : List Bool) (hu : BracketsClose u)
    {i j : ℕ} (hi : i < u.length) (hodd : (u ++ v)[i]? = some true)
    (hd : LvlDrop (u ++ v) i j) : LvlDrop u i j ∧ j ≤ u.length := by
  rw [List.getElem?_append_left hi] at hodd
  obtain ⟨j0, hd0⟩ := hu i hodd
  have hj0 := lvlDrop_le_length hi hd0
  have hjj := lvlDrop_unique hd ((lvlDrop_append_left v hj0).mpr hd0)
  subst hjj
  exact ⟨hd0, hj0⟩

theorem colSet_append_left {u : List Bool} (v : List Bool) (hu : BracketsClose u) {k : ℕ}
    (hk : k < u.length) : colSet (u ++ v) k = colSet u k := by
  have hk' : k < (u ++ v).length := by
    rw [List.length_append]
    omega
  ext i
  constructor
  · intro h
    have hik := le_of_mem_colSet h
    obtain ⟨hi, j, hd, hkj, hno⟩ := (mem_colSet_iff hk').mp h
    obtain ⟨hd0, hj0⟩ := lvlDrop_of_bracketsClose v hu (by omega) hi hd
    rw [List.getElem?_append_left (by omega)] at hi
    refine (mem_colSet_iff hk).mpr ⟨hi, j, hd0, hkj, fun m hkm hmj hm => ?_⟩
    apply hno m hkm hmj
    rw [List.getElem?_append_left (by omega)]
    exact hm
  · intro h
    have hik := le_of_mem_colSet h
    obtain ⟨hi, j, hd, hkj, hno⟩ := (mem_colSet_iff hk).mp h
    have hjL := lvlDrop_le_length (by omega) hd
    refine (mem_colSet_iff hk').mpr ⟨?_, j, (lvlDrop_append_left v hjL).mpr hd, hkj,
      fun m hkm hmj hm => ?_⟩
    · rw [List.getElem?_append_left (by omega)]
      exact hi
    · rw [List.getElem?_append_left (by omega)] at hm
      exact hno m hkm hmj hm

theorem colSet_append_right {u : List Bool} (v : List Bool) (hu : BracketsClose u) {k : ℕ}
    (hk : k < v.length) :
    colSet (u ++ v) (u.length + k) = (colSet v k).map (addLeftEmbedding u.length) := by
  have hk' : u.length + k < (u ++ v).length := by
    rw [List.length_append]
    omega
  ext i
  rw [Finset.mem_map]
  constructor
  · intro h
    have hik := le_of_mem_colSet h
    obtain ⟨hi, j, hd, hkj, hno⟩ := (mem_colSet_iff hk').mp h
    have hui : u.length ≤ i := by
      by_contra hlt
      push Not at hlt
      have := (lvlDrop_of_bracketsClose v hu hlt hi hd).2
      omega
    obtain ⟨i', rfl⟩ : ∃ i', i = u.length + i' := ⟨i - u.length, by omega⟩
    obtain ⟨j', rfl⟩ : ∃ j', j = u.length + j' := ⟨j - u.length, by omega⟩
    refine ⟨i', (mem_colSet_iff hk).mpr ⟨?_, j', (lvlDrop_append_right u v i' j').mp hd,
      by omega, fun m hkm hmj hm => ?_⟩, rfl⟩
    · rw [getElem?_length_add_append] at hi
      exact hi
    · apply hno (u.length + m) (by omega) (by omega)
      rw [getElem?_length_add_append]
      exact hm
  · rintro ⟨i', h, rfl⟩
    obtain ⟨hi, j', hd, hkj, hno⟩ := (mem_colSet_iff hk).mp h
    refine (mem_colSet_iff hk').mpr ⟨?_, u.length + j',
      (lvlDrop_append_right u v i' j').mpr hd, by omega, fun m hkm hmj hm => ?_⟩
    · change (u ++ v)[u.length + i']? = some true
      rw [getElem?_length_add_append]
      exact hi
    · obtain ⟨m', rfl⟩ : ∃ m', m = u.length + m' := ⟨m - u.length, by omega⟩
      rw [getElem?_length_add_append] at hm
      exact hno m' (by omega) (by omega) hm

/-- A prefix whose brackets all close contributes its own bracket word. -/
theorem bracketWord_append {u : List Bool} (v : List Bool) (hu : BracketsClose u) :
    bracketWord (u ++ v) = bracketWord u ++ bracketWord v := by
  unfold bracketWord
  rw [oddPos_append, List.map_append, List.map_map]
  congr 1
  · apply List.map_congr_left
    intro k hk
    have hkL := (List.getElem?_eq_some_iff.mp (mem_oddPos.mp hk)).1
    rw [colCount_eq, colCount_eq, colSet_append_left v hu hkL]
  · apply List.map_congr_left
    intro k hk
    have hkL := (List.getElem?_eq_some_iff.mp (mem_oddPos.mp hk)).1
    rw [Function.comp_apply, colCount_eq, colCount_eq, colSet_append_right v hu hkL,
      Finset.card_map]

theorem bracketWord_flatten_append (bs : List (List Bool)) (t : List Bool)
    (h : ∀ b ∈ bs, BracketsClose b) :
    bracketWord (bs.flatten ++ t) = (bs.map bracketWord).flatten ++ bracketWord t := by
  induction bs with
  | nil => simp
  | cons b bs ih =>
    rw [List.flatten_cons, List.append_assoc, bracketWord_append _ (h b List.mem_cons_self),
      ih (fun c hc => h c (List.mem_cons_of_mem b hc)), List.map_cons, List.flatten_cons,
      List.append_assoc]

/-- The bracket of the leading position of an admissible word closes at the end. -/
theorem lvlDrop_zero_iff {s : List Bool} (hA : Admissible s) {j : ℕ} :
    LvlDrop s 0 j ↔ j = s.length := by
  have hne : s ≠ [] := fun h => not_admissible_nil (h ▸ hA)
  have hend : LvlDrop s 0 s.length := by
    refine ⟨List.length_pos_iff.mpr hne, ?_, fun k hk hk0 => ?_⟩
    · rw [lvl_zero]
      unfold lvl
      rw [List.take_length]
      exact hA.lt_one
    · rw [lvl_zero]
      exact (hA.prefix_gt k hk0 hk).le
  constructor
  · intro h
    exact lvlDrop_unique h hend
  · rintro rfl
    exact hend

theorem lvlDrop_cons (b : Bool) (r : List Bool) (i j : ℕ) :
    LvlDrop (b :: r) (1 + i) (1 + j) ↔ LvlDrop r i j :=
  lvlDrop_append_right [b] r i j

theorem getElem?_cons_one_add (b : Bool) (r : List Bool) (i : ℕ) :
    (b :: r)[1 + i]? = r[i]? := by
  rw [Nat.add_comm, List.getElem?_cons_succ]

/-- Column of the leading 1 of an admissible word true :: true :: _: no closes. -/
theorem colSet_cons_zero {r : List Bool} (hA : Admissible (true :: r))
    (hr : r[0]? = some true) : colSet (true :: r) 0 = ∅ := by
  ext i
  simp only [Finset.notMem_empty, iff_false]
  intro h
  have hik := le_of_mem_colSet h
  obtain ⟨_, j, hd, hkj, hno⟩ := (mem_colSet_iff (by simp)).mp h
  obtain rfl : i = 0 := by omega
  have hj := (lvlDrop_zero_iff hA).mp hd
  have hrL := (List.getElem?_eq_some_iff.mp hr).1
  rw [List.length_cons] at hj
  apply hno 1 (by omega) (by omega)
  rw [List.getElem?_cons_succ]
  exact hr

/-- Column of an odd position 1 + k of an admissible word true :: r: the closes of
    r in the column of k, and the bracket of the leading 1 in the last column. -/
theorem colSet_cons_succ {r : List Bool} (hA : Admissible (true :: r)) {k : ℕ}
    (hk : k < r.length) :
    colSet (true :: r) (1 + k) = (colSet r k).map (addLeftEmbedding 1) ∪
      (if nextOdd r k = r.length then {0} else ∅) := by
  have hk' : 1 + k < (true :: r).length := by
    rw [List.length_cons]
    omega
  ext i
  rw [Finset.mem_union, Finset.mem_map]
  constructor
  · intro h
    obtain ⟨hi, j, hd, hkj, hno⟩ := (mem_colSet_iff hk').mp h
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · right
      have hj := (lvlDrop_zero_iff hA).mp hd
      rw [List.length_cons] at hj
      have hc : nextOdd r k = r.length := by
        apply (nextOdd_eq_length_iff hk).mpr
        intro m hkm hm
        have hmL := (List.getElem?_eq_some_iff.mp hm).1
        apply hno (1 + m) (by omega) (by omega)
        rw [getElem?_cons_one_add]
        exact hm
      simp only [hc, ↓reduceIte]
      exact Finset.mem_singleton_self 0
    · left
      obtain ⟨i', rfl⟩ : ∃ i', i = 1 + i' := ⟨i - 1, by omega⟩
      obtain ⟨j', rfl⟩ : ∃ j', j = 1 + j' := ⟨j - 1, by omega⟩
      rw [getElem?_cons_one_add] at hi
      refine ⟨i', (mem_colSet_iff hk).mpr ⟨hi, j', (lvlDrop_cons true r i' j').mp hd,
        by omega, fun m hkm hmj hm => ?_⟩, rfl⟩
      apply hno (1 + m) (by omega) (by omega)
      rw [getElem?_cons_one_add]
      exact hm
  · rintro (⟨i', h, rfl⟩ | h0)
    · obtain ⟨hi, j', hd, hkj, hno⟩ := (mem_colSet_iff hk).mp h
      refine (mem_colSet_iff hk').mpr ⟨?_, 1 + j', (lvlDrop_cons true r i' j').mpr hd,
        by omega, fun m hkm hmj hm => ?_⟩
      · change (true :: r)[1 + i']? = some true
        rw [getElem?_cons_one_add]
        exact hi
      · obtain ⟨m', rfl⟩ : ∃ m', m = 1 + m' := ⟨m - 1, by omega⟩
        rw [getElem?_cons_one_add] at hm
        exact hno m' (by omega) (by omega) hm
    · split_ifs at h0 with hc
      · rw [Finset.mem_singleton] at h0
        subst h0
        refine (mem_colSet_iff hk').mpr ⟨rfl, (true :: r).length,
          (lvlDrop_zero_iff hA).mpr rfl, hk', fun m hkm hmj hm => ?_⟩
        rw [List.length_cons] at hmj
        obtain ⟨m', rfl⟩ : ∃ m', m = 1 + m' := ⟨m - 1, by omega⟩
        rw [getElem?_cons_one_add] at hm
        exact (nextOdd_eq_length_iff hk).mp hc m' (by omega) hm
      · exact absurd h0 (Finset.notMem_empty i)

theorem colCount_cons_succ {r : List Bool} (hA : Admissible (true :: r)) {k : ℕ}
    (hk : k < r.length) :
    colCount (true :: r) (1 + k) =
      colCount r k + (if nextOdd r k = r.length then 1 else 0) := by
  rw [colCount_eq, colCount_eq, colSet_cons_succ hA hk, Finset.card_union_of_disjoint,
    Finset.card_map]
  · split_ifs
    · rfl
    · rfl
  · rw [Finset.disjoint_left]
    intro i hi h0
    obtain ⟨i', _, rfl⟩ := Finset.mem_map.mp hi
    split_ifs at h0
    · rw [Finset.mem_singleton] at h0
      change 1 + i' = 0 at h0
      omega
    · exact absurd h0 (Finset.notMem_empty _)

/-- Adding 1 at the last odd position adds 1 to the last entry. -/
theorem map_colCount_last (r : List Bool) (hne : oddPos r ≠ []) :
    (oddPos r).map (fun k => colCount r k + (if nextOdd r k = r.length then 1 else 0)) =
      addLast 1 (bracketWord r) := by
  rcases List.eq_nil_or_concat (oddPos r) with h0 | ⟨init, z, hl⟩
  · exact absurd h0 hne
  rw [List.concat_eq_append] at hl
  have hpw : (oddPos r).Pairwise (· < ·) := List.Pairwise.filter _ List.pairwise_lt_range
  have hmem : ∀ k, k ∈ oddPos r ↔ k ∈ init ∨ k = z := by
    intro k
    rw [hl, List.mem_append, List.mem_singleton]
  have hz := mem_oddPos.mp ((hmem z).mpr (Or.inr rfl))
  have hzL := (List.getElem?_eq_some_iff.mp hz).1
  rw [hl, List.pairwise_append] at hpw
  have hlt : ∀ k ∈ init, k < z := fun k hk => hpw.2.2 k hk z (List.mem_singleton_self z)
  unfold bracketWord
  rw [hl, List.map_append, List.map_append, List.map_singleton, List.map_singleton,
    addLast_concat]
  congr 1
  · apply List.map_congr_left
    intro k hk
    have hle := nextOdd_le_of_mem (mem_oddSet.mpr hz) (hlt k hk)
    have hc : nextOdd r k ≠ r.length := by omega
    simp only [hc, ↓reduceIte, Nat.add_zero]
  · have hc : nextOdd r z = r.length := by
      apply (nextOdd_eq_length_iff hzL).mpr
      intro m hzm hm
      rcases (hmem m).mp (mem_oddPos.mpr hm) with hmi | rfl
      · have := hlt m hmi
        omega
      · omega
    simp only [hc, ↓reduceIte]

/-- Bracket word of an admissible word true :: r with r starting with a 1. -/
theorem bracketWord_cons {r : List Bool} (hA : Admissible (true :: r))
    (hr : r[0]? = some true) : bracketWord (true :: r) = 0 :: addLast 1 (bracketWord r) := by
  have hne : oddPos r ≠ [] := List.ne_nil_of_mem (mem_oddPos.mpr hr)
  rw [← map_colCount_last r hne]
  have hs : true :: r = [true] ++ r := rfl
  have h1 : oddPos [true] = [0] := by decide
  unfold bracketWord
  rw [hs, oddPos_append, h1, ← hs, List.map_append, List.map_singleton, List.map_map,
    colCount_eq, colSet_cons_zero hA hr, Finset.card_empty, List.singleton_append]
  congr 1
  apply List.map_congr_left
  intro k hk
  have hkL := (List.getElem?_eq_some_iff.mp (mem_oddPos.mp hk)).1
  exact colCount_cons_succ hA hkL

/-- Bracket word of the word 10 of Order 1. -/
theorem bracketWord_true_false : bracketWord [true, false] = [1] := by
  have hA : Admissible [true, false] := by
    refine ⟨fun m hm hml => ?_, by norm_num [seqProduct, factor]⟩
    obtain rfl : m = 1 := by
      simp only [List.length_cons, List.length_nil] at hml
      omega
    norm_num [seqProduct, factor]
  have h1 : oddPos [true, false] = [0] := by decide
  have hcol : colSet [true, false] 0 = {0} := by
    ext i
    rw [Finset.mem_singleton]
    constructor
    · intro h
      have := le_of_mem_colSet h
      omega
    · rintro rfl
      refine (mem_colSet_iff (by simp)).mpr ⟨rfl, 2, (lvlDrop_zero_iff hA).mpr rfl, by omega,
        fun m hm0 hm2 hm => ?_⟩
      obtain rfl : m = 1 := by omega
      simp at hm
  unfold bracketWord
  rw [h1, List.map_singleton, colCount_eq, hcol, Finset.card_singleton]

/-- A chain block starts with a 1. -/
theorem getElem?_zero_of_chainBlock {b : List Bool} (hb : IsChainBlock b) :
    b[0]? = some true := by
  have hne := ne_nil_of_admissible b hb.adm
  have hL : 0 < b.length := List.length_pos_iff.mpr hne
  rw [List.getElem?_eq_getElem hL]
  cases hb0 : b[0]
  · have hs := eq_single_of_admissible_false hb.adm (by rw [List.getElem?_eq_getElem hL, hb0])
    have hord := hb.order_pos
    rw [hs] at hord
    simp [order] at hord
  · rfl

/-- Chain recursion of bracket words: for the chain word 1 :: (A1 ++ ... ++ Ak ++ t)
    the bracket word is 0 :: (the bracket words of A1 .. Ak), with 1 added to the
    last entry; [1] for the empty chain. -/
theorem bracketWord_chain {n : ℕ} {bs : List (List Bool)} (h : bs ∈ chainBlocks n) :
    bracketWord (chainWord bs) = addLast 1 (0 :: (bs.map bracketWord).flatten) := by
  have hA := ((mem_admSet (n + 1) _).mp (chainWord_mem h)).1
  have htail : bracketWord (chainTail bs) = [] := by
    rcases chainTail_cases bs with ⟨_, ht⟩ | ⟨_, ht⟩
    · rw [ht]
      decide
    · rw [ht]
      decide
  have hflat : bracketWord (bs.flatten ++ chainTail bs) = (bs.map bracketWord).flatten := by
    rw [bracketWord_flatten_append bs _ fun b hb => bracketsClose_of_admissible (h.1 b hb).adm,
      htail, List.append_nil]
  cases bs with
  | nil =>
    have hup : LevelUp (([] : List (List Bool)).map order) := by decide
    have ht : chainTail [] = [false] := by
      unfold chainTail
      simp only [hup, ↓reduceIte]
    unfold chainWord
    rw [ht]
    exact bracketWord_true_false
  | cons b bs' =>
    have hb0 := getElem?_zero_of_chainBlock (h.1 b List.mem_cons_self)
    have hbL := (List.getElem?_eq_some_iff.mp hb0).1
    have hr : ((b :: bs').flatten ++ chainTail (b :: bs'))[0]? = some true := by
      rw [List.flatten_cons, List.append_assoc, List.getElem?_append_left hbL]
      exact hb0
    unfold chainWord at hA ⊢
    have hne : bracketWord ((b :: bs').flatten ++ chainTail (b :: bs')) ≠ [] := by
      unfold bracketWord
      rw [ne_eq, List.map_eq_nil_iff]
      exact List.ne_nil_of_mem (mem_oddPos.mpr hr)
    rw [bracketWord_cons hA hr, ← hflat, addLast_cons 1 0 hne]

set_option linter.hashCommand false in
#guard addLast 1 [0, 0, 1, 2] = [0, 0, 1, 3]

end AcceleratedCollatz
