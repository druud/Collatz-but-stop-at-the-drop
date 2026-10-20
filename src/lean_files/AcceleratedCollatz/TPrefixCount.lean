-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TBinomial
import AcceleratedCollatz.TRhoBound

/-!
  Counting the admissible PVs of Order n that begin with a given prefix. The count
  depends only on the number of letters still to come and the number of ones so far:
  `cnt n r j` (`card_extSet`), with the Pascal-type rule `cnt_succ`. `rows` builds
  the table row by row, `count n` reads a(n) from it (`card_admSet_eq_count`).
  Compiled code runs `rowStepFast` for `rowStep` (`rowStep_eq_rowStepFast`).
-/

namespace AcceleratedCollatz

/-- Every nonempty prefix of p shorter than p2(n) has level > 1. -/
def GoodPrefix (n : ℕ) (p : List Bool) : Prop :=
  ∀ m, 1 ≤ m → m ≤ p.length → m < p2_of n → 1 < seqProduct (p.take m)

/-- Admissible PVs of Order n that begin with p. -/
def extSet (n : ℕ) (p : List Bool) : Finset (List Bool) :=
  (admSet n).filter (fun s => p <+: s)

theorem mem_extSet (n : ℕ) (p s : List Bool) :
    s ∈ extSet n p ↔ (Admissible s ∧ order s = n) ∧ p <+: s := by
  simp only [extSet, Finset.mem_filter, mem_admSet]

theorem extSet_nil (n : ℕ) : extSet n [] = admSet n := by
  ext s
  simp [extSet]

theorem goodPrefix_nil (n : ℕ) : GoodPrefix n [] := by
  intro m hm1 hm _
  rw [List.length_nil] at hm
  omega

/-- A prefix of an admissible PV of Order n is good. -/
theorem goodPrefix_of_mem_extSet {n : ℕ} {p s : List Bool} (h : s ∈ extSet n p) :
    GoodPrefix n p := by
  obtain ⟨⟨hA, hord⟩, t, rfl⟩ := (mem_extSet n p s).mp h
  intro m hm1 hm hlt
  have hlen := admissible_length _ hA
  rw [hord] at hlen
  have hgt := hA.prefix_gt m hm1 (by omega)
  rwa [List.take_append_of_le_length hm] at hgt

/-- One more letter keeps a prefix good iff the longer prefix is complete or has
    level > 1. -/
theorem goodPrefix_append_single (n : ℕ) (p : List Bool) (b : Bool) :
    GoodPrefix n (p ++ [b]) ↔
      GoodPrefix n p ∧ (p.length + 1 < p2_of n → 1 < seqProduct (p ++ [b])) := by
  have hl : (p ++ [b]).length = p.length + 1 := by
    rw [List.length_append, List.length_singleton]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro m hm1 hm hlt
      have hgt := h m hm1 (by omega) hlt
      rwa [List.take_append_of_le_length hm] at hgt
    · intro hlt
      have hgt := h (p.length + 1) (by omega) (by omega) hlt
      rwa [List.take_of_length_le (by omega)] at hgt
  · rintro ⟨hp, hb⟩ m hm1 hm hlt
    rcases Nat.lt_or_ge m (p.length + 1) with h | h
    · rw [List.take_append_of_le_length (by omega)]
      exact hp m hm1 (by omega) hlt
    · rw [List.take_of_length_le (by omega)]
      exact hb (by omega)

/-- A good word of length p2(n) is admissible of Order n iff it has n ones. -/
theorem mem_admSet_iff_of_goodPrefix {n : ℕ} {p : List Bool} (hG : GoodPrefix n p)
    (hlen : p.length = p2_of n) : p ∈ admSet n ↔ order p = n := by
  rw [mem_admSet]
  constructor
  · exact fun h => h.2
  · intro ho
    refine ⟨⟨fun m hm1 hm => hG m hm1 hm.le (by omega), ?_⟩, ho⟩
    rw [seqProduct_lt_one_iff, ho, hlen]
    exact p2_of_spec n

/-- At full length the only candidate is the word itself. -/
theorem card_extSet_full {n : ℕ} {p : List Bool} (hlen : p.length = p2_of n) :
    (extSet n p).card = if p ∈ admSet n then 1 else 0 := by
  have hsub : ∀ s ∈ extSet n p, s = p := by
    intro s hs
    obtain ⟨⟨hA, ho⟩, hpre⟩ := (mem_extSet n p s).mp hs
    have hl := admissible_length s hA
    rw [ho] at hl
    exact (hpre.eq_of_length (by omega)).symm
  split_ifs with hp
  · rw [Finset.card_eq_one]
    refine ⟨p, Finset.eq_singleton_iff_unique_mem.mpr ⟨?_, hsub⟩⟩
    exact (mem_extSet n p p).mpr ⟨(mem_admSet n p).mp hp, List.prefix_refl p⟩
  · rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro s hs
    have hsp := hsub s hs
    subst hsp
    exact hp ((mem_admSet n s).mpr ((mem_extSet n s s).mp hs).1)

/-- Below full length the extensions split by the next letter. -/
theorem card_extSet_split {n : ℕ} {p : List Bool} (hlen : p.length < p2_of n) :
    (extSet n p).card = (extSet n (p ++ [false])).card + (extSet n (p ++ [true])).card := by
  have hu : extSet n p = extSet n (p ++ [false]) ∪ extSet n (p ++ [true]) := by
    ext s
    rw [Finset.mem_union, mem_extSet, mem_extSet, mem_extSet]
    constructor
    · rintro ⟨hs, t, rfl⟩
      have hl := admissible_length _ hs.1
      rw [hs.2, List.length_append] at hl
      cases t with
      | nil =>
        rw [List.length_nil] at hl
        omega
      | cons b t =>
        cases b with
        | false =>
          exact Or.inl ⟨hs, t, by rw [List.append_assoc, List.singleton_append]⟩
        | true =>
          exact Or.inr ⟨hs, t, by rw [List.append_assoc, List.singleton_append]⟩
    · rintro (⟨hs, h⟩ | ⟨hs, h⟩)
      · exact ⟨hs, (List.prefix_append p [false]).trans h⟩
      · exact ⟨hs, (List.prefix_append p [true]).trans h⟩
  have hd : Disjoint (extSet n (p ++ [false])) (extSet n (p ++ [true])) := by
    rw [Finset.disjoint_left]
    intro s h1 h2
    obtain ⟨_, t1, rfl⟩ := (mem_extSet n _ s).mp h1
    obtain ⟨_, t2, h⟩ := (mem_extSet n _ _).mp h2
    rw [List.append_assoc, List.append_assoc, List.append_cancel_left_eq, List.singleton_append,
      List.singleton_append, List.cons.injEq] at h
    exact absurd h.1 (by decide)
  rw [hu, Finset.card_union_of_disjoint hd]

/-- Number of admissible PVs of Order n that begin with a good prefix with r letters
    to come and j ones. -/
def cnt (n : ℕ) : ℕ → ℕ → ℕ
  | 0, j => if j = n then 1 else 0
  | r + 1, j =>
    (if r = 0 ∨ 2 ^ (p2_of n - r) < 3 ^ j then cnt n r j else 0) +
      (if r = 0 ∨ 2 ^ (p2_of n - r) < 3 ^ (j + 1) then cnt n r (j + 1) else 0)

/-- `cnt` after one more letter: 0 unless the longer prefix is complete or has
    level > 1. -/
def childCnt (n r j : ℕ) : ℕ :=
  if r = 0 ∨ 2 ^ (p2_of n - r) < 3 ^ j then cnt n r j else 0

theorem cnt_succ (n r j : ℕ) : cnt n (r + 1) j = childCnt n r j + childCnt n r (j + 1) := by
  rw [cnt]
  rfl

theorem cnt_eq_zero (n : ℕ) : ∀ r j, n < j → cnt n r j = 0
  | 0, j, h => by
    rw [cnt, ite_eq_right (by omega)]
  | r + 1, j, h => by
    rw [cnt, cnt_eq_zero n r j h, cnt_eq_zero n r (j + 1) (by omega)]
    simp

/-- The extensions of a good prefix by one letter. -/
theorem card_extSet_child {n r : ℕ} {p : List Bool} (b : Bool) (hG : GoodPrefix n p)
    (hlen : p.length + 1 + r = p2_of n)
    (ih : ∀ q, GoodPrefix n q → q.length + r = p2_of n →
      (extSet n q).card = cnt n r (order q)) :
    (extSet n (p ++ [b])).card = childCnt n r (order (p ++ [b])) := by
  have hl : (p ++ [b]).length = p.length + 1 := by
    rw [List.length_append, List.length_singleton]
  have hpow : p2_of n - r = (p ++ [b]).length := by omega
  unfold childCnt
  rw [hpow]
  by_cases hok : r = 0 ∨ 2 ^ (p ++ [b]).length < 3 ^ order (p ++ [b])
  · rw [ite_eq_left hok]
    apply ih
    · rw [goodPrefix_append_single]
      refine ⟨hG, fun hlt => ?_⟩
      rw [one_lt_seqProduct_iff]
      rcases hok with h0 | h
      · omega
      · exact h
    · omega
  · rw [ite_eq_right hok, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro s hs
    have hg := (goodPrefix_append_single n p b).mp (goodPrefix_of_mem_extSet hs)
    have hr : r ≠ 0 := fun h => hok (Or.inl h)
    exact hok (Or.inr ((one_lt_seqProduct_iff _).mp (hg.2 (by omega))))

/-- The admissible PVs of Order n beginning with a good prefix number `cnt`. -/
theorem card_extSet {n : ℕ} : ∀ (r : ℕ) (p : List Bool), GoodPrefix n p →
    p.length + r = p2_of n → (extSet n p).card = cnt n r (order p)
  | 0, p, hG, hlen => by
    rw [card_extSet_full (by omega), cnt]
    by_cases ho : order p = n
    · rw [ite_eq_left ((mem_admSet_iff_of_goodPrefix hG (by omega)).mpr ho), ite_eq_left ho]
    · rw [ite_eq_right (fun h => ho ((mem_admSet_iff_of_goodPrefix hG (by omega)).mp h)),
        ite_eq_right ho]
  | r + 1, p, hG, hlen => by
    rw [card_extSet_split (by omega), cnt_succ,
      card_extSet_child false hG (by omega) (card_extSet r),
      card_extSet_child true hG (by omega) (card_extSet r),
      order_append_single, order_append_single]
    simp

/-- a(n) from the count of the empty prefix. -/
theorem card_admSet_eq_cnt (n : ℕ) : (admSet n).card = cnt n (p2_of n) 0 := by
  rw [← extSet_nil, card_extSet (p2_of n) [] (goodPrefix_nil n) (by simp)]
  rfl

/-- Row r + 1 of the table from row r. -/
def rowStep (n r : ℕ) (prev : List ℕ) : List ℕ :=
  (List.range (n + 1)).map fun j =>
    (if r = 0 ∨ 2 ^ (p2_of n - r) < 3 ^ j then prev.getD j 0 else 0) +
      (if r = 0 ∨ 2 ^ (p2_of n - r) < 3 ^ (j + 1) then prev.getD (j + 1) 0 else 0)

/-- Entries j, j + 1, ... of a row, from the previous row without its first j entries;
    t = the least number of ones that gives level > 1. -/
def rowGo (t : ℕ) : ℕ → ℕ → List ℕ → List ℕ
  | 0, _, _ => []
  | m + 1, j, l =>
    ((if t ≤ j then l.headD 0 else 0) + (if t ≤ j + 1 then l.tail.headD 0 else 0)) ::
      rowGo t m (j + 1) l.tail

/-- `rowStep` with one threshold per row for the powers, and one pass over the
    previous row. -/
def rowStepFast (n r : ℕ) (prev : List ℕ) : List ℕ :=
  rowGo (if r = 0 then 0 else Nat.log 3 (2 ^ (p2_of n - r)) + 1) (n + 1) 0 prev

theorem headD_drop (l : List ℕ) (j : ℕ) : (l.drop j).headD 0 = l.getD j 0 := by
  rw [List.headD_eq_head?_getD, List.head?_drop, List.getD_eq_getElem?_getD]

theorem rowGo_drop (t : ℕ) (prev : List ℕ) : ∀ m j,
    rowGo t m j (prev.drop j) = (List.range' j m).map fun i =>
      (if t ≤ i then prev.getD i 0 else 0) + (if t ≤ i + 1 then prev.getD (i + 1) 0 else 0)
  | 0, _ => rfl
  | m + 1, j => by
    rw [rowGo, List.tail_drop, headD_drop, headD_drop, rowGo_drop t prev m (j + 1),
      List.range'_succ]
    rfl

/-- Compiled code runs `rowStepFast` for `rowStep`. -/
@[csimp]
theorem rowStep_eq_rowStepFast : @rowStep = @rowStepFast := by
  funext n r prev
  have h := rowGo_drop (if r = 0 then 0 else Nat.log 3 (2 ^ (p2_of n - r)) + 1) prev (n + 1) 0
  rw [List.drop_zero] at h
  rw [rowStepFast, h, rowStep, List.range_eq_range']
  apply List.map_congr_left
  intro j _
  by_cases hr : r = 0
  · simp [hr]
  · have hc : ∀ i, (r = 0 ∨ 2 ^ (p2_of n - r) < 3 ^ i) ↔
        Nat.log 3 (2 ^ (p2_of n - r)) + 1 ≤ i := by
      intro i
      rw [Nat.succ_le_iff, Nat.log_lt_iff_lt_pow (by omega) (by positivity)]
      exact or_iff_right hr
    simp only [hc]
    simp only [hr, ↓reduceIte]

/-- Rows r, r - 1, ..., 0 of the table; row r lists `cnt n r j` for j ≤ n. -/
def rows (n : ℕ) : ℕ → List (List ℕ)
  | 0 => [(List.range (n + 1)).map fun j => if j = n then 1 else 0]
  | r + 1 =>
    let t := rows n r
    rowStep n r (t.headD []) :: t

/-- Row r of the table. -/
def row (n r : ℕ) : List ℕ := (rows n r).headD []

theorem rows_succ (n r : ℕ) : rows n (r + 1) = row n (r + 1) :: rows n r :=
  rfl

theorem row_succ (n r : ℕ) : row n (r + 1) = rowStep n r (row n r) :=
  rfl

theorem length_rows (n : ℕ) : ∀ r, (rows n r).length = r + 1
  | 0 => rfl
  | r + 1 => by
    rw [rows_succ, List.length_cons, length_rows n r]

theorem getD_map_range (f : ℕ → ℕ) (m j : ℕ) :
    ((List.range m).map f).getD j 0 = if j < m then f j else 0 := by
  by_cases h : j < m
  · simp [List.getD_eq_getElem?_getD, h]
  · simp [List.getD_eq_getElem?_getD, h]

/-- The table holds `cnt`. -/
theorem getD_row (n : ℕ) : ∀ r j, (row n r).getD j 0 = cnt n r j
  | 0, j => by
    change ((List.range (n + 1)).map fun j => if j = n then 1 else 0).getD j 0 = _
    rw [getD_map_range, cnt]
    by_cases h : j < n + 1
    · rw [ite_eq_left h]
    · rw [ite_eq_right h, ite_eq_right (by omega)]
  | r + 1, j => by
    rw [row_succ, rowStep, getD_map_range]
    by_cases h : j < n + 1
    · rw [ite_eq_left h, getD_row n r j, getD_row n r (j + 1), cnt]
    · rw [ite_eq_right h, cnt_eq_zero n (r + 1) j (by omega)]

/-- a(n), read from the table. -/
def count (n : ℕ) : ℕ := (row n (p2_of n)).getD 0 0

/-- `count n` is the number of admissible PVs of Order n. -/
theorem card_admSet_eq_count (n : ℕ) : (admSet n).card = count n := by
  rw [card_admSet_eq_cnt, count, getD_row]

-- A100982: a(0..7), and a(60).
set_option linter.hashCommand false in
#guard (List.range 8).map count = [1, 1, 1, 2, 3, 7, 12, 30]

set_option linter.hashCommand false in
#guard count 60 = 1325438036712274130536314

end AcceleratedCollatz
