-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TBracketDrop
import AcceleratedCollatz.TRhoBound

/-!
  The bracket word of an admissible word of Order n is a Dyck path with n up and
  n down steps: its entries sum to n (`sum_bracketWord`) and the closes in the
  columns of the odd positions below p number at most the odd positions below p
  (`sum_colCount_lt_le`). Every column closes at least as many brackets as it has
  halvings (`halvings_le_colCount`); the surplus, the shared closes, totals
  2 n - p2(n) (`sum_sharedCloses`).
-/

namespace AcceleratedCollatz

variable {s : List Bool}

/-- Odd positions of s. -/
def oddSet (s : List Bool) : Finset ℕ :=
  (Finset.range s.length).filter (fun i => s[i]? = some true)

/-- Odd positions i < j whose bracket closes at j. -/
def closeSet (s : List Bool) (j : ℕ) : Finset ℕ :=
  (Finset.range j).filter (fun i => s[i]? = some true ∧ LvlDrop s i j)

/-- Odd positions whose bracket closes in the column of k. -/
def colSet (s : List Bool) (k : ℕ) : Finset ℕ :=
  (Finset.Ioc k (nextOdd s k)).biUnion (closeSet s)

theorem mem_oddSet {i : ℕ} : i ∈ oddSet s ↔ s[i]? = some true := by
  unfold oddSet
  rw [Finset.mem_filter, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨(List.getElem?_eq_some_iff.mp h).1, h⟩

theorem card_oddSet (s : List Bool) : (oddSet s).card = order s := by
  induction s using List.reverseRecOn with
  | nil => simp [oddSet, order]
  | append_singleton t b ih =>
    unfold oddSet at ih ⊢
    rw [Finset.card_filter] at ih ⊢
    rw [List.length_append, List.length_singleton, Finset.sum_range_succ,
      order_append_single, ← ih]
    congr 1
    · apply Finset.sum_congr rfl
      intro i hi
      rw [List.getElem?_append_left (Finset.mem_range.mp hi)]
    · cases b with
      | false => simp
      | true => simp

theorem sum_bracketWord_eq (s : List Bool) :
    (bracketWord s).sum = ∑ k ∈ oddSet s, colCount s k := by
  simp [bracketWord, oddPos, oddSet, Finset.sum, Finset.filter_val, Finset.range_val,
    Multiset.range]

theorem nextOdd_le (s : List Bool) (k : ℕ) : nextOdd s k ≤ s.length := by
  unfold nextOdd
  split_ifs with h
  · exact (Nat.find_spec h).1.le
  · exact le_rfl

theorem lt_nextOdd {k : ℕ} (hk : k < s.length) : k < nextOdd s k := by
  unfold nextOdd
  split_ifs with h
  · exact (Nat.find_spec h).2.1
  · exact hk

theorem nextOdd_mem {k : ℕ} (h : nextOdd s k < s.length) : nextOdd s k ∈ oddSet s := by
  unfold nextOdd at h ⊢
  split_ifs with hex
  · exact mem_oddSet.mpr (Nat.find_spec hex).2.2
  · simp [hex] at h

theorem nextOdd_le_of_mem {k m : ℕ} (hm : m ∈ oddSet s) (hkm : k < m) : nextOdd s k ≤ m := by
  have hodd := mem_oddSet.mp hm
  have hmL := (List.getElem?_eq_some_iff.mp hodd).1
  unfold nextOdd
  split_ifs with h
  · exact Nat.find_min' h ⟨hmL, hkm, hodd⟩
  · exact absurd ⟨m, hmL, hkm, hodd⟩ h

/-- The columns of distinct odd positions are disjoint. -/
theorem column_unique {k k' j : ℕ} (hk : k ∈ oddSet s) (hk' : k' ∈ oddSet s)
    (h : k < j ∧ j ≤ nextOdd s k) (h' : k' < j ∧ j ≤ nextOdd s k') : k = k' := by
  rcases lt_trichotomy k k' with hlt | heq | hgt
  · have := nextOdd_le_of_mem hk' hlt
    omega
  · exact heq
  · have := nextOdd_le_of_mem hk hgt
    omega

/-- Every position j ≤ |s| after an odd i lies in the column of an odd k ≥ i. -/
theorem exists_column {i j : ℕ} (hi : i ∈ oddSet s) (hij : i < j) (hjL : j ≤ s.length) :
    ∃ k ∈ oddSet s, i ≤ k ∧ k < j ∧ j ≤ nextOdd s k := by
  have hiF : i ∈ (oddSet s).filter (· < j) := Finset.mem_filter.mpr ⟨hi, hij⟩
  have hne : ((oddSet s).filter (· < j)).Nonempty := ⟨i, hiF⟩
  have hk := Finset.mem_filter.mp (Finset.max'_mem _ hne)
  refine ⟨_, hk.1, Finset.le_max' _ i hiF, hk.2, ?_⟩
  set m := ((oddSet s).filter (· < j)).max' hne with hm
  by_contra hlt
  push Not at hlt
  have hmem := nextOdd_mem (s := s) (k := m) (by omega)
  have hgt := lt_nextOdd (s := s) (k := m) (by omega)
  have hle := Finset.le_max' ((oddSet s).filter (· < j)) _
    (Finset.mem_filter.mpr ⟨hmem, hlt⟩)
  rw [← hm] at hle
  omega

theorem lvlDrop_unique {i j j' : ℕ} (h : LvlDrop s i j) (h' : LvlDrop s i j') : j = j' := by
  obtain ⟨hij, hj, hmin⟩ := h
  obtain ⟨hij', hj', hmin'⟩ := h'
  rcases lt_trichotomy j j' with hlt | heq | hgt
  · exact absurd (hmin' j hlt hij) (not_le.mpr hj)
  · exact heq
  · exact absurd (hmin j' hgt hij') (not_le.mpr hj')

/-- In an admissible word every bracket closes, at the latest at the end. -/
theorem exists_lvlDrop_of_mem (hA : Admissible s) {i : ℕ} (hi : i ∈ oddSet s) :
    ∃ j, LvlDrop s i j ∧ j ≤ s.length := by
  have hiL := (List.getElem?_eq_some_iff.mp (mem_oddSet.mp hi)).1
  have hL : lvl s s.length < 1 := by
    unfold lvl
    rw [List.take_length]
    exact hA.lt_one
  have hi1 : 1 ≤ lvl s i := by
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · rw [lvl_zero]
    · exact (hA.prefix_gt i hpos hiL).le
  exact exists_lvlDrop_le hiL (by linarith)

theorem mem_closeSet {i j : ℕ} : i ∈ closeSet s j ↔ s[i]? = some true ∧ LvlDrop s i j := by
  unfold closeSet
  rw [Finset.mem_filter, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨h.2.1, h⟩

theorem sum_closesAt (J : Finset ℕ) :
    ∑ j ∈ J, closesAt s j = (J.biUnion (closeSet s)).card := by
  rw [Finset.card_biUnion]
  · rfl
  intro j _ j' _ hne
  change Disjoint (closeSet s j) (closeSet s j')
  rw [Finset.disjoint_left]
  intro i hi hi'
  exact hne (lvlDrop_unique (mem_closeSet.mp hi).2 (mem_closeSet.mp hi').2)

theorem colCount_eq (k : ℕ) : colCount s k = (colSet s k).card := sum_closesAt _

theorem mem_colSet {i k : ℕ} : i ∈ colSet s k ↔
    ∃ j, (k < j ∧ j ≤ nextOdd s k) ∧ s[i]? = some true ∧ LvlDrop s i j := by
  unfold colSet
  simp only [Finset.mem_biUnion, Finset.mem_Ioc, mem_closeSet]

theorem sum_colCount (K : Finset ℕ) (hK : K ⊆ oddSet s) :
    ∑ k ∈ K, colCount s k = (K.biUnion (colSet s)).card := by
  rw [Finset.card_biUnion]
  · exact Finset.sum_congr rfl fun k _ => colCount_eq k
  · intro k hk k' hk' hne
    change Disjoint (colSet s k) (colSet s k')
    rw [Finset.disjoint_left]
    intro i hi hi'
    obtain ⟨j, hj, _, hd⟩ := mem_colSet.mp hi
    obtain ⟨j', hj', _, hd'⟩ := mem_colSet.mp hi'
    have hjj := lvlDrop_unique hd hd'
    subst hjj
    exact hne (column_unique (hK hk) (hK hk') hj hj')

/-- A bracket closing in the column of k was opened at an odd position ≤ k. -/
theorem le_of_mem_colSet {i k : ℕ} (h : i ∈ colSet s k) : i ≤ k := by
  obtain ⟨j, hj, hodd, hd⟩ := mem_colSet.mp h
  by_contra hlt
  push Not at hlt
  have := nextOdd_le_of_mem (mem_oddSet.mpr hodd) hlt
  have := hd.1
  omega

/-- Dyck prefix bound: the columns below p close at most as many brackets as open
    below p. -/
theorem sum_colCount_lt_le (p : ℕ) :
    ∑ k ∈ (oddSet s).filter (· < p), colCount s k ≤ ((oddSet s).filter (· < p)).card := by
  rw [sum_colCount _ (Finset.filter_subset _ _)]
  apply Finset.card_le_card
  intro i hi
  obtain ⟨k, hk, hik⟩ := Finset.mem_biUnion.mp hi
  obtain ⟨j, _, hodd, _⟩ := mem_colSet.mp hik
  exact Finset.mem_filter.mpr ⟨mem_oddSet.mpr hodd,
    lt_of_le_of_lt (le_of_mem_colSet hik) (Finset.mem_filter.mp hk).2⟩

/-- The entries of the bracket word sum to the Order. -/
theorem sum_bracketWord (hA : Admissible s) : (bracketWord s).sum = order s := by
  rw [sum_bracketWord_eq, sum_colCount _ subset_rfl, ← card_oddSet]
  congr 1
  ext i
  constructor
  · intro hi
    obtain ⟨k, _, hik⟩ := Finset.mem_biUnion.mp hi
    obtain ⟨j, _, hodd, _⟩ := mem_colSet.mp hik
    exact mem_oddSet.mpr hodd
  · intro hi
    obtain ⟨j, hd, hjL⟩ := exists_lvlDrop_of_mem hA hi
    obtain ⟨k, hk, _, hkj, hjn⟩ := exists_column hi hd.1 hjL
    exact Finset.mem_biUnion.mpr ⟨k, hk, mem_colSet.mpr ⟨j, ⟨hkj, hjn⟩,
      mem_oddSet.mp hi, hd⟩⟩

/-- Every column closes at least as many brackets as it has halvings. -/
theorem halvings_le_colCount (hA : Admissible s) (k : ℕ) :
    nextOdd s k - k - 1 ≤ colCount s k := by
  unfold colCount
  calc nextOdd s k - k - 1 = ∑ _j ∈ Finset.Ioc (k + 1) (nextOdd s k), 1 := by
        rw [Finset.sum_const, Nat.card_Ioc, smul_eq_mul, mul_one]
        omega
    _ ≤ ∑ j ∈ Finset.Ioc (k + 1) (nextOdd s k), closesAt s j := by
        apply Finset.sum_le_sum
        intro j hj
        rw [Finset.mem_Ioc] at hj
        have hjL := nextOdd_le s k
        have hnot : j - 1 ∉ oddSet s := by
          intro hm
          have := nextOdd_le_of_mem hm (by omega : k < j - 1)
          omega
        have hlt : j - 1 < s.length := by omega
        have hf : s[j - 1]? = some false := by
          rw [List.getElem?_eq_getElem hlt]
          cases hb : s[j - 1]
          · rfl
          · exact absurd (mem_oddSet.mpr (by rw [List.getElem?_eq_getElem hlt, hb])) hnot
        have hpos := closesAt_pos_of_halving hA (by omega) hlt hf
        rw [Nat.sub_add_cancel (by omega)] at hpos
        exact hpos
    _ ≤ ∑ j ∈ Finset.Ioc k (nextOdd s k), closesAt s j := by
        apply Finset.sum_le_sum_of_subset
        exact Finset.Ioc_subset_Ioc_left (by omega)

/-- The columns of the odd positions cover the positions 1..|s| once each. -/
theorem sum_column_widths (h0 : 0 ∈ oddSet s) :
    ∑ k ∈ oddSet s, (nextOdd s k - k) = s.length := by
  have hcard : ((oddSet s).biUnion (fun k => Finset.Ioc k (nextOdd s k))).card =
      ∑ k ∈ oddSet s, (nextOdd s k - k) := by
    rw [Finset.card_biUnion]
    · exact Finset.sum_congr rfl fun k _ => Nat.card_Ioc _ _
    · intro k hk k' hk' hne
      change Disjoint (Finset.Ioc k (nextOdd s k)) (Finset.Ioc k' (nextOdd s k'))
      rw [Finset.disjoint_left]
      intro j hj hj'
      exact hne (column_unique hk hk' (Finset.mem_Ioc.mp hj) (Finset.mem_Ioc.mp hj'))
  have hset : (oddSet s).biUnion (fun k => Finset.Ioc k (nextOdd s k)) =
      Finset.Ioc 0 s.length := by
    ext j
    rw [Finset.mem_biUnion, Finset.mem_Ioc]
    constructor
    · rintro ⟨k, _, hj⟩
      rw [Finset.mem_Ioc] at hj
      have := nextOdd_le s k
      omega
    · rintro ⟨hj0, hjL⟩
      obtain ⟨k, hk, _, hkj, hjn⟩ := exists_column h0 hj0 hjL
      exact ⟨k, hk, Finset.mem_Ioc.mpr ⟨hkj, hjn⟩⟩
  rw [← hcard, hset, Nat.card_Ioc, Nat.sub_zero]

/-- Shared closes: the surplus of closes over halvings, summed over the columns, is
    2 order s - |s|. -/
theorem sum_sharedCloses (hA : Admissible s) (hord : 1 ≤ order s) :
    ∑ k ∈ oddSet s, (colCount s k - (nextOdd s k - k - 1)) + s.length = 2 * order s := by
  have hL : 0 < s.length := by
    rcases s with _ | ⟨b, t⟩
    · simp [order] at hord
    · simp
  have h0 : 0 ∈ oddSet s := by
    rw [mem_oddSet, List.getElem?_eq_getElem hL]
    cases hb : s[0]
    · have hs := eq_single_of_admissible_false hA (by rw [List.getElem?_eq_getElem hL, hb])
      subst hs
      simp [order] at hord
    · rfl
  rw [Finset.sum_tsub_distrib _ fun k _ => halvings_le_colCount hA k]
  have hc : ∑ k ∈ oddSet s, colCount s k = order s := by
    rw [← sum_bracketWord_eq]
    exact sum_bracketWord hA
  have hw := sum_column_widths h0
  have hsplit : ∑ k ∈ oddSet s, (nextOdd s k - k) =
      ∑ k ∈ oddSet s, (nextOdd s k - k - 1) + (oddSet s).card := by
    rw [Finset.card_eq_sum_ones, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    have := lt_nextOdd (s := s) (List.getElem?_eq_some_iff.mp (mem_oddSet.mp hk)).1
    omega
  have hle : ∑ k ∈ oddSet s, (nextOdd s k - k - 1) ≤ ∑ k ∈ oddSet s, colCount s k :=
    Finset.sum_le_sum fun k _ => halvings_le_colCount hA k
  rw [card_oddSet] at hsplit
  omega

end AcceleratedCollatz
