-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TBracketDyck
import AcceleratedCollatz.TBracketQ

/-!
  The bracket word of an admissible word of Order n of the q-family (q ≥ 3) holds
  e n closes, e = `bracketsQ q`: every bracket closes exactly once, at the latest at
  the end (`exists_lvlDropQ_of_mem`, `lvlDropQ_unique`), so the entries sum to e n
  (`sum_bracketWordQ`), and the closes in the columns of the odd positions below p
  number at most e times the odd positions below p (`sum_colCountQ_lt_le`). Every
  column closes at least as many brackets as it has halvings (`halvings_le_colCountQ`);
  the surplus, the shared closes, totals (e + 1) n - p2Q q n (`sum_sharedClosesQ`).
-/

namespace AcceleratedCollatz

variable {q : ℕ} {s : List Bool}

/-- Brackets (i, m), i an odd position below j and m < `bracketsQ q`, that close at j. -/
def closeSetQ (q : ℕ) (s : List Bool) (j : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range j ×ˢ Finset.range (bracketsQ q)).filter
    (fun x => s[x.1]? = some true ∧ LvlDropQ q s x.1 x.2 j)

/-- Brackets that close in the column of k. -/
def colSetQ (q : ℕ) (s : List Bool) (k : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Ioc k (nextOdd s k)).biUnion (closeSetQ q s)

theorem lvlDropQ_unique {i m j j' : ℕ} (h : LvlDropQ q s i m j) (h' : LvlDropQ q s i m j') :
    j = j' := by
  obtain ⟨hij, hj, hmin⟩ := h
  obtain ⟨hij', hj', hmin'⟩ := h'
  rcases lt_trichotomy j j' with hlt | heq | hgt
  · exact absurd (hmin' j hlt hij) (not_le.mpr hj)
  · exact heq
  · exact absurd (hmin j' hgt hij') (not_le.mpr hj')

/-- Any level below the threshold of bracket m of i, after i, gives a close of that
    bracket no later. -/
theorem exists_lvlDropQ_le {i m j : ℕ} (hij : i < j)
    (hj : lvlQ q s j < 2 ^ m * lvlQ q s i) : ∃ j', LvlDropQ q s i m j' ∧ j' ≤ j := by
  classical
  have hex : ∃ r, i < r ∧ lvlQ q s r < 2 ^ m * lvlQ q s i := ⟨j, hij, hj⟩
  refine ⟨Nat.find hex, ⟨(Nat.find_spec hex).1, (Nat.find_spec hex).2, ?_⟩,
    Nat.find_min' hex ⟨hij, hj⟩⟩
  intro k hk hik
  by_contra hlt
  exact Nat.find_min hex hk ⟨hik, not_le.mp hlt⟩

/-- In an admissible word every bracket closes, at the latest at the end. -/
theorem exists_lvlDropQ_of_mem (hA : AdmissibleQ q s) {i : ℕ} (hi : i ∈ oddSet s) (m : ℕ) :
    ∃ j, LvlDropQ q s i m j ∧ j ≤ s.length := by
  have hiL := (List.getElem?_eq_some_iff.mp (mem_oddSet.mp hi)).1
  have hL : lvlQ q s s.length < 1 := by
    rw [lvlQ_length]
    exact hA.lt_one
  have hi1 : 1 ≤ lvlQ q s i := by
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · rw [lvlQ_zero]
    · exact (hA.prefix_gt i hpos hiL).le
  have h2 : (1 : ℚ) ≤ 2 ^ m := one_le_pow₀ (by norm_num)
  have hthr : 1 ≤ 2 ^ m * lvlQ q s i := one_le_mul_of_one_le_of_one_le h2 hi1
  exact exists_lvlDropQ_le hiL (by linarith)

theorem mem_closeSetQ {x : ℕ × ℕ} {j : ℕ} :
    x ∈ closeSetQ q s j ↔
      x.2 < bracketsQ q ∧ s[x.1]? = some true ∧ LvlDropQ q s x.1 x.2 j := by
  unfold closeSetQ
  rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]
  constructor
  · rintro ⟨⟨_, h2⟩, h3⟩
    exact ⟨h2, h3⟩
  · rintro ⟨h2, h3⟩
    exact ⟨⟨h3.2.1, h2⟩, h3⟩

theorem sum_closesAtQ (J : Finset ℕ) :
    ∑ j ∈ J, closesAtQ q s j = (J.biUnion (closeSetQ q s)).card := by
  rw [Finset.card_biUnion]
  · rfl
  intro j _ j' _ hne
  change Disjoint (closeSetQ q s j) (closeSetQ q s j')
  rw [Finset.disjoint_left]
  intro x hx hx'
  exact hne (lvlDropQ_unique (mem_closeSetQ.mp hx).2.2 (mem_closeSetQ.mp hx').2.2)

theorem colCountQ_eq (k : ℕ) : colCountQ q s k = (colSetQ q s k).card := sum_closesAtQ _

theorem mem_colSetQ {x : ℕ × ℕ} {k : ℕ} : x ∈ colSetQ q s k ↔
    ∃ j, (k < j ∧ j ≤ nextOdd s k) ∧
      x.2 < bracketsQ q ∧ s[x.1]? = some true ∧ LvlDropQ q s x.1 x.2 j := by
  unfold colSetQ
  simp only [Finset.mem_biUnion, Finset.mem_Ioc, mem_closeSetQ]

theorem sum_colCountQ (K : Finset ℕ) (hK : K ⊆ oddSet s) :
    ∑ k ∈ K, colCountQ q s k = (K.biUnion (colSetQ q s)).card := by
  rw [Finset.card_biUnion]
  · exact Finset.sum_congr rfl fun k _ => colCountQ_eq k
  · intro k hk k' hk' hne
    change Disjoint (colSetQ q s k) (colSetQ q s k')
    rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨j, hj, _, _, hd⟩ := mem_colSetQ.mp hx
    obtain ⟨j', hj', _, _, hd'⟩ := mem_colSetQ.mp hx'
    have hjj := lvlDropQ_unique hd hd'
    subst hjj
    exact hne (column_unique (hK hk) (hK hk') hj hj')

theorem sum_bracketWordQ_eq (q : ℕ) (s : List Bool) :
    (bracketWordQ q s).sum = ∑ k ∈ oddSet s, colCountQ q s k := by
  simp [bracketWordQ, oddPos, oddSet, Finset.sum, Finset.filter_val, Finset.range_val,
    Multiset.range]

/-- A bracket closing in the column of k was opened at an odd position ≤ k. -/
theorem le_of_mem_colSetQ {x : ℕ × ℕ} {k : ℕ} (h : x ∈ colSetQ q s k) : x.1 ≤ k := by
  obtain ⟨j, hj, _, hodd, hd⟩ := mem_colSetQ.mp h
  by_contra hlt
  push Not at hlt
  have := nextOdd_le_of_mem (mem_oddSet.mpr hodd) hlt
  have := hd.1
  omega

/-- Prefix bound: the columns below p close at most as many brackets as open below p. -/
theorem sum_colCountQ_lt_le (q : ℕ) (s : List Bool) (p : ℕ) :
    ∑ k ∈ (oddSet s).filter (· < p), colCountQ q s k ≤
      bracketsQ q * ((oddSet s).filter (· < p)).card := by
  have hcard : (((oddSet s).filter (· < p)) ×ˢ Finset.range (bracketsQ q)).card =
      bracketsQ q * ((oddSet s).filter (· < p)).card := by
    rw [Finset.card_product, Finset.card_range, Nat.mul_comm]
  rw [sum_colCountQ _ (Finset.filter_subset _ _), ← hcard]
  apply Finset.card_le_card
  intro x hx
  obtain ⟨k, hk, hxk⟩ := Finset.mem_biUnion.mp hx
  obtain ⟨j, _, hm, hodd, _⟩ := mem_colSetQ.mp hxk
  exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨mem_oddSet.mpr hodd,
    lt_of_le_of_lt (le_of_mem_colSetQ hxk) (Finset.mem_filter.mp hk).2⟩,
    Finset.mem_range.mpr hm⟩

/-- The entries of the bracket word sum to `bracketsQ q` times the Order. -/
theorem sum_bracketWordQ (hA : AdmissibleQ q s) :
    (bracketWordQ q s).sum = bracketsQ q * order s := by
  have hcard : (oddSet s ×ˢ Finset.range (bracketsQ q)).card = bracketsQ q * order s := by
    rw [Finset.card_product, Finset.card_range, card_oddSet, Nat.mul_comm]
  rw [sum_bracketWordQ_eq, sum_colCountQ _ subset_rfl, ← hcard]
  congr 1
  ext x
  constructor
  · intro hx
    obtain ⟨k, _, hxk⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨j, _, hm, hodd, _⟩ := mem_colSetQ.mp hxk
    exact Finset.mem_product.mpr ⟨mem_oddSet.mpr hodd, Finset.mem_range.mpr hm⟩
  · intro hx
    obtain ⟨hi, hm⟩ := Finset.mem_product.mp hx
    obtain ⟨j, hd, hjL⟩ := exists_lvlDropQ_of_mem hA hi x.2
    obtain ⟨k, hk, _, hkj, hjn⟩ := exists_column hi hd.1 hjL
    exact Finset.mem_biUnion.mpr ⟨k, hk, mem_colSetQ.mpr ⟨j, ⟨hkj, hjn⟩,
      Finset.mem_range.mp hm, mem_oddSet.mp hi, hd⟩⟩

/-- Every column closes at least as many brackets as it has halvings. -/
theorem halvings_le_colCountQ (hq : 3 ≤ q) (hA : AdmissibleQ q s) (k : ℕ) :
    nextOdd s k - k - 1 ≤ colCountQ q s k := by
  unfold colCountQ
  calc nextOdd s k - k - 1 = ∑ _j ∈ Finset.Ioc (k + 1) (nextOdd s k), 1 := by
        rw [Finset.sum_const, Nat.card_Ioc, smul_eq_mul, mul_one]
        omega
    _ ≤ ∑ j ∈ Finset.Ioc (k + 1) (nextOdd s k), closesAtQ q s j := by
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
        have hpos := closesAtQ_pos_of_halving hq hA (by omega) hlt hf
        rw [Nat.sub_add_cancel (by omega)] at hpos
        exact hpos
    _ ≤ ∑ j ∈ Finset.Ioc k (nextOdd s k), closesAtQ q s j := by
        apply Finset.sum_le_sum_of_subset
        exact Finset.Ioc_subset_Ioc_left (by omega)

/-- Shared closes: the surplus of closes over halvings, summed over the columns, is
    (e + 1) order s - |s|, e = `bracketsQ q`. -/
theorem sum_sharedClosesQ (hq : 3 ≤ q) (hA : AdmissibleQ q s) (hord : 1 ≤ order s) :
    ∑ k ∈ oddSet s, (colCountQ q s k - (nextOdd s k - k - 1)) + s.length =
      (bracketsQ q + 1) * order s := by
  have hL : 0 < s.length := List.length_pos_iff.mpr (ne_nil_of_admissibleQ hA)
  have h0 : 0 ∈ oddSet s := by
    rw [mem_oddSet, List.getElem?_eq_getElem hL]
    cases hb : s[0]
    · have hs := eq_single_of_admissibleQ_false hA (by rw [List.getElem?_eq_getElem hL, hb])
      subst hs
      simp [order] at hord
    · rfl
  rw [Finset.sum_tsub_distrib _ fun k _ => halvings_le_colCountQ hq hA k]
  have hc : ∑ k ∈ oddSet s, colCountQ q s k = bracketsQ q * order s := by
    rw [← sum_bracketWordQ_eq]
    exact sum_bracketWordQ hA
  have hw := sum_column_widths h0
  have hsplit : ∑ k ∈ oddSet s, (nextOdd s k - k) =
      ∑ k ∈ oddSet s, (nextOdd s k - k - 1) + (oddSet s).card := by
    rw [Finset.card_eq_sum_ones, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    have := lt_nextOdd (s := s) (List.getElem?_eq_some_iff.mp (mem_oddSet.mp hk)).1
    omega
  have hle : ∑ k ∈ oddSet s, (nextOdd s k - k - 1) ≤ ∑ k ∈ oddSet s, colCountQ q s k :=
    Finset.sum_le_sum fun k _ => halvings_le_colCountQ hq hA k
  rw [card_oddSet] at hsplit
  rw [Nat.add_mul, Nat.one_mul]
  omega

end AcceleratedCollatz
