-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TBracketDecodeQ

/-!
  The bracket word of a valid tree of the q-family (odd q ≥ 3) from the Orders of its nodes.
  Bracket m of a node closes at the end of its first child after which the level is below
  2^m (`lvlDropQ_zero_cut`), there `OpenAtQ` fails (`two_pow_le_lvlQ_cut_iff`); the cut lies
  in the column counted by the Orders before it (`colQ_eq_sum_take`), the column of odd
  position p being the positions j with order (s.take j) one more than the index of p
  (`column_iff_order_take`). So the closes of the leading brackets per column are
  `leadQ` (`map_leadCountQ_eq_leadQ`), the bracket word of a valid tree is `encQ`
  (`bracketWordQ_word_eq_encQ`), and the decoder reads every admissible word of Order at
  least 1 back from its bracket word, filler zeros included
  (`decodeQ_bracketWordQ`).
-/

namespace AcceleratedCollatz

variable {q : ℕ}

/-! ### Odd positions -/

theorem oddPos_false_cons (r : List Bool) :
    oddPos (false :: r) = (oddPos r).map (1 + ·) := by
  have h := oddPos_append [false] r
  have h1 : oddPos [false] = [] := by
    simp [oddPos]
  rw [h1, List.nil_append, List.singleton_append] at h
  exact h

/-- One odd position per odd step. -/
theorem length_oddPos : ∀ s : List Bool, (oddPos s).length = order s
  | [] => by
    simp [oddPos, order]
  | true :: r => by
    rw [oddPos_true_cons, List.length_cons, List.length_map, length_oddPos r, order_cons]
    simp
  | false :: r => by
    rw [oddPos_false_cons, List.length_map, length_oddPos r, order_cons]
    simp

theorem pairwise_oddPos (s : List Bool) : (oddPos s).Pairwise (· < ·) :=
  List.Pairwise.filter _ List.pairwise_lt_range

theorem lt_of_mem_oddPos_take {s : List Bool} {j r : ℕ} (hr : r ∈ oddPos (s.take j)) : r < j := by
  have h := (List.getElem?_eq_some_iff.mp (mem_oddPos.mp hr)).1
  rw [List.length_take] at h
  omega

/-- Position j lies in the column of the n-th odd position iff n + 1 odd steps come before
    it. -/
theorem column_iff_order_take {s : List Bool} {n j : ℕ} (hn : n < (oddPos s).length)
    (hj : j ≤ s.length) :
    ((oddPos s)[n] < j ∧ ∀ r, (oddPos s)[n] < r → r < j → s[r]? ≠ some true) ↔
      order (s.take j) = n + 1 := by
  have hsplit := oddPos_append (s.take j) (s.drop j)
  rw [List.take_append_drop] at hsplit
  have hlenA := length_oddPos (s.take j)
  have hpw := List.pairwise_iff_getElem.mp (pairwise_oddPos s)
  have hlen : (oddPos s).length = (oddPos (s.take j)).length +
      ((oddPos (s.drop j)).map ((s.take j).length + ·)).length := by
    rw [hsplit, List.length_append]
  have hA : ∀ i (hi : i < (oddPos (s.take j)).length),
      (oddPos s)[i]'(by omega) = (oddPos (s.take j))[i] := by
    intro i hi
    simp only [hsplit]
    exact List.getElem_append_left hi
  have hAlt : ∀ i (hi : i < (oddPos (s.take j)).length), (oddPos (s.take j))[i] < j :=
    fun i hi => lt_of_mem_oddPos_take (List.getElem_mem hi)
  have hB : ∀ i (hi : i < (oddPos s).length), (oddPos (s.take j)).length ≤ i →
      j ≤ (oddPos s)[i] := by
    intro i hi hle
    have hmem : (oddPos s)[i] ∈ (oddPos (s.drop j)).map ((s.take j).length + ·) := by
      have hi2 : i < ((oddPos (s.take j)) ++
          (oddPos (s.drop j)).map ((s.take j).length + ·)).length := by
        simpa only [← hsplit] using hi
      have hg : (oddPos s)[i] = ((oddPos (s.take j)) ++
          (oddPos (s.drop j)).map ((s.take j).length + ·))[i]'hi2 := by
        simp only [hsplit]
      rw [hg, List.getElem_append_right hle]
      exact List.getElem_mem _
    obtain ⟨r, _, hr⟩ := List.mem_map.mp hmem
    rw [List.length_take, Nat.min_eq_left hj] at hr
    omega
  constructor
  · rintro ⟨hpj, hno⟩
    have hna : n < (oddPos (s.take j)).length := by
      by_contra hcon
      have := hB n hn (by omega)
      omega
    have han : (oddPos (s.take j)).length ≤ n + 1 := by
      by_contra hcon
      have hi1 : n + 1 < (oddPos (s.take j)).length := by
        omega
      have hlt := hpw n (n + 1) hn (by omega) (by omega)
      have hrA := hA (n + 1) hi1
      have hrj := hAlt (n + 1) hi1
      have hodd : s[(oddPos s)[n + 1]'(by omega)]? =
          some true :=
        mem_oddPos.mp (List.getElem_mem _)
      rw [hrA] at hlt hodd
      exact hno _ hlt hrj hodd
    omega
  · intro hord
    have hna : n < (oddPos (s.take j)).length := by
      omega
    have hpj : (oddPos s)[n] < j := by
      rw [hA n hna]
      exact hAlt n hna
    refine ⟨hpj, fun r hpr hrj hr => ?_⟩
    have hrmem : r ∈ oddPos (s.take j) := by
      apply mem_oddPos.mpr
      rw [List.getElem?_take]
      simp only [hrj, ↓reduceIte]
      exact hr
    obtain ⟨i, hi, hir⟩ := List.mem_iff_getElem.mp hrmem
    have hin : i ≤ n := by
      omega
    rw [hA n hna] at hpr
    rcases Nat.lt_or_ge i n with hlt | hge
    · have h1 := hpw i n (by omega) hn hlt
      rw [hA i hi, hA n hna, hir] at h1
      omega
    · have hieq : i = n := by
        omega
      subst hieq
      omega

/-! ### Levels at the cuts -/

theorem two_pow_le_seqProductQ_iff (q m : ℕ) (s : List Bool) :
    (2 : ℚ) ^ m ≤ seqProductQ q s ↔ 2 ^ (m + s.length) ≤ q ^ order s := by
  have h := seqProductQ_mul_pow q s
  have hpos : (0 : ℚ) < 2 ^ s.length := by
    positivity
  constructor
  · intro h1
    have h2 := mul_le_mul_of_nonneg_right h1 hpos.le
    rw [h, ← pow_add] at h2
    exact_mod_cast h2
  · intro h1
    have h2 : (2 : ℚ) ^ (m + s.length) ≤ (q : ℚ) ^ order s := by
      exact_mod_cast h1
    rw [pow_add, ← h] at h2
    exact le_of_mul_le_mul_right h2 hpos

theorem take_cut (bs : List (List Bool)) (i : ℕ) :
    (true :: bs.flatten).take (1 + (bs.take i).flatten.length) = true :: (bs.take i).flatten := by
  have hfl : bs.flatten = (bs.take i).flatten ++ (bs.drop i).flatten := by
    rw [← List.flatten_append, List.take_append_drop]
  rw [Nat.add_comm, List.take_succ_cons, hfl, List.take_left' rfl]

/-- The level of 1 :: (B1 ++ ... ++ Bi) is at least 2^m iff bracket m is open after the
    Orders of B1 .. Bi. -/
theorem two_pow_le_lvlQ_cut_iff (hq : 3 ≤ q) {bs : List (List Bool)}
    (hbs : ∀ b ∈ bs, AdmissibleQ q b) (i m : ℕ) :
    2 ^ m ≤ lvlQ q (true :: bs.flatten) (1 + (bs.take i).flatten.length) ↔
      OpenAtQ q ((bs.map order).take i) m := by
  have htake : ∀ b ∈ bs.take i, AdmissibleQ q b := fun b hb => hbs b (List.mem_of_mem_take hb)
  unfold lvlQ
  rw [take_cut, two_pow_le_seqProductQ_iff, List.length_cons, length_flatten_admQ hq _ htake,
    order_cons_flatten]
  unfold OpenAtQ
  rw [← List.map_take]
  constructor
  · intro h
    convert h using 2
    omega
  · intro h
    convert h using 2
    omega

theorem order_take_cut (bs : List (List Bool)) (i : ℕ) :
    order ((true :: bs.flatten).take (1 + (bs.take i).flatten.length)) =
      1 + ((bs.map order).take i).sum := by
  rw [take_cut, order_cons_flatten, List.map_take]

/-- With bracket m open before child i and closed after it, its column is the sum of the
    first i Orders. -/
theorem colQ_eq_sum_take (hq : 3 ≤ q) {m : ℕ} : ∀ (os pre : List ℕ) (i : ℕ), i ≤ os.length →
    (∀ i' < i, OpenAtQ q (pre ++ os.take i') m) → ¬OpenAtQ q (pre ++ os.take i) m →
      colQ q pre os m = (os.take i).sum
  | [], _, i, _, _, _ => by
    simp [colQ]
  | o :: os, pre, 0, _, _, hnot => by
    rw [List.take_zero, List.append_nil] at hnot
    rw [colQ_of_not_openAtQ hq _ _ hnot, List.take_zero, List.sum_nil]
  | o :: os, pre, i + 1, hi, hopen, hnot => by
    have h0 := hopen 0 (by omega)
    rw [List.take_zero, List.append_nil] at h0
    have hi' : i ≤ os.length := by
      simp only [List.length_cons] at hi
      omega
    have hrec := colQ_eq_sum_take hq os (pre ++ [o]) i hi'
      (fun i' hi' => by
        have h := hopen (i' + 1) (by omega)
        rw [List.take_succ_cons, ← List.singleton_append, ← List.append_assoc] at h
        exact h)
      (by
        rw [List.take_succ_cons, ← List.singleton_append, ← List.append_assoc] at hnot
        exact hnot)
    rw [colQ, hrec, List.take_succ_cons, List.sum_cons]
    simp only [h0, ↓reduceIte]

theorem openAtQ_nil_of_lt {m : ℕ} (hq : 3 ≤ q) (hm : m < bracketsQ q) : OpenAtQ q [] m := by
  unfold OpenAtQ
  simp only [List.map_nil, List.sum_nil, Nat.add_zero, pow_one]
  have h := Nat.pow_log_le_self 2 (show q ≠ 0 by omega)
  have h2 : 2 ^ (m + 1) ≤ 2 ^ Nat.log 2 q := Nat.pow_le_pow_right (by norm_num) hm
  unfold bracketsQ at hm
  omega

/-- The bracket m of the leading 1 closes in the column of the n-th odd position iff its
    column by Orders is n. -/
theorem lead_close_iff (hq : 3 ≤ q) {bs : List (List Bool)} (hbs : ∀ b ∈ bs, AdmissibleQ q b)
    (hA : AdmissibleQ q (true :: bs.flatten)) {n m : ℕ}
    (hn : n < (oddPos (true :: bs.flatten)).length) (hm : m < bracketsQ q) :
    (∃ j, LvlDropQ q (true :: bs.flatten) 0 m j ∧ (oddPos (true :: bs.flatten))[n] < j ∧
        ∀ r, (oddPos (true :: bs.flatten))[n] < r → r < j →
          (true :: bs.flatten)[r]? ≠ some true) ↔
      OpenAtQ q [] m ∧ ¬OpenAtQ q ([] ++ bs.map order) m ∧ colQ q [] (bs.map order) m = n := by
  have h0 : (0 : ℕ) ∈ oddSet (true :: bs.flatten) := by
    rw [mem_oddSet]
    rfl
  obtain ⟨j, hj, hjL⟩ := exists_lvlDropQ_of_mem hA h0 m
  obtain ⟨i, hi, hji, hlt, hmin⟩ := lvlDropQ_zero_cut hq hbs hj
  have hnot : ¬OpenAtQ q ((bs.map order).take i) m := by
    rw [← two_pow_le_lvlQ_cut_iff hq hbs, ← hji]
    exact not_le.mpr hlt
  have hopen : ∀ i' < i, OpenAtQ q ([] ++ (bs.map order).take i') m := by
    intro i' hi'
    rw [List.nil_append, ← two_pow_le_lvlQ_cut_iff hq hbs]
    exact hmin i' hi'
  have hiL : i ≤ (bs.map order).length := by
    rw [List.length_map]
    exact hi
  have hnot' : ¬OpenAtQ q ([] ++ (bs.map order).take i) m := by
    rw [List.nil_append]
    exact hnot
  have hcol := colQ_eq_sum_take hq (bs.map order) [] i hiL hopen hnot'
  have hend : ¬OpenAtQ q ([] ++ bs.map order) m := by
    rw [List.nil_append, ← List.take_append_drop i (bs.map order)]
    exact not_openAtQ_append hq hnot _
  have hord : order ((true :: bs.flatten).take j) = 1 + ((bs.map order).take i).sum := by
    rw [hji, order_take_cut]
  constructor
  · rintro ⟨j', hj', hcolj⟩
    have hjj := lvlDropQ_unique hj hj'
    subst hjj
    have hc := (column_iff_order_take hn hjL).mp hcolj
    exact ⟨openAtQ_nil_of_lt hq hm, hend, by omega⟩
  · rintro ⟨_, _, hc⟩
    exact ⟨j, hj, (column_iff_order_take hn hjL).mpr (by omega)⟩

/-- Per column, the closes of the leading brackets of an admissible 1 :: (B1 ++ ... ++ Bk)
    are `leadQ` of the Orders of the blocks. -/
theorem map_leadCountQ_eq_leadQ (hq : 3 ≤ q) {bs : List (List Bool)}
    (hbs : ∀ b ∈ bs, AdmissibleQ q b) (hA : AdmissibleQ q (true :: bs.flatten)) :
    (oddPos (true :: bs.flatten)).map (leadCountQ q (true :: bs.flatten)) =
      leadQ q [] (bs.map order) := by
  apply List.ext_getElem
  · rw [List.length_map, length_oddPos, order_cons_flatten, leadQ, List.length_map,
      List.length_range]
  · intro n h1 _
    rw [List.length_map] at h1
    simp only [leadQ, List.getElem_map, List.getElem_range]
    have hpL : (oddPos (true :: bs.flatten))[n] < (true :: bs.flatten).length :=
      (List.getElem?_eq_some_iff.mp (mem_oddPos.mp (List.getElem_mem h1))).1
    unfold leadCountQ leadAtQ
    refine Finset.card_bij' (fun x _ => x.2) (fun m _ => ((0 : ℕ), m)) ?_ ?_ ?_ ?_
    · intro x hx
      rw [Finset.mem_filter] at hx
      obtain ⟨hxc, hx0⟩ := hx
      obtain ⟨hm, _, j, hj, hpj, hno⟩ := (mem_colSetQ_iff hpL).mp hxc
      rw [Finset.mem_filter, Finset.mem_range]
      rw [hx0] at hj
      exact ⟨hm, (lead_close_iff hq hbs hA h1 hm).mp ⟨j, hj, hpj, hno⟩⟩
    · intro m hm
      rw [Finset.mem_filter, Finset.mem_range] at hm
      obtain ⟨j, hj, hpj, hno⟩ := (lead_close_iff hq hbs hA h1 hm.1).mpr hm.2
      rw [Finset.mem_filter, mem_colSetQ_iff hpL]
      exact ⟨⟨hm.1, rfl, j, hj, hpj, hno⟩, rfl⟩
    · intro x hx
      rw [Finset.mem_filter] at hx
      rw [← hx.2]
    · intro m _
      rfl

/-! ### The bracket word of a tree -/

/-- The bracket word of the word of a valid tree is its encoding by Orders. -/
theorem bracketWordQ_word_eq_encQ (hodd : Odd q) (hq : 3 ≤ q) {t : ChainTreeQ}
    (h : ValidTreeQ q t) : bracketWordQ q t.word = encQ q t := by
  induction h with
  | leaf =>
    rw [ChainTreeQ.word_leaf]
    simp [bracketWordQ, oddPos, encQ]
  | node ts hts _ _ ih =>
    have hbs : ∀ b ∈ ts.map ChainTreeQ.word, AdmissibleQ q b := by
      intro b hb
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hb
      exact admissibleQ_word hodd hq (hts u hu)
    have hA : AdmissibleQ q (true :: (ts.map ChainTreeQ.word).flatten) := by
      rw [← ChainTreeQ.word_node]
      exact admissibleQ_word hodd hq (.node ts hts ‹_› ‹_›)
    have hmap : (ts.map ChainTreeQ.word).map (bracketWordQ q) = ts.map (encQ q) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro u hu
      exact ih u hu
    have hlead := map_leadCountQ_eq_leadQ hq hbs hA
    rw [oddPos_true_cons, List.map_cons, List.map_map] at hlead
    have hords : ChainTreeQ.orders ts = (ts.map ChainTreeQ.word).map order := rfl
    rw [ChainTreeQ.word_node, ← chainWordQ, bracketWordQ_chainWordQ hq hbs, hmap, encQ_node_eq hq,
      hords, ← hlead, List.zipWith_cons_cons, Nat.zero_add]
    rfl

/-- The decoder reads an admissible word of Order at least 1 back from its bracket word, as
    its tree with the filler zeros marked. -/
theorem decodeQ_bracketWordQ (hodd : Odd q) (hq : 3 ≤ q) {s : List Bool} (hA : AdmissibleQ q s)
    (hn : 1 ≤ order s) : decodeQ q (bracketWordQ q s) = parseTreeQ q s := by
  obtain ⟨t, ht, rfl⟩ := exists_validTreeQ_word hodd hq _ s rfl hA
  have hnl : t ≠ .leaf := by
    rintro rfl
    rw [order_word_leaf] at hn
    omega
  rw [bracketWordQ_word_eq_encQ hodd hq ht, decodeQ_encQ hodd hq ht hnl,
    (parseTreeQ_eq_some_iff hq _ t).mpr ⟨ht, rfl⟩]

-- q = 5: the bracket word of 11000 reads back as node [node [leaf, leaf], leaf].
set_option linter.hashCommand false in
#guard (match decodeQ 5 (bracketWordQ 5 [true, true, false, false, false]) with
  | some (.node [.node [.leaf, .leaf], .leaf]) => true
  | _ => false)

end AcceleratedCollatz
