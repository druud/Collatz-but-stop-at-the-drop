-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TBracketWordTreeQ

/-!
  One-bracket words of the q-family (q ≥ 3): an odd step opens only its first bracket
  (m = 0), the one that closes where the level first falls below the level before the
  step; the one-bracket word counts these closes per column (`bracketWordOneQ`, the counts
  of `colCountOne`, `colCountOne_eq`). A prefix whose brackets close contributes its own
  one-bracket word (`bracketWordOneQ_append`, `bracketWordOneQ_flatten`), and the first
  bracket of the leading 1 of an admissible word closes at its end, in the column of its
  last odd step (`lvlDropQ_zero_zero_length`). So the one-bracket word of an admissible
  1 :: (B1 ++ ... ++ Bk) is 0 followed by the one-bracket words of the blocks, with 1 added
  to the last entry (`bracketWordOneQ_chain`): a filler zero adds nothing, so the
  one-bracket word does not see where the filler zeros stand.
-/

namespace AcceleratedCollatz

variable {q : ℕ}

/-- Closes of first brackets in the column of k. -/
def oneCountQ (q : ℕ) (s : List Bool) (k : ℕ) : ℕ :=
  ((colSetQ q s k).filter (fun x => x.2 = 0)).card

/-- One-bracket word: the closes of first brackets per column, one entry per odd step. -/
def bracketWordOneQ (q : ℕ) (s : List Bool) : List ℕ := (oddPos s).map (oneCountQ q s)

/-- `oneCountQ` counts what `colCountOne` counts. -/
theorem colCountOne_eq (hq : 2 ≤ q) (s : List Bool) (k : ℕ) :
    colCountOne q s k = oneCountQ q s k := by
  have he : 0 < bracketsQ q := by
    unfold bracketsQ
    exact Nat.log_pos (by norm_num) hq
  unfold colCountOne oneCountQ colSetQ
  rw [Finset.filter_biUnion, Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro j _
    refine Finset.card_bij' (fun i _ => (i, 0)) (fun x _ => x.1) ?_ ?_ ?_ ?_
    · intro i hi
      rw [Finset.mem_filter, Finset.mem_range] at hi
      rw [Finset.mem_filter, mem_closeSetQ]
      exact ⟨⟨he, hi.2.1, hi.2.2⟩, rfl⟩
    · intro x hx
      rw [Finset.mem_filter, mem_closeSetQ] at hx
      obtain ⟨⟨_, hodd, hd⟩, h0⟩ := hx
      rw [h0] at hd
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨hd.1, hodd, hd⟩
    · intro i _
      rfl
    · intro x hx
      rw [Finset.mem_filter] at hx
      rw [← hx.2]
  · intro j _ j' _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro x hx hx'
    rw [Finset.mem_filter, mem_closeSetQ] at hx hx'
    exact hne (lvlDropQ_unique hx.1.2.2 hx'.1.2.2)

/-- A prefix whose brackets all close contributes its own one-bracket word. -/
theorem bracketWordOneQ_append (hq0 : 0 < q) {u : List Bool} (v : List Bool)
    (hu : BracketsCloseQ q u) :
    bracketWordOneQ q (u ++ v) = bracketWordOneQ q u ++ bracketWordOneQ q v := by
  unfold bracketWordOneQ
  rw [oddPos_append, List.map_append, List.map_map]
  congr 1
  · apply List.map_congr_left
    intro k hk
    have hkL := (List.getElem?_eq_some_iff.mp (mem_oddPos.mp hk)).1
    unfold oneCountQ
    rw [colSetQ_append_left v hu hkL]
  · apply List.map_congr_left
    intro k hk
    have hkL := (List.getElem?_eq_some_iff.mp (mem_oddPos.mp hk)).1
    unfold oneCountQ
    rw [Function.comp_apply, colSetQ_append_right hq0 v hu hkL, Finset.filter_map,
      Finset.card_map]
    rfl

/-- Admissible blocks contribute their one-bracket words. -/
theorem bracketWordOneQ_flatten (hq0 : 0 < q) (bs : List (List Bool))
    (h : ∀ b ∈ bs, AdmissibleQ q b) :
    bracketWordOneQ q bs.flatten = (bs.map (bracketWordOneQ q)).flatten := by
  induction bs with
  | nil =>
    simp [bracketWordOneQ, oddPos]
  | cons b bs ih =>
    rw [List.flatten_cons, bracketWordOneQ_append hq0 _
      (bracketsCloseQ_of_admissibleQ (h b List.mem_cons_self)),
      ih (fun c hc => h c (List.mem_cons_of_mem b hc)), List.map_cons, List.flatten_cons]

/-- The brackets of the column of 1 + k in true :: r that were not opened by the leading 1
    are those of the column of k in r, shifted by one. -/
theorem colSetQ_true_cons_filter (hq0 : 0 < q) {r : List Bool} {k : ℕ} (hk : k < r.length) :
    (colSetQ q (true :: r) (1 + k)).filter (fun x => ¬x.1 = 0) =
      (colSetQ q r k).map (shiftQ 1) := by
  have hk' : 1 + k < (true :: r).length := by
    rw [List.length_cons]
    omega
  ext x
  rw [Finset.mem_filter, Finset.mem_map]
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

/-- Whether the first bracket of the leading 1 closes in the column of c. -/
def leadOneQ (q : ℕ) (s : List Bool) (c : ℕ) : ℕ :=
  if ((0 : ℕ), (0 : ℕ)) ∈ colSetQ q s c then 1 else 0

/-- First brackets of the leading position closing in the column of c. -/
theorem card_filter_lead (s : List Bool) (c : ℕ) :
    ((colSetQ q s c).filter (fun x => x.2 = 0 ∧ x.1 = 0)).card = leadOneQ q s c := by
  unfold leadOneQ
  split_ifs with h
  · rw [Finset.card_eq_one]
    refine ⟨(0, 0), ?_⟩
    ext x
    rw [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨_, h2, h1⟩
      exact Prod.ext h1 h2
    · rintro rfl
      exact ⟨h, rfl, rfl⟩
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro x hx ⟨h2, h1⟩
    apply h
    have hx' : x = (0, 0) := Prod.ext h1 h2
    rw [← hx']
    exact hx

theorem oneCountQ_split (s : List Bool) (c : ℕ) :
    oneCountQ q s c = leadOneQ q s c +
      (((colSetQ q s c).filter (fun x => ¬x.1 = 0)).filter (fun x => x.2 = 0)).card := by
  unfold oneCountQ
  rw [← card_filter_lead, Finset.filter_filter,
    ← Finset.card_filter_add_card_filter_not (s := (colSetQ q s c).filter (fun x => x.2 = 0))
      (fun x : ℕ × ℕ => x.1 = 0), Finset.filter_filter, Finset.filter_filter]
  congr 1
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro x _
  tauto

/-- Column of 1 + k in true :: r: the first-bracket closes of r in the column of k, and the
    first bracket of the leading 1 if it closes there. -/
theorem oneCountQ_true_cons (hq0 : 0 < q) {r : List Bool} {k : ℕ} (hk : k < r.length) :
    oneCountQ q (true :: r) (1 + k) = leadOneQ q (true :: r) (1 + k) + oneCountQ q r k := by
  rw [oneCountQ_split, colSetQ_true_cons_filter hq0 hk, Finset.filter_map, Finset.card_map]
  rfl

/-- Column of the leading 1: only its own bracket can close there. -/
theorem oneCountQ_true_cons_zero (r : List Bool) :
    oneCountQ q (true :: r) 0 = leadOneQ q (true :: r) 0 := by
  rw [oneCountQ_split]
  have h0 : ((colSetQ q (true :: r) 0).filter (fun x => ¬x.1 = 0)) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro x hx
    have := le_of_mem_colSetQ hx
    omega
  rw [h0, Finset.filter_empty, Finset.card_empty, Nat.add_zero]

/-- The first bracket of the leading 1 of an admissible word closes at its end. -/
theorem lvlDropQ_zero_zero_length {s : List Bool} (hA : AdmissibleQ q s) :
    LvlDropQ q s 0 0 s.length := by
  have hne := ne_nil_of_admissibleQ hA
  have hpos : 0 < s.length := List.length_pos_iff.mpr hne
  refine ⟨hpos, ?_, fun k hk hk0 => ?_⟩
  · rw [lvlQ_zero, pow_zero, mul_one]
    unfold lvlQ
    rw [List.take_length]
    exact hA.lt_one
  · rw [lvlQ_zero, pow_zero, mul_one]
    unfold lvlQ
    exact (hA.prefix_gt k (by omega) hk).le

/-- In an admissible 1 :: r the first bracket of the leading 1 closes in the column of c
    iff no odd step follows c. -/
theorem leadOneQ_eq (hq : 2 ≤ q) {r : List Bool} (hA : AdmissibleQ q (true :: r)) {c : ℕ}
    (hc : c < (true :: r).length) :
    leadOneQ q (true :: r) c = if nextOdd (true :: r) c = (true :: r).length then 1 else 0 := by
  have hL := lvlDropQ_zero_zero_length hA
  have he : 0 < bracketsQ q := by
    unfold bracketsQ
    exact Nat.log_pos (by norm_num) hq
  have hiff : ((0 : ℕ), (0 : ℕ)) ∈ colSetQ q (true :: r) c ↔
      nextOdd (true :: r) c = (true :: r).length := by
    rw [mem_colSetQ]
    constructor
    · rintro ⟨j, ⟨_, hjn⟩, _, _, hd⟩
      have hjj := lvlDropQ_unique hd hL
      subst hjj
      exact le_antisymm (nextOdd_le _ c) hjn
    · intro hn
      exact ⟨(true :: r).length, ⟨hc, hn.ge⟩, he, rfl, hL⟩
  unfold leadOneQ
  simp only [hiff]

/-- Only the last odd position has no odd step after it. -/
theorem map_nextOdd_eq_length (s : List Bool) (hne : oddPos s ≠ []) :
    (oddPos s).map (fun c => if nextOdd s c = s.length then 1 else 0) =
      List.replicate ((oddPos s).length - 1) 0 ++ [1] := by
  have hpw := List.pairwise_iff_getElem.mp (pairwise_oddPos s)
  have hlen : 0 < (oddPos s).length := List.length_pos_iff.mpr hne
  apply List.ext_getElem
  · rw [List.length_map, List.length_append, List.length_replicate, List.length_singleton]
    omega
  · intro n h1 h2
    rw [List.length_map] at h1
    rw [List.getElem_map]
    have hcL : (oddPos s)[n] < s.length :=
      (List.getElem?_eq_some_iff.mp (mem_oddPos.mp (List.getElem_mem h1))).1
    rcases Nat.lt_or_ge n ((oddPos s).length - 1) with hn | hn
    · have hlt := hpw n (n + 1) h1 (by omega) (by omega)
      have hmem : (oddPos s)[n + 1] ∈ oddSet s :=
        mem_oddSet.mpr (mem_oddPos.mp (List.getElem_mem _))
      have hle := nextOdd_le_of_mem hmem hlt
      have hnL : (oddPos s)[n + 1] < s.length :=
        (List.getElem?_eq_some_iff.mp (mem_oddPos.mp (List.getElem_mem _))).1
      have hne' : ¬nextOdd s (oddPos s)[n] = s.length := by
        omega
      have hnr : n < (List.replicate ((oddPos s).length - 1) 0).length := by
        rw [List.length_replicate]
        exact hn
      simp only [hne', ↓reduceIte]
      rw [List.getElem_append_left hnr, List.getElem_replicate]
    · have hn' : n = (oddPos s).length - 1 := by
        omega
      have hnone : nextOdd s (oddPos s)[n] = s.length := by
        rw [nextOdd_eq_length_iff hcL]
        intro m hm hodd
        obtain ⟨i, hi, him⟩ := List.mem_iff_getElem.mp (mem_oddPos.mpr hodd)
        rcases Nat.lt_or_ge n i with hni | hni
        · omega
        · rcases Nat.lt_or_ge i n with hin | hin
          · have := hpw i n hi h1 hin
            omega
          · have hin' : i = n := by
              omega
            subst hin'
            omega
      have hnr : (List.replicate ((oddPos s).length - 1) 0).length ≤ n := by
        rw [List.length_replicate]
        omega
      simp only [hnone, ↓reduceIte]
      rw [List.getElem_append_right hnr]
      simp [hn']

/-- Adding 1 at the last of the positions of l. -/
theorem zipWith_replicate_one : ∀ l : List ℕ, l ≠ [] →
    List.zipWith (· + ·) l (List.replicate (l.length - 1) 0 ++ [1]) = addLast 1 l
  | [], h => absurd rfl h
  | [a], _ => by
    simp [addLast]
  | a :: b :: t, _ => by
    have ih := zipWith_replicate_one (b :: t) (List.cons_ne_nil _ _)
    have hr : List.replicate ((a :: b :: t).length - 1) 0 =
        0 :: List.replicate ((b :: t).length - 1) 0 := by
      simp [List.replicate_succ]
    rw [hr, List.cons_append, List.zipWith_cons_cons, ih, addLast_cons 1 a (List.cons_ne_nil b t),
      Nat.add_zero]

/-- The one-bracket word of an admissible 1 :: (B1 ++ ... ++ Bk): 0 and the one-bracket words
    of the blocks, with 1 added to the last entry. -/
theorem bracketWordOneQ_chain (hq : 3 ≤ q) {bs : List (List Bool)}
    (hbs : ∀ b ∈ bs, AdmissibleQ q b) (hA : AdmissibleQ q (true :: bs.flatten)) :
    bracketWordOneQ q (true :: bs.flatten) =
      addLast 1 (0 :: (bs.map (bracketWordOneQ q)).flatten) := by
  have hq0 : 0 < q := by
    omega
  have h1 : bracketWordOneQ q (true :: bs.flatten) =
      List.zipWith (· + ·) (0 :: bracketWordOneQ q bs.flatten)
        ((oddPos (true :: bs.flatten)).map (leadOneQ q (true :: bs.flatten))) := by
    unfold bracketWordOneQ
    rw [oddPos_true_cons, List.map_cons, List.map_cons, oneCountQ_true_cons_zero, List.map_map,
      List.map_map, List.zipWith_cons_cons, Nat.zero_add, ← map_add_eq_zipWith]
    congr 1
    apply List.map_congr_left
    intro k hk
    have hkL := (List.getElem?_eq_some_iff.mp (mem_oddPos.mp hk)).1
    rw [Function.comp_apply, oneCountQ_true_cons hq0 hkL, Nat.add_comm]
    rfl
  have hlead : (oddPos (true :: bs.flatten)).map (leadOneQ q (true :: bs.flatten)) =
      List.replicate ((oddPos (true :: bs.flatten)).length - 1) 0 ++ [1] := by
    have hne : oddPos (true :: bs.flatten) ≠ [] := by
      rw [oddPos_true_cons]
      exact List.cons_ne_nil _ _
    rw [← map_nextOdd_eq_length _ hne]
    apply List.map_congr_left
    intro c hc
    exact leadOneQ_eq (by omega) hA
      (List.getElem?_eq_some_iff.mp (mem_oddPos.mp hc)).1
  have hlen : (0 :: bracketWordOneQ q bs.flatten).length - 1 =
      (oddPos (true :: bs.flatten)).length - 1 := by
    rw [List.length_cons, bracketWordOneQ, List.length_map, oddPos_true_cons, List.length_cons,
      List.length_map]
  rw [h1, hlead, ← hlen, zipWith_replicate_one _ (List.cons_ne_nil _ _),
    bracketWordOneQ_flatten hq0 bs hbs]

-- q = 5: 10100 = 1 | 0 | 100 and 11000 = 1 | 100 | 0 have the same one-bracket word.
set_option linter.hashCommand false in
#guard bracketWordOneQ 5 [true, false, true, false, false] = [0, 2] &&
  bracketWordOneQ 5 [true, true, false, false, false] = [0, 2]

end AcceleratedCollatz
