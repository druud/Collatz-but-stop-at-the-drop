-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TSplitGrammar

/-!
  Chained form of an admissible PV of Order ≥ 1 (q = 3): a leading 1, a chain of
  admissible PVs of Order ≥ 1, and a tail t ∈ {[], [0]}. The tail is [0]
  iff the level after the chain is > 1 (`exists_chain`). Conversely a chain
  whose level stays > 1 at inner boundaries is completed by t = [] if its
  final level is < 1, and by t = [0] otherwise (`admissible_chain`). A single
  0 suffices: blocks of Order ≥ 1 have PV-factor in (1/2, 1), so the level
  after the chain is < 3/2.
-/

namespace AcceleratedCollatz

variable (bs : List (List Bool))

/-- Chain condition: admissible PVs of Order ≥ 1. -/
structure IsChainBlock (b : List Bool) : Prop where
  /-- The block is admissible. -/
  adm : Admissible b
  /-- The block has Order ≥ 1. -/
  order_pos : 1 ≤ order b

/-- Products are positive. -/
theorem seqProduct_pos (s : List Bool) : 0 < seqProduct s := by
  rw [← seqProductQ_three]
  exact seqProductQ_pos (by norm_num) s

/-- Product of [0] is 1/2. -/
theorem seqProduct_singleton_false : seqProduct [false] = 1 / 2 := by
  norm_num [seqProduct, factor]

/-- [0] is admissible (Order 0). -/
theorem admissible_singleton_false : Admissible [false] :=
  (admissibleQ_three _).mp (admissibleQ_singleton_false 3)

/-- Chain blocks concatenated have product ≤ 1. -/
theorem seqProduct_flatten_le_one (h : ∀ b ∈ bs, IsChainBlock b) :
    seqProduct bs.flatten ≤ 1 := by
  induction bs with
  | nil =>
    simp [seqProduct]
  | cons b t ih =>
    rw [List.flatten_cons, seqProduct_append]
    have hb := (h b List.mem_cons_self).adm.lt_one
    have ht := ih (fun c hc => h c (List.mem_cons_of_mem b hc))
    have hbpos := seqProduct_pos b
    have htpos := seqProduct_pos t.flatten
    nlinarith

/-- Chain blocks concatenated, at least one, have product < 1. -/
theorem seqProduct_flatten_lt_one (h : ∀ b ∈ bs, IsChainBlock b) (hne : bs ≠ []) :
    seqProduct bs.flatten < 1 := by
  obtain ⟨b, t, rfl⟩ := List.exists_cons_of_ne_nil hne
  rw [List.flatten_cons, seqProduct_append]
  have hb := (h b List.mem_cons_self).adm.lt_one
  have ht := seqProduct_flatten_le_one t (fun c hc => h c (List.mem_cons_of_mem b hc))
  have hbpos := seqProduct_pos b
  have htpos := seqProduct_pos t.flatten
  nlinarith

/-- The level after 1 :: chain blocks: 3/2 times the product of the blocks. -/
theorem seqProduct_true_cons_flatten :
    seqProduct (true :: bs.flatten) = 3 / 2 * seqProduct bs.flatten := by
  have h1 := seqProduct_append [true] bs.flatten
  simp only [List.singleton_append] at h1
  rw [h1]
  norm_num [seqProduct, factor]

/-- The level after 1 :: chain blocks is at most 3/2 (equality for the empty chain). -/
theorem seqProduct_chain_le (h : ∀ b ∈ bs, IsChainBlock b) :
    seqProduct (true :: bs.flatten) ≤ 3 / 2 := by
  rw [seqProduct_true_cons_flatten]
  have hle := seqProduct_flatten_le_one bs h
  linarith

/-- The level after 1 :: chain blocks is < 3/2 when there is at least one block. -/
theorem seqProduct_chain_lt (h : ∀ b ∈ bs, IsChainBlock b) (hne : bs ≠ []) :
    seqProduct (true :: bs.flatten) < 3 / 2 := by
  rw [seqProduct_true_cons_flatten]
  have hlt := seqProduct_flatten_lt_one bs h hne
  linarith

/-- A nonempty PV-factor is never 1. -/
theorem seqProduct_ne_one (s : List Bool) (hne : s ≠ []) : seqProduct s ≠ 1 := by
  rw [← seqProductQ_three]
  exact seqProductQ_ne_one (by decide) le_rfl hne

/-- Assembly: a chain whose level stays > 1 at inner boundaries is completed by no
    tail if its final level is < 1, and by a single 0 otherwise. -/
theorem admissible_chain (hbs : ∀ b ∈ bs, IsChainBlock b)
    (hlev : ∀ i, 1 ≤ i → i < bs.length → 1 < seqProduct (true :: (bs.take i).flatten)) :
    (seqProduct (true :: bs.flatten) < 1 → Admissible (true :: bs.flatten)) ∧
      (1 < seqProduct (true :: bs.flatten) → Admissible (true :: (bs.flatten ++ [false]))) := by
  have hbsA : ∀ b ∈ bs, Admissible b := fun b hb => (hbs b hb).adm
  constructor
  · intro hlt
    exact (admissible_split_iff bs hbsA).mpr ⟨hlev, hlt⟩
  · intro hgt
    have hA' : ∀ b ∈ bs ++ [[false]], Admissible b := by
      intro b hb
      rcases List.mem_append.mp hb with hb' | hb'
      · exact hbsA b hb'
      · rw [List.mem_singleton] at hb'
        rw [hb']
        exact admissible_singleton_false
    have hflat : (bs ++ [[false]]).flatten = bs.flatten ++ [false] := by
      simp
    rw [← hflat]
    apply (admissible_split_iff (bs ++ [[false]]) hA').mpr
    constructor
    · intro i hi hil
      rw [List.length_append, List.length_singleton] at hil
      rw [List.take_append_of_le_length (by omega)]
      rcases Nat.lt_or_ge i bs.length with hlt | hge
      · exact hlev i hi hlt
      · have hi' : i = bs.length := by omega
        rw [hi', List.take_length]
        exact hgt
    · rw [hflat]
      have h2 : seqProduct (true :: bs.flatten) < 2 := by
        have h32 := seqProduct_chain_le bs hbs
        linarith
      have happ : true :: (bs.flatten ++ [false]) = (true :: bs.flatten) ++ [false] := by
        simp
      rw [happ, seqProduct_append, seqProduct_singleton_false]
      linarith

/-- Parse: an admissible PV of Order ≥ 1 is a leading 1, a chain, and a tail t ∈ {[], [0]};
    t = [0] iff the level after the chain is > 1. -/
theorem exists_chain (s : List Bool) (hA : Admissible s) (hord : 1 ≤ order s) :
    ∃ (bs : List (List Bool)) (t : List Bool),
      s = true :: (bs.flatten ++ t) ∧ (∀ b ∈ bs, IsChainBlock b) ∧
      (t = [] ∨ t = [false]) ∧ (t = [false] ↔ 1 < seqProduct (true :: bs.flatten)) := by
  obtain ⟨bs0, hsplit⟩ := exists_split s hA hord
  rcases List.eq_nil_or_concat bs0 with h0 | ⟨pre, b, rfl⟩
  · have hs : s = [true] := by
      rw [hsplit.1, h0]
      rfl
    have hP := hA.lt_one
    rw [hs] at hP
    norm_num [seqProduct, factor] at hP
  · rw [List.concat_eq_append] at hsplit
    have hpre : ∀ c ∈ pre, IsChainBlock c := by
      intro c hc
      refine ⟨hsplit.2 c (by simp [hc]), ?_⟩
      obtain ⟨l1, l2, rfl⟩ := List.append_of_mem hc
      apply zero_block_last s hA l1 (l2 ++ [b]) c
      · have h := hsplit
        simp only [List.append_assoc, List.cons_append] at h
        exact h
      · simp
    have hbA : Admissible b := hsplit.2 b (by simp)
    have hs : s = true :: (pre.flatten ++ b) := by
      rw [hsplit.1]
      simp
    rcases Nat.eq_zero_or_pos (order b) with hb0 | hbpos
    · have hbf : b = [false] := admissible_order_zero b hbA hb0
      refine ⟨pre, [false], by rw [hs, hbf], hpre, Or.inr rfl, ?_⟩
      simp only [true_iff]
      have hlen : (true :: pre.flatten).length < s.length := by
        rw [hs, hbf]
        simp
      have h := hA.prefix_gt (true :: pre.flatten).length (by simp) hlen
      rw [hs, hbf, ← List.cons_append, List.take_left] at h
      exact h
    · have hs' : s = true :: ((pre ++ [b]).flatten ++ []) := by
        rw [hs]
        simp
      refine ⟨pre ++ [b], [], hs', ?_, Or.inl rfl, ?_⟩
      · intro c hc
        rcases List.mem_append.mp hc with hc' | hc'
        · exact hpre c hc'
        · rw [List.mem_singleton] at hc'
          rw [hc']
          exact ⟨hbA, hbpos⟩
      · have hP := hA.lt_one
        have hflat : true :: (pre ++ [b]).flatten = s := by
          rw [hs]
          simp
        rw [hflat]
        constructor
        · intro h
          simp at h
        · intro h
          linarith

/-- Length of concatenated chain blocks: the sum of p2 of their Orders. -/
theorem length_flatten_chain (hbs : ∀ b ∈ bs, IsChainBlock b) :
    bs.flatten.length = (bs.map (fun b => p2_of (order b))).sum := by
  induction bs with
  | nil =>
    simp
  | cons b t ih =>
    rw [List.flatten_cons, List.length_append, List.map_cons, List.sum_cons,
      admissible_length b (hbs b List.mem_cons_self).adm,
      ih (fun c hc => hbs c (List.mem_cons_of_mem b hc))]

/-- p2 form of the tail: t = [0] iff p2(1 + Σ o_i) = 2 + Σ p2(o_i), o_i the chain Orders. -/
theorem tail_eq_zero_iff (t : List Bool)
    (hbs : ∀ b ∈ bs, IsChainBlock b) (ht : t = [] ∨ t = [false])
    (hA : Admissible (true :: (bs.flatten ++ t))) :
    t = [false] ↔
      p2_of (1 + (bs.map order).sum) = 2 + (bs.map (fun b => p2_of (order b))).sum := by
  have hlen := admissible_length _ hA
  have hord : order (true :: (bs.flatten ++ t)) = 1 + (bs.map order).sum := by
    rcases ht with rfl | rfl
    · rw [order_cons, List.append_nil, order_flatten]
      simp only [↓reduceIte]
      omega
    · rw [order_cons, order_append, order_flatten]
      simp [order]
      omega
  rw [hord, List.length_cons, List.length_append, length_flatten_chain bs hbs] at hlen
  rw [← hlen]
  rcases ht with rfl | rfl
  · simp only [List.length_nil, reduceCtorEq, false_iff]
    omega
  · simp only [List.length_singleton, true_iff]
    omega

end AcceleratedCollatz
