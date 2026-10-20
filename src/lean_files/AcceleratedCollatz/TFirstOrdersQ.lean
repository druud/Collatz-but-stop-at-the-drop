-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TFirstChainQ
import AcceleratedCollatz.TRecordGapQ

/-!
  The Orders of the blocks of a first word in the q-family (odd q ≥ 3). In the chain of
  the first word of Order n ≥ 1 every block but the last has an upper record Order
  (`upperRecordQ_order_of_firstWordQ`): the Orders read before two neighbouring blocks
  are equal or are neighbouring lower record Orders (`firstWordQ_chain`), and the gap of
  two neighbouring lower record Orders is an upper record Order
  (`upperRecordQ_sub_of_lowerRecordQ`). The last block is [0] when n is a lower record
  Order (`firstWordQ_blocks`); otherwise its Order is n minus the last lower record
  Order below n, which need not be a record Order.
-/

namespace AcceleratedCollatz

variable {q : ℕ}

/-- Order 0 is an upper record Order. -/
theorem upperRecordQ_zero (q : ℕ) : UpperRecordQ q 0 := by
  intro a ha1 ha
  omega

/-- The sum of the first j entries of a list of natural numbers grows with j. -/
theorem sum_take_le_sum_take (l : List ℕ) {j k : ℕ} (h : j ≤ k) :
    (l.take j).sum ≤ (l.take k).sum := by
  induction l generalizing j k with
  | nil =>
    rw [List.take_nil, List.take_nil]
  | cons x l ih =>
    cases j with
    | zero =>
      rw [List.take_zero, List.sum_nil]
      exact Nat.zero_le _
    | succ j =>
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      rw [List.take_succ_cons, List.take_succ_cons, List.sum_cons, List.sum_cons]
      exact Nat.add_le_add_left (ih (by omega)) x

/-- Blocks for which the Orders read before each block, counted from 1, are exactly the
    lower record Orders from 1 to n: every block but the last has an upper record
    Order. -/
theorem upperRecordQ_order_of_cuts (hq : 3 ≤ q) {bs : List (List Bool)} {n : ℕ}
    (hcuts : ∀ a, (∃ i, i < bs.length ∧ a = 1 + ((bs.take i).map order).sum) ↔
      (1 ≤ a ∧ a ≤ n ∧ LowerRecordQ q a))
    {b : List Bool} (hb : b ∈ bs.dropLast) : UpperRecordQ q (order b) := by
  obtain ⟨i, hi, hbi⟩ := List.mem_iff_getElem.mp hb
  rw [List.getElem_dropLast] at hbi
  rw [List.length_dropLast] at hi
  have hi0 : i < bs.length := by
    omega
  have hi1 : i + 1 < bs.length := by
    omega
  have hstep : ((bs.take (i + 1)).map order).sum =
      ((bs.take i).map order).sum + order b := by
    rw [List.take_add_one, List.getElem?_eq_getElem hi0, hbi, List.map_append,
      List.sum_append]
    simp
  obtain ⟨ha1, _, hRa⟩ := (hcuts _).mp ⟨i, hi0, rfl⟩
  obtain ⟨_, hbn, hRb⟩ := (hcuts _).mp ⟨i + 1, hi1, rfl⟩
  rcases Nat.eq_zero_or_pos (order b) with h0 | hpos
  · rw [h0]
    exact upperRecordQ_zero q
  · have hnone : ∀ x, 1 + ((bs.take i).map order).sum < x →
        x < 1 + ((bs.take (i + 1)).map order).sum → ¬LowerRecordQ q x := by
      intro x hax hxb hRx
      obtain ⟨j, _, hxj⟩ := (hcuts x).mpr ⟨by omega, by omega, hRx⟩
      rcases Nat.lt_or_ge i j with hij | hji
      · have hmono := sum_take_le_sum_take (bs.map order) (show i + 1 ≤ j by omega)
        rw [← List.map_take, ← List.map_take] at hmono
        omega
      · have hmono := sum_take_le_sum_take (bs.map order) hji
        rw [← List.map_take, ← List.map_take] at hmono
        omega
    have h := upperRecordQ_sub_of_lowerRecordQ hq ha1 (by omega) hRa hRb hnone
    have heq : 1 + ((bs.take (i + 1)).map order).sum - (1 + ((bs.take i).map order).sum) =
        order b := by
      omega
    rw [heq] at h
    exact h

/-- For odd q ≥ 3, in the chain of the first word of Order n ≥ 1 every block but the last
    has an upper record Order. -/
theorem upperRecordQ_order_of_firstWordQ (hodd : Odd q) (hq : 3 ≤ q) {n : ℕ} (hn : 1 ≤ n)
    {bs : List (List Bool)} (hs : IsSplitQ q (firstWordQ q n) bs) {b : List Bool}
    (hb : b ∈ bs.dropLast) : UpperRecordQ q (order b) := by
  obtain ⟨bs', hs', _, hcuts⟩ := firstWordQ_chain hodd hq hn
  rw [splitQ_unique hs hs'] at hb
  exact upperRecordQ_order_of_cuts hq hcuts hb

end AcceleratedCollatz
