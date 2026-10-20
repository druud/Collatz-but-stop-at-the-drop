-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TChainQ
import AcceleratedCollatz.TFirstWordQ

/-!
  The first word of each Order in the q-family as a chain (odd q ≥ 3). Its first part is
  the leading 1 followed by p2Q(1) - 2 blocks [0] (`firstBodyQ_one`); with these and with
  the final halving as blocks, the first word of Order n ≥ 1 is 1 :: (B1 ++ ... ++ Bm)
  with admissible blocks (`firstWordQ_chain`): every block is the first word of its
  Order, [0] being the first word of Order 0, and the Orders read before the blocks are
  exactly the lower record Orders from 1 to n. By `splitQ_unique` these blocks are its
  chain. For q = 3 there is no block [0] after the leading 1.
-/

namespace AcceleratedCollatz

variable {q : ℕ}

/-- Order 1 is a lower record Order. -/
theorem lowerRecordQ_one (q : ℕ) : LowerRecordQ q 1 := by
  intro a ha1 ha
  omega

/-- The first part of a first word: the first odd step and p2Q(1) - 2 halvings. -/
theorem firstBodyQ_one (q : ℕ) :
    firstBodyQ q 1 = true :: List.replicate (p2Q q 1 - 2) false := by
  have h : firstBodyQ q 1 =
      firstBodyQ q 0 ++ true :: List.replicate (p2Q q 1 - p2Q q 0 - 1) false := rfl
  rw [h, p2Q_zero, Nat.sub_sub]
  rfl

theorem flatten_replicate_false (k : ℕ) :
    (List.replicate k [false]).flatten = List.replicate k false := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, List.flatten_cons, ih, List.replicate_succ]
    rfl

/-- Blocks [0] have Orders that sum to 0. -/
theorem sum_map_order_eq_zero {X : List (List Bool)} (h : ∀ b ∈ X, b = [false]) :
    (X.map order).sum = 0 := by
  induction X with
  | nil => rfl
  | cons b X ih =>
    rw [List.map_cons, List.sum_cons, h b List.mem_cons_self,
      ih (fun c hc => h c (List.mem_cons_of_mem b hc))]
    rfl

/-- With blocks [0] in front of the blocks of `FirstBlocksQ`, and at most one behind them,
    present exactly when n is a lower record Order: the Orders read before the blocks are
    the lower record Orders from 1 to n. -/
theorem FirstBlocksQ.cuts_zero {Z cs T : List (List Bool)} {n : ℕ}
    (hcs : FirstBlocksQ q cs n) (hn : 1 ≤ n) (hZ : ∀ b ∈ Z, b = [false])
    (hT : ∀ b ∈ T, b = [false]) (hTlen : T.length ≤ 1) (htail : T ≠ [] ↔ LowerRecordQ q n)
    (a : ℕ) :
    (∃ i, i < (Z ++ (cs ++ T)).length ∧ a = 1 + (((Z ++ (cs ++ T)).take i).map order).sum) ↔
      (1 ≤ a ∧ a ≤ n ∧ LowerRecordQ q a) := by
  have hsum := hcs.sum
  constructor
  · rintro ⟨i, hi, ha⟩
    rw [List.length_append, List.length_append] at hi
    rcases Nat.lt_or_ge i Z.length with hiz | hiz
    · rw [List.take_append_of_le_length (le_of_lt hiz),
        sum_map_order_eq_zero (fun b hb => hZ b (List.mem_of_mem_take hb))] at ha
      rw [ha]
      exact ⟨le_rfl, hn, lowerRecordQ_one q⟩
    · obtain ⟨k, rfl⟩ : ∃ k, i = Z.length + k := ⟨i - Z.length, by omega⟩
      rw [List.take_length_add_append, List.map_append, List.sum_append,
        sum_map_order_eq_zero hZ] at ha
      rcases Nat.lt_or_ge k cs.length with hk | hk
      · rw [List.take_append_of_le_length (le_of_lt hk)] at ha
        obtain ⟨ha1, han, hR⟩ := (hcs.cuts a).mp ⟨k, hk, by omega⟩
        exact ⟨ha1, by omega, hR⟩
      · obtain ⟨j, rfl⟩ : ∃ j, k = cs.length + j := ⟨k - cs.length, by omega⟩
        rw [List.take_length_add_append, List.map_append, List.sum_append,
          sum_map_order_eq_zero (fun b hb => hT b (List.mem_of_mem_take hb))] at ha
        have hTne : T ≠ [] := by
          intro hnil
          rw [hnil, List.length_nil] at hi
          omega
        have han : a = n := by
          omega
        rw [han]
        exact ⟨hn, le_rfl, htail.mp hTne⟩
  · rintro ⟨ha1, han, hR⟩
    rcases Nat.lt_or_ge a n with hlt | hge
    · obtain ⟨k, hk, hak⟩ := (hcs.cuts a).mpr ⟨ha1, hlt, hR⟩
      refine ⟨Z.length + k, ?_, ?_⟩
      · rw [List.length_append, List.length_append]
        omega
      · rw [List.take_length_add_append, List.take_append_of_le_length (le_of_lt hk),
          List.map_append, List.sum_append, sum_map_order_eq_zero hZ]
        omega
    · have han' : a = n := by
        omega
      rw [han'] at hR
      have hTne := htail.mpr hR
      have hTpos := List.length_pos_iff.mpr hTne
      refine ⟨Z.length + cs.length, ?_, ?_⟩
      · rw [List.length_append, List.length_append]
        omega
      · rw [List.take_length_add_append, List.take_left' rfl, List.map_append,
          List.sum_append, sum_map_order_eq_zero hZ]
        omega

/-- The first word of Order n ≥ 1 as 1 :: (B1 ++ ... ++ Bm): every block is the first word
    of its Order, and the Orders read before the blocks are exactly the lower record
    Orders from 1 to n. -/
theorem firstWordQ_eq_cons_flatten (hq : 3 ≤ q) {n : ℕ} (hn : 1 ≤ n) :
    ∃ bs : List (List Bool), firstWordQ q n = true :: bs.flatten ∧
      (∀ b ∈ bs, b = firstWordQ q (order b)) ∧ 1 + (bs.map order).sum = n ∧
      ∀ a, (∃ i, i < bs.length ∧ a = 1 + ((bs.take i).map order).sum) ↔
        (1 ≤ a ∧ a ≤ n ∧ LowerRecordQ q a) := by
  obtain ⟨cs, t, hs, hcs, htail, ht⟩ := firstWordQ_blocks hq hn
  obtain ⟨Z, hZdef⟩ : ∃ Z : List (List Bool), Z = List.replicate (p2Q q 1 - 2) [false] :=
    ⟨_, rfl⟩
  obtain ⟨T, hTdef⟩ : ∃ T : List (List Bool), T = t.map (fun _ => [false]) := ⟨_, rfl⟩
  have hZ : ∀ b ∈ Z, b = [false] := by
    intro b hb
    rw [hZdef] at hb
    exact List.eq_of_mem_replicate hb
  have hT : ∀ b ∈ T, b = [false] := by
    intro b hb
    rw [hTdef] at hb
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp hb
    rfl
  have hZflat : Z.flatten = List.replicate (p2Q q 1 - 2) false := by
    rw [hZdef, flatten_replicate_false]
  have hTflat : T.flatten = t := by
    rw [hTdef]
    rcases ht with rfl | rfl
    · rfl
    · rfl
  have hTlen : T.length ≤ 1 := by
    rw [hTdef, List.length_map]
    rcases ht with rfl | rfl
    · exact Nat.zero_le 1
    · exact le_rfl
  have hTtail : T ≠ [] ↔ LowerRecordQ q n := by
    rw [← htail, hTdef]
    rcases ht with rfl | rfl
    · simp
    · simp
  refine ⟨Z ++ (cs ++ T), ?_, ?_, ?_, hcs.cuts_zero hn hZ hT hTlen hTtail⟩
  · rw [hs, firstBodyQ_one, List.flatten_append, List.flatten_append, hZflat, hTflat]
    rfl
  · intro b hb
    rcases List.mem_append.mp hb with hb1 | hb2
    · rw [hZ b hb1]
      rfl
    · rcases List.mem_append.mp hb2 with hb3 | hb4
      · exact (hcs.first b hb3).2
      · rw [hT b hb4]
        rfl
  · have hsum := hcs.sum
    rw [List.map_append, List.map_append, List.sum_append, List.sum_append,
      sum_map_order_eq_zero hZ, sum_map_order_eq_zero hT]
    omega

/-- For odd q ≥ 3 the chain of the first word of Order n ≥ 1: every block is the first
    word of its Order, and the Orders read before the blocks are exactly the lower record
    Orders from 1 to n. -/
theorem firstWordQ_chain (hodd : Odd q) (hq : 3 ≤ q) {n : ℕ} (hn : 1 ≤ n) :
    ∃ bs : List (List Bool), IsSplitQ q (firstWordQ q n) bs ∧
      (∀ b ∈ bs, b = firstWordQ q (order b)) ∧
      ∀ a, (∃ i, i < bs.length ∧ a = 1 + ((bs.take i).map order).sum) ↔
        (1 ≤ a ∧ a ≤ n ∧ LowerRecordQ q a) := by
  obtain ⟨bs, hs, hfirst, _, hcuts⟩ := firstWordQ_eq_cons_flatten hq hn
  refine ⟨bs, ⟨hs, ?_⟩, hfirst, hcuts⟩
  intro b hb
  rw [hfirst b hb]
  exact firstWordQ_admissibleQ hodd hq (order b)

end AcceleratedCollatz
