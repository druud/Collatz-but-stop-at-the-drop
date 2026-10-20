-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TChainOrders
import AcceleratedCollatz.TRecordLowQ

/-!
  Record lows: the q = 3 case of TRecordLowQ (`isRecordLowQ_three`). A strict
  record-low time m of a word s: the level after its first m letters is below every
  earlier level (`IsRecordLow`). Appending an admissible block to a word whose level
  ends at its minimum adds exactly one record low, at the block's end
  (`isRecordLow_append`). So for 1 :: c_1 ... c_k with admissible c_i, the record-low
  times are exactly the cut positions 1 + |c_1 ... c_i| (`isRecordLow_iff_cut`), and
  in the chain decomposition of an admissible word the cuts are its record-low times,
  the tail [0] counting as a last block (`exists_chain_recordLow`).
-/

namespace AcceleratedCollatz

/-- m is a strict record-low time of s: the level after m letters is below every
    earlier level. -/
def IsRecordLow (s : List Bool) (m : ℕ) : Prop :=
  1 ≤ m ∧ m ≤ s.length ∧ ∀ j, 1 ≤ j → j < m → seqProduct (s.take m) < seqProduct (s.take j)

/-- The level at the end of w is at most every level along w. -/
def EndIsMin (w : List Bool) : Prop :=
  ∀ j, 1 ≤ j → j ≤ w.length → seqProduct w ≤ seqProduct (w.take j)

/-- `IsRecordLow` is `IsRecordLowQ` at q = 3. -/
theorem isRecordLowQ_three (s : List Bool) (m : ℕ) : IsRecordLowQ 3 s m ↔ IsRecordLow s m := by
  unfold IsRecordLowQ IsRecordLow
  rw [seqProductQ_three]

/-- `EndIsMin` is `EndIsMinQ` at q = 3. -/
theorem endIsMinQ_three (w : List Bool) : EndIsMinQ 3 w ↔ EndIsMin w := by
  unfold EndIsMinQ EndIsMin
  rw [seqProductQ_three]

/-- Inside an appended admissible block the level stays above the block's start. -/
theorem seqProduct_lt_inside (w b : List Bool) (r : ℕ) (hb : Admissible b) (hr1 : 1 ≤ r)
    (hr : r < b.length) : seqProduct w < seqProduct ((w ++ b).take (w.length + r)) := by
  rw [← seqProductQ_three]
  exact seqProductQ_lt_inside (by norm_num) w b r ((admissibleQ_three b).mpr hb) hr1 hr

/-- At the end of an appended admissible block the level is below the block's start. -/
theorem seqProduct_append_lt (w b : List Bool) (hb : Admissible b) :
    seqProduct (w ++ b) < seqProduct w := by
  rw [← seqProductQ_three]
  exact seqProductQ_append_lt (by norm_num) w b ((admissibleQ_three b).mpr hb)

/-- After an appended admissible block, the level ends at its minimum again. -/
theorem endIsMin_append (w b : List Bool) (hQ : EndIsMin w) (hb : Admissible b) :
    EndIsMin (w ++ b) :=
  (endIsMinQ_three _).mp (endIsMinQ_append (by norm_num) w b ((endIsMinQ_three w).mpr hQ)
    ((admissibleQ_three b).mpr hb))

/-- Appending an admissible block adds exactly one record low, at its end. -/
theorem isRecordLow_append (w b : List Bool) (hw : w ≠ []) (hQ : EndIsMin w)
    (hb : Admissible b) (m : ℕ) :
    IsRecordLow (w ++ b) m ↔ IsRecordLow w m ∨ m = w.length + b.length := by
  rw [← isRecordLowQ_three, ← isRecordLowQ_three]
  exact isRecordLowQ_append (by norm_num) w b hw ((endIsMinQ_three w).mpr hQ)
    ((admissibleQ_three b).mpr hb) m

/-- Record lows of w followed by admissible blocks: those of w, and the block ends. -/
theorem isRecordLow_append_flatten (cs : List (List Bool)) (hcs : ∀ c ∈ cs, Admissible c) :
    ∀ w : List Bool, w ≠ [] → EndIsMin w → ∀ m,
      (IsRecordLow (w ++ cs.flatten) m ↔
        IsRecordLow w m ∨
          ∃ i, 1 ≤ i ∧ i ≤ cs.length ∧ m = w.length + (cs.take i).flatten.length) := by
  intro w hw hQ m
  rw [← isRecordLowQ_three, ← isRecordLowQ_three]
  exact isRecordLowQ_append_flatten (by norm_num) cs ((forall_admissibleQ_three cs).mpr hcs)
    w hw ((endIsMinQ_three w).mpr hQ) m

/-- The one-letter word [1] has its only record low at 1. -/
theorem isRecordLow_single (m : ℕ) : IsRecordLow [true] m ↔ m = 1 := by
  rw [← isRecordLowQ_three]
  exact isRecordLowQ_single 3 m

/-- [1] ends at its minimum level. -/
theorem endIsMin_single : EndIsMin [true] :=
  (endIsMinQ_three _).mp (endIsMinQ_single 3)

/-- The record-low times of 1 :: c_1 ... c_k (admissible c_i) are the cuts. -/
theorem isRecordLow_iff_cut (cs : List (List Bool)) (hcs : ∀ c ∈ cs, Admissible c) (m : ℕ) :
    IsRecordLow (true :: cs.flatten) m ↔
      ∃ i, i ≤ cs.length ∧ m = 1 + (cs.take i).flatten.length := by
  rw [← isRecordLowQ_three]
  exact isRecordLowQ_iff_cut (by norm_num) cs ((forall_admissibleQ_three cs).mpr hcs) m

/-- The chain cuts of an admissible word are exactly its record-low times; the tail
    [0], if present, counts as a last block. -/
theorem exists_chain_recordLow (s : List Bool) (hA : Admissible s) (hord : 1 ≤ order s) :
    ∃ (bs : List (List Bool)) (t : List Bool),
      s = true :: (bs.flatten ++ t) ∧ (∀ b ∈ bs, IsChainBlock b) ∧ (t = [] ∨ t = [false]) ∧
      ∀ m, IsRecordLow s m ↔
        ∃ i, i ≤ (bs ++ t.map (fun _ => [false])).length ∧
          m = 1 + ((bs ++ t.map (fun _ => [false])).take i).flatten.length := by
  obtain ⟨bs, t, hs, hbs, ht, _⟩ := exists_chain s hA hord
  refine ⟨bs, t, hs, hbs, ht, ?_⟩
  have hflat : (bs ++ t.map (fun _ => [false])).flatten = bs.flatten ++ t := by
    rcases ht with rfl | rfl
    · simp
    · simp
  have hcs : ∀ c ∈ bs ++ t.map (fun _ => [false]), Admissible c := by
    intro c hc
    rw [List.mem_append] at hc
    rcases hc with hc | hc
    · exact (hbs c hc).adm
    · rw [List.mem_map] at hc
      obtain ⟨_, _, rfl⟩ := hc
      exact admissible_singleton_false
  intro m
  rw [← isRecordLow_iff_cut _ hcs m, hflat, hs]

/-- `IsRecordLow` is decidable. -/
instance (s : List Bool) (m : ℕ) : Decidable (IsRecordLow s m) := by
  unfold IsRecordLow
  infer_instance

/-- The word 1100 (Order 2): block 10, tail [0]; record lows at 1, 3 and 4, not at 2. -/
example : Admissible [true, true, false, false] := by
  decide +kernel

example : IsRecordLow [true, true, false, false] 1 := by
  decide +kernel

example : ¬ IsRecordLow [true, true, false, false] 2 := by
  decide +kernel

example : IsRecordLow [true, true, false, false] 3 := by
  decide +kernel

example : IsRecordLow [true, true, false, false] 4 := by
  decide +kernel

end AcceleratedCollatz
