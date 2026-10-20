-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TFirstOrdersQ
import AcceleratedCollatz.TFirstWord
import AcceleratedCollatz.TSplit

/-!
  The Orders of the blocks of a first word, q = 3: in the chain of the first word of
  Order n ≥ 1 every block but the last has an upper record Order
  (`upperRecord_order_of_firstWord`, the q = 3 case of
  `upperRecordQ_order_of_firstWordQ`). The last block can have an Order that is no upper
  record Order: the first word of Order 4 is 1101100 with blocks 10 and 1100, of Orders 1
  and 2.
-/

namespace AcceleratedCollatz

/-- In the chain of the first word of Order n ≥ 1 every block but the last has an upper
    record Order. -/
theorem upperRecord_order_of_firstWord {n : ℕ} (hn : 1 ≤ n) {bs : List (List Bool)}
    (hs : IsSplit (firstWord n) bs) {b : List Bool} (hb : b ∈ bs.dropLast) :
    UpperRecord (order b) := by
  have hs' : IsSplitQ 3 (firstWordQ 3 n) bs := by
    rw [firstWordQ_three]
    exact ⟨hs.eq, fun c hc => (admissibleQ_three c).mpr (hs.adm c hc)⟩
  exact upperRecordQ_order_of_firstWordQ (by decide) le_rfl hn hs' hb

/-- Order 2 is no upper record Order. -/
theorem not_upperRecord_two : ¬UpperRecord 2 := by
  intro h
  have h1 := h 1 le_rfl (by omega)
  have hp1 : p2_of 1 = 2 := by
    decide +kernel
  have hp2 : p2_of 2 = 4 := by
    decide +kernel
  omega

/-- The chain of the first word of Order 4: the blocks 10 and 1100, of Orders 1 and 2. -/
theorem isSplit_firstWord_four :
    IsSplit (firstWord 4) [[true, false], [true, true, false, false]] := by
  refine ⟨by decide +kernel, ?_⟩
  intro b hb
  rcases List.mem_cons.mp hb with rfl | hb'
  · decide +kernel
  · obtain rfl := List.mem_singleton.mp hb'
    decide +kernel

end AcceleratedCollatz
