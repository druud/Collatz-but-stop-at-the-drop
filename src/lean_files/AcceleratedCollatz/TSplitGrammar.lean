-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TSplit

/-!
  Grammar converse of the first-drop split: the q = 3 case of TSplitQ. For admissible
  blocks A1 .. Ak (k ≥ 1), 1 :: A1 ++ ... ++ Ak is admissible iff the running level
  3/2 · P(A1) ⋯ P(Ai) stays > 1 at every inner block boundary (1 ≤ i < k)
  and ends < 1 (`admissible_split_iff`).
-/

namespace AcceleratedCollatz

/-- The product is multiplicative under concatenation. -/
theorem seqProduct_append (a b : List Bool) :
    seqProduct (a ++ b) = seqProduct a * seqProduct b := by
  rw [← seqProductQ_three]
  exact seqProductQ_append 3 a b

/-- An admissible word is nonempty. -/
theorem ne_nil_of_admissible (b : List Bool) (h : Admissible b) : b ≠ [] :=
  ne_nil_of_admissibleQ ((admissibleQ_three b).mpr h)

/-- Levels > 1 at the start and at inner boundaries give levels > 1 at every
    position inside the blocks. -/
theorem one_lt_seqProduct_take_flatten :
    ∀ (bs : List (List Bool)) (P : List Bool), (∀ b ∈ bs, Admissible b) →
      1 < seqProduct P →
      (∀ i, 1 ≤ i → i < bs.length → 1 < seqProduct (P ++ (bs.take i).flatten)) →
      ∀ k < bs.flatten.length, 1 < seqProduct (P ++ bs.flatten.take k) := by
  intro bs P hbs
  rw [← seqProductQ_three]
  exact one_lt_seqProductQ_take_flatten bs P ((forall_admissibleQ_three bs).mpr hbs)

/-- Grammar converse: admissibility of 1 :: A1 ++ ... ++ Ak is decided at the block
    boundaries. -/
theorem admissible_split_iff (bs : List (List Bool)) (hbs : ∀ b ∈ bs, Admissible b) :
    Admissible (true :: bs.flatten) ↔
      (∀ i, 1 ≤ i → i < bs.length → 1 < seqProduct (true :: (bs.take i).flatten)) ∧
        seqProduct (true :: bs.flatten) < 1 := by
  rw [← admissibleQ_three, ← seqProductQ_three]
  exact admissibleQ_split_iff le_rfl bs ((forall_admissibleQ_three bs).mpr hbs)

end AcceleratedCollatz
