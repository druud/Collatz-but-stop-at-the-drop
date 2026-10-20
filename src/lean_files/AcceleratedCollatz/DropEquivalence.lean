-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.DescendToMinimum
import AcceleratedCollatz.RMap

/-!
  DropConjecture and CollatzConjecture, and their equivalence, obtained by
  instantiating DescendToMinimum's generic result with f := R, m := 1.
  Both are stated for the fast map R; `rDrop_iff_tDrop` (TRLink) gives the
  T-form of DropConjecture, DropEquivalenceT the T-form of the equivalence.
-/

namespace AcceleratedCollatz

open DescendToMinimum

def DropConjecture : Prop := DropsToward R 1

def CollatzConjecture : Prop := ReachesMin R 1

theorem R_never_below_one : NeverBelowMin R 1 := fun n _ => R_ge_one n

theorem drop_equiv_collatz : DropConjecture ↔ CollatzConjecture :=
  drop_equiv_reaches R 1 R_never_below_one

end AcceleratedCollatz
