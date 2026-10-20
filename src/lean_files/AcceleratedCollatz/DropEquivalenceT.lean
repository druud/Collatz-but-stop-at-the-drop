-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TClass
import AcceleratedCollatz.TRLink

/-!
  The T form of DropEquivalence: `CollatzConjectureT`, the conjecture for the step T,
  is equivalent to the drop under T (`tDrop_equiv_collatzT`), to DropConjecture
  (`drop_equiv_collatzT`) and to CollatzConjecture for the fast map R
  (`collatz_iff_collatzT`).
-/

namespace AcceleratedCollatz

open DescendToMinimum

def CollatzConjectureT : Prop := ReachesMin tStep 1

theorem tStep_never_below_one : NeverBelowMin tStep 1 := fun n hn => tStep_pos n hn

theorem tDrop_equiv_collatzT : DropsToward tStep 1 ↔ CollatzConjectureT :=
  drop_equiv_reaches tStep 1 tStep_never_below_one

theorem drop_equiv_collatzT : DropConjecture ↔ CollatzConjectureT :=
  rDrop_iff_tDrop.trans tDrop_equiv_collatzT

theorem collatz_iff_collatzT : CollatzConjecture ↔ CollatzConjectureT :=
  drop_equiv_collatz.symm.trans drop_equiv_collatzT

end AcceleratedCollatz
