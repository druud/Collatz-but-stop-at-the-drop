-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TCutSweepQ
import AcceleratedCollatz.TGridOrder
import AcceleratedCollatz.TStartSweepInjQ
import AcceleratedCollatz.TSweep

/-!
  Start sweep and cut sweep (paper sec:sweeps), the q = 3 case of `TStartSweepPermQ`,
  `TStartSweepInjQ` and `TCutSweepQ`. The start sweep sorts the steps of a word by the
  level at which they start, lowest first (`startSweep`); the cut sweep is the start sweep
  of the word without its final step, followed by a halving (`cutSweep`): for a word that
  ends in a halving, a rearrangement of its steps. The start sweep maps the admissible
  words of Order n to admissible words exactly at the upper record Orders
  (`mapsTo_startSweep_iff`); under `SweepBijective` it permutes them there
  (`startSweep_bijOn_iff`) and is one-to-one on them at every Order
  (`startSweep_injOn`). The cut sweep maps them to admissible words at every Order
  (`cutSweep_mem_admSet`); under `SweepBijective` it permutes them exactly at the
  lower record Orders (`cutSweep_bijOn_iff`), and at every other Order two admissible
  words have the same cut sweep (`not_injOn_cutSweep`).
-/

namespace AcceleratedCollatz

/-- Step indices of s, sorted by starting level, lowest first. -/
def startIdx (s : List Bool) : List ℕ :=
  (List.range s.length).mergeSort (fun i k => decide (lvl s i ≤ lvl s k))

/-- Start sweep: the steps of s in the order of `startIdx`. -/
def startSweep (s : List Bool) : List Bool := (startIdx s).map (fun i => s.getD i false)

/-- Cut sweep: the start sweep of s without its final step, then a halving. -/
def cutSweep (s : List Bool) : List Bool := startSweep s.dropLast ++ [false]

/-- For q = 3 the start sweep of the q-family is the start sweep of the paper. -/
theorem startSweepQ_three : startSweepQ 3 = startSweep := by
  funext s
  simp only [startSweepQ, startIdxQ, startSweep, startIdx, lvlQ_three]

/-- For q = 3 the cut sweep of the q-family is the cut sweep of the paper. -/
theorem cutSweepQ_three : cutSweepQ 3 = cutSweep := by
  funext s
  simp only [cutSweepQ, cutSweep, startSweepQ_three]

/-- The start sweep maps the admissible words of Order n to admissible words exactly at
    the upper record Orders. -/
theorem mapsTo_startSweep_iff (n : ℕ) :
    Set.MapsTo startSweep (admSet n : Set (List Bool)) (admSet n) ↔ UpperRecord n := by
  rw [← startSweepQ_three, ← admSetQ_three]
  exact mapsTo_startSweepQ_iff (by decide) le_rfl n

/-- Under Thomas and Williams, Thm 6.3, the start sweep permutes the admissible words of
    Order n exactly at the upper record Orders. -/
theorem startSweep_bijOn_iff (hTW : SweepBijective) (n : ℕ) :
    Set.BijOn startSweep (admSet n : Set (List Bool)) (admSet n) ↔ UpperRecord n := by
  rw [← startSweepQ_three, ← admSetQ_three]
  exact startSweepQ_bijOn_iff (by decide) le_rfl hTW n

/-- Under Thomas and Williams, Thm 6.3, the start sweep is one-to-one on the admissible
    words of every Order. -/
theorem startSweep_injOn (hTW : SweepBijective) (n : ℕ) :
    Set.InjOn startSweep (admSet n : Set (List Bool)) := by
  rw [← startSweepQ_three, ← admSetQ_three]
  exact startSweepQ_injOn (by decide) le_rfl hTW n

/-- The cut sweep maps admissible words of Order n to admissible words of Order n. -/
theorem cutSweep_mem_admSet {n : ℕ} {s : List Bool} (hs : s ∈ admSet n) :
    cutSweep s ∈ admSet n := by
  rw [← admSetQ_three] at hs ⊢
  rw [← cutSweepQ_three]
  exact cutSweepQ_mem_admSetQ (by decide) le_rfl hs

/-- Under Thomas and Williams, Thm 6.3, the cut sweep permutes the admissible words of
    Order n exactly at the lower record Orders. -/
theorem cutSweep_bijOn_iff (hTW : SweepBijective) (n : ℕ) :
    Set.BijOn cutSweep (admSet n : Set (List Bool)) (admSet n) ↔ LowerRecord n := by
  rw [← cutSweepQ_three, ← admSetQ_three]
  exact cutSweepQ_bijOn_iff (by decide) le_rfl hTW n

/-- At an Order that is no lower record two admissible words have the same cut sweep. -/
theorem not_injOn_cutSweep {n : ℕ} (hR : ¬LowerRecord n) :
    ¬Set.InjOn cutSweep (admSet n : Set (List Bool)) := by
  rw [← cutSweepQ_three, ← admSetQ_three]
  exact not_injOn_cutSweepQ (by decide) le_rfl hR

set_option linter.hashCommand false in
#guard startSweep [true, true, false, true, true, false, true, false] =
  [true, true, true, true, true, false, false, false]

set_option linter.hashCommand false in
#guard cutSweep [true, true, false, true, false] = [true, true, true, false, false]

end AcceleratedCollatz
