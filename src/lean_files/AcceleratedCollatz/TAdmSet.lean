-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TChainOrders

/-!
  The admissible PVs of Order n as a finite set: `admSet n`, cut out of the bit
  lists of length p2(n) (`allBits`), with `mem_admSet`; it is the q = 3 case of
  `admSetQ` (`admSetQ_three`). `LevelUp` and `ValidOrders` are decidable.
-/

namespace AcceleratedCollatz

variable (n : ℕ)

/-- `LevelUp` is decidable. -/
instance (os : List ℕ) : Decidable (LevelUp os) := by
  unfold LevelUp
  infer_instance

/-- `ValidOrders` is decidable. -/
instance (os : List ℕ) : Decidable (ValidOrders os) := by
  unfold ValidOrders
  infer_instance

/-- Admissible PVs of Order n. -/
def admSet (n : ℕ) : Finset (List Bool) :=
  (allBits (p2_of n)).toFinset.filter (fun s => Admissible s ∧ order s = n)

/-- Membership in `admSet n`. -/
theorem mem_admSet (s : List Bool) : s ∈ admSet n ↔ Admissible s ∧ order s = n := by
  simp only [admSet, Finset.mem_filter, List.mem_toFinset, mem_allBits]
  constructor
  · intro h
    exact h.2
  · intro h
    refine ⟨?_, h⟩
    rw [admissible_length s h.1, h.2]

/-- For q = 3 the q-family is the admissible set of the paper. -/
theorem admSetQ_three (n : ℕ) : admSetQ 3 n = admSet n := by
  ext s
  rw [mem_admSetQ (by norm_num), mem_admSet, admissibleQ_three]

end AcceleratedCollatz
