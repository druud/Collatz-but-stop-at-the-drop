-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TSweepQ

/-!
  Sweep map (paper sec:sweeps): the steps of a word sorted by the level at their
  endpoints, highest first (Armstrong, Loehr, Warrington). The q = 3 case of
  `sweepQ` (`sweepQ_three`): it permutes the steps (`sweep_perm`) and maps
  admissible words of Order n to admissible words of Order n (`sweep_mem_admSet`).
-/

namespace AcceleratedCollatz

/-- Step indices of s, sorted by endpoint level, highest first. -/
def sweepIdx (s : List Bool) : List ℕ :=
  (List.range s.length).mergeSort (fun i k => decide (lvl s (k + 1) ≤ lvl s (i + 1)))

/-- Sweep map: the steps of s in the order of `sweepIdx`. -/
def sweep (s : List Bool) : List Bool := (sweepIdx s).map (fun i => s.getD i false)

/-- For q = 3 the sweep of the q-family is the sweep of the paper. -/
theorem sweepQ_three : sweepQ 3 = sweep := by
  funext s
  simp only [sweepQ, sweepIdxQ, sweep, sweepIdx, lvlQ_three]

/-- The sweep permutes the steps. -/
theorem sweep_perm (s : List Bool) : (sweep s).Perm s :=
  sweepQ_three ▸ sweepQ_perm 3 s

theorem length_sweep (s : List Bool) : (sweep s).length = s.length :=
  (sweep_perm s).length_eq

theorem seqProduct_sweep (s : List Bool) : seqProduct (sweep s) = seqProduct s :=
  ((sweep_perm s).map factor).prod_eq

theorem order_sweep (s : List Bool) : order (sweep s) = order s :=
  ((sweep_perm s).filter id).length_eq

/-- The sweep maps admissible words of Order n to admissible words of Order n. -/
theorem sweep_mem_admSet {n : ℕ} {s : List Bool} (hs : s ∈ admSet n) :
    sweep s ∈ admSet n := by
  rw [← admSetQ_three] at hs ⊢
  rw [← sweepQ_three]
  exact sweepQ_mem_admSetQ (by decide) (by norm_num) hs

end AcceleratedCollatz
