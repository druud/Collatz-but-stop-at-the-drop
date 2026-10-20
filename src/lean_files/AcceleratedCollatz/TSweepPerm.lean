-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TSweep
import AcceleratedCollatz.TSweepPermQ

/-!
  The sweep as a permutation (paper sec:sweeps), the q = 3 case of
  `TSweepPermQ`. Integer weights c, d with d (p2(a) - 1) < c a < d p2(a) for all
  1 ≤ a ≤ n + 1 (`exists_weights`); with the weights c - d and -d the sweep of an
  admissible word is the integer sweep of its Dyck part followed by the final
  halving (`sweep_eq_sweepZ`). Under `SweepBijective` the sweep permutes
  `admSet n` for every n (`sweep_bijOn`).
-/

namespace AcceleratedCollatz

/-- Integer weights c, d strictly between (p2(a) - 1)/a and p2(a)/a for 1 ≤ a ≤ n + 1. -/
theorem exists_weights (n : ℕ) : ∃ c d : ℤ, 0 < d ∧ ∀ a : ℕ, 1 ≤ a → a ≤ n + 1 →
    d * ((p2_of a : ℤ) - 1) < c * a ∧ c * a < d * p2_of a :=
  exists_weightsQ le_rfl n

/-- The sweep of an admissible word is the integer sweep of its Dyck part, then the
    final halving. -/
theorem sweep_eq_sweepZ {n : ℕ} {c d : ℤ} (hd : 0 < d)
    (hcd : ∀ a : ℕ, 1 ≤ a → a ≤ n + 1 →
      d * ((p2_of a : ℤ) - 1) < c * a ∧ c * a < d * p2_of a)
    {w : List Bool} (hs : w ++ [false] ∈ admSet n) :
    sweep (w ++ [false]) = sweepZ (c - d) (-d) w ++ [false] := by
  rw [← admSetQ_three] at hs
  rw [← sweepQ_three]
  exact sweepQ_eq_sweepZ (by decide) le_rfl hd hcd hs

/-- Under Thomas and Williams, Thm 6.3, the sweep permutes the admissible words of
    each Order. -/
theorem sweep_bijOn (hTW : SweepBijective) (n : ℕ) :
    Set.BijOn sweep (admSet n : Set (List Bool)) (admSet n) := by
  rw [← sweepQ_three, ← admSetQ_three]
  exact sweepQ_bijOn (by decide) le_rfl hTW n

end AcceleratedCollatz
