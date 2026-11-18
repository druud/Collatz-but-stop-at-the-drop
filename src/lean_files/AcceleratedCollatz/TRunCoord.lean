-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TGMap

/-!
  Runs in one step (Questions B80, B88, B89). The odd run of x (x + 1 = 2^a b) ends at
  3^a b - 1 (`odd_run_end`, TGMap), so it depends on 3^a b only: (a, b) and (a + 1, b / 3)
  land on the same value (`odd_run_end_shift`). The 1 put in front: for x = 5 mod 6,
  y = (2x - 1)/3 is odd, 3 mod 4, below x, and T(y) = x (`one_in_front`).
  The run coordinate: for a digit d (y -> (3y + 1)/2^d) and Y = (2^d - 3) y - 1, one digit d
  is Y -> 3Y/2^d (`run_coord_step`), so k digits d in a row are Y = 2^(dk) E -> 3^k E.
-/

namespace AcceleratedCollatz

/-- (a, b) and (a + 1, b / 3) land on the same value after their odd runs. -/
theorem odd_run_end_shift (x x' a b : ℕ) (h : x + 1 = 2 ^ a * (3 * b))
    (h' : x' + 1 = 2 ^ (a + 1) * b) : tStep^[a] x = tStep^[a + 1] x' := by
  have e1 := odd_run_end x a (3 * b) h
  have e2 := odd_run_end x' (a + 1) b h'
  have : 3 ^ a * (3 * b) = 3 ^ (a + 1) * b := by ring
  omega

/-- The 1 put in front: for x = 5 mod 6, y = (2x - 1)/3 is odd, 3 mod 4, below x, and
    T(y) = x. -/
theorem one_in_front (x : ℕ) (hx : x % 6 = 5) :
    ((2 * x - 1) / 3) % 4 = 3 ∧ (2 * x - 1) / 3 < x ∧ tStep ((2 * x - 1) / 3) = x := by
  refine ⟨by omega, by omega, ?_⟩
  rw [tStep_odd _ (by omega)]
  omega

/-- The run coordinate: if 3y + 1 = 2^d z then 2^d ((2^d - 3) z - 1) = 3 ((2^d - 3) y - 1),
    i.e. Y = (2^d - 3) y - 1 goes to 3Y/2^d under one digit d (in ℤ, so d = 1 is allowed). -/
theorem run_coord_step (d : ℕ) (y z : ℤ) (h : 3 * y + 1 = 2 ^ d * z) :
    2 ^ d * ((2 ^ d - 3) * z - 1) = 3 * ((2 ^ d - 3) * y - 1) := by
  have e : (2 : ℤ) ^ d * ((2 ^ d - 3) * z - 1) = (2 ^ d - 3) * (2 ^ d * z) - 2 ^ d := by ring
  rw [e, ← h]
  ring

/-- k digits d in a row: if each step is 3 y_i + 1 = 2^d y_(i+1), then
    2^(dk) Y_k = 3^k Y_0 with Y_i = (2^d - 3) y_i - 1. -/
theorem run_coord_iterate (d : ℕ) (y : ℕ → ℤ) (hy : ∀ i, 3 * y i + 1 = 2 ^ d * y (i + 1)) :
    ∀ k : ℕ, 2 ^ (d * k) * ((2 ^ d - 3) * y k - 1) = 3 ^ k * ((2 ^ d - 3) * y 0 - 1) := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have s := run_coord_step d (y k) (y (k + 1)) (hy k)
    calc 2 ^ (d * (k + 1)) * ((2 ^ d - 3) * y (k + 1) - 1)
        = 2 ^ (d * k) * (2 ^ d * ((2 ^ d - 3) * y (k + 1) - 1)) := by ring
      _ = 2 ^ (d * k) * (3 * ((2 ^ d - 3) * y k - 1)) := by rw [s]
      _ = 3 * (2 ^ (d * k) * ((2 ^ d - 3) * y k - 1)) := by ring
      _ = 3 ^ (k + 1) * ((2 ^ d - 3) * y 0 - 1) := by rw [ih]; ring

end AcceleratedCollatz
