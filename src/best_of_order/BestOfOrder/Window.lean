-- SPDX-License-Identifier: MIT
import BestOfOrder.Bridge

/-!
  The window (paper, Theorem B and Theorem 6.1). If a member x of the class of an admissible word
  of Order n has T^L(x)/x > b/a, then x (2^L b - 3^n a) < R(n) a, with R(n) = `rhoMax n` the
  constant of the wall word (`window`). A ratio b/a is stated as b x < a T^L(x), so a may be any
  natural number; with b/a the ratio of a class id of the Order, this is the window of the search.
-/

namespace BestOfOrder

open AcceleratedCollatz

/-- Theorem B: a start with a ratio above b/a lies inside the window. -/
theorem window {s : List Bool} (hA : Admissible s) {x a b : ℕ} (hx : tBits x s.length = s)
    (hab : b * x < a * tStep^[s.length] x) :
    (x : ℤ) * (2 ^ s.length * b - 3 ^ order s * a) < rhoMax (order s) * a := by
  have h := affine s.length x
  rw [hx] at h
  have h' : (2 : ℤ) ^ s.length * (tStep^[s.length] x : ℤ) = 3 ^ order s * x + rho s := by
    exact_mod_cast h
  have hab' : (b : ℤ) * x < a * (tStep^[s.length] x : ℤ) := by exact_mod_cast hab
  have hR : (rho s : ℤ) ≤ rhoMax (order s) := by exact_mod_cast rho_le_wall hA
  have h1 : (2 : ℤ) ^ s.length * (b * x) < 2 ^ s.length * (a * (tStep^[s.length] x : ℤ)) :=
    mul_lt_mul_of_pos_left hab' (by positivity)
  have h2 : (2 : ℤ) ^ s.length * (a * (tStep^[s.length] x : ℤ)) = a * (3 ^ order s * x + rho s) := by
    rw [← h']
    ring
  have h3 : (a : ℤ) * rho s ≤ a * rhoMax (order s) := mul_le_mul_of_nonneg_left hR (by positivity)
  nlinarith

end BestOfOrder
