-- SPDX-License-Identifier: MIT
import BestOfOrder.Bridge
import Mathlib.Tactic.LinearCombination

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

/-- Remark 2.8 (ties): two starts with the same word length L and Order, x of word s and y of word t,
    with equal ratios T^L(x)/x = T^L(y)/y, have rho s * y = rho t * x. -/
theorem tie_rho {s t : List Bool} (hl : s.length = t.length) (ho : order s = order t) {x y : ℕ}
    (hx : tBits x s.length = s) (hy : tBits y t.length = t)
    (h : tStep^[s.length] x * y = tStep^[s.length] y * x) : rho s * y = rho t * x := by
  have h1 := affine s.length x
  have h2 := affine s.length y
  rw [hx] at h1
  rw [hl, hy, ← ho, ← hl] at h2
  have h1' : (2 : ℤ) ^ s.length * (tStep^[s.length] x : ℤ) = 3 ^ order s * x + rho s := by
    exact_mod_cast h1
  have h2' : (2 : ℤ) ^ s.length * (tStep^[s.length] y : ℤ) = 3 ^ order s * y + rho t := by
    exact_mod_cast h2
  have h' : (tStep^[s.length] x : ℤ) * y = (tStep^[s.length] y : ℤ) * x := by exact_mod_cast h
  zify
  linear_combination -(y : ℤ) * h1' + (x : ℤ) * h2' + (2 : ℤ) ^ s.length * h'

/-- Remark 2.8 (ties), the divisibility: a start x tying y (as in `tie_rho`, y > 0) is a multiple of
    u = y / gcd(y, rho t). So the ties of the best c* are among the multiples of c*/gcd(c*, rho*)
    below the window (`window`, non-strict). -/
theorem tie_dvd {s t : List Bool} (hl : s.length = t.length) (ho : order s = order t) {x y : ℕ}
    (hx : tBits x s.length = s) (hy : tBits y t.length = t) (hy0 : 0 < y)
    (h : tStep^[s.length] x * y = tStep^[s.length] y * x) :
    y / Nat.gcd y (rho t) ∣ x := by
  have hr := tie_rho hl ho hx hy h
  have hg : 0 < Nat.gcd y (rho t) := Nat.gcd_pos_of_pos_left _ hy0
  have hc := Nat.coprime_div_gcd_div_gcd hg
  apply hc.dvd_of_dvd_mul_left
  apply Nat.dvd_of_mul_dvd_mul_right hg
  rw [Nat.div_mul_cancel (Nat.gcd_dvd_left y (rho t)), mul_right_comm,
    Nat.div_mul_cancel (Nat.gcd_dvd_right y (rho t)), ← hr]
  exact Dvd.intro_left _ rfl

end BestOfOrder
