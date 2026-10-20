-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.Numlib
import Mathlib.Tactic.FieldSimp

/-!
  The point of a number: its binary digits read from the lowest one, a digit 1 mapping y
  to y + 1 and a digit 0 mapping y to 1/(y + 1), from the point 1 of the number 0
  (`markerPoint`). These are the two maps of the trees of Hanna, Czyz and Self and of
  Yu-Ting (K. Ryde, Trees of Rationals), taken low to high, at the node whose number is
  the complement of x with one more digit on top. An odd x is h 2^(t + 1) + 2^t - 1 with
  t ≥ 1 its number of trailing 1s, the block 0 1^t that the fast map removes; its point
  is t + 1/(y + 1) with y the point of h (`markerPoint_ht`), and t + 1 when h = 0
  (`markerPoint_mersenne`). So the lowest run of 1s is the quotient t of the continued
  fraction, and every further run of u 1s, with the 0 below it, is a quotient u + 1, a
  marker and u digits; the highest run counts u + 2. The point of x lies between t and
  t + 1 (`lt_markerPoint_ht`, `markerPoint_ht_lt`), unless x is 2^t - 1.
-/

namespace AcceleratedCollatz

/-- The point of a number by its binary digits, lowest first: 1 for the number 0; a digit
    1 maps y to y + 1, a digit 0 maps y to 1/(y + 1). -/
def markerPoint (n : ℕ) : ℚ :=
  if h : n = 0 then 1
  else if n % 2 = 1 then markerPoint (n / 2) + 1
  else 1 / (markerPoint (n / 2) + 1)
decreasing_by
  · omega
  · omega

theorem markerPoint_zero : markerPoint 0 = 1 := by
  rw [markerPoint]
  rfl

/-- A lowest digit 1. -/
theorem markerPoint_bit_one (n : ℕ) : markerPoint (2 * n + 1) = markerPoint n + 1 := by
  have h1 : (2 * n + 1) % 2 = 1 := by
    omega
  have h2 : (2 * n + 1) / 2 = n := by
    omega
  rw [markerPoint, dite_eq_right (Nat.succ_ne_zero _), h1, h2]
  rfl

/-- A lowest digit 0, of a number that is not 0. -/
theorem markerPoint_bit_zero {n : ℕ} (hn : 1 ≤ n) :
    markerPoint (2 * n) = 1 / (markerPoint n + 1) := by
  have h0 : 2 * n ≠ 0 := by
    omega
  have h1 : ¬(2 * n) % 2 = 1 := by
    omega
  have h2 : 2 * n / 2 = n := by
    omega
  rw [markerPoint, dite_eq_right h0, h2]
  exact ite_eq_right h1

theorem markerPoint_pos (n : ℕ) : 0 < markerPoint n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · rw [markerPoint_zero]
      exact one_pos
    · have hlt : n / 2 < n := by
        omega
      have hy := ih (n / 2) hlt
      rcases Nat.mod_two_eq_zero_or_one n with h | h
      · have hn : n = 2 * (n / 2) := by
          omega
        rw [hn, markerPoint_bit_zero (by omega)]
        exact div_pos one_pos (by linarith)
      · have hn : n = 2 * (n / 2) + 1 := by
          omega
        rw [hn, markerPoint_bit_one]
        linarith

/-- t digits 1 below the digits of m add t to the point of m. -/
theorem markerPoint_ones (t m : ℕ) :
    markerPoint (2 ^ t * (m + 1) - 1) = t + markerPoint m := by
  induction t with
  | zero =>
    rw [pow_zero, one_mul, Nat.add_sub_cancel, Nat.cast_zero, zero_add]
  | succ t ih =>
    have hpos : 1 ≤ 2 ^ t * (m + 1) := Nat.mul_pos (Nat.two_pow_pos t) (Nat.succ_pos m)
    have hmul : 2 ^ (t + 1) * (m + 1) = 2 * (2 ^ t * (m + 1)) := by
      ring
    have hx : 2 ^ (t + 1) * (m + 1) - 1 = 2 * (2 ^ t * (m + 1) - 1) + 1 := by
      omega
    rw [hx, markerPoint_bit_one, ih]
    push_cast
    ring

/-- The point of 2^t - 1, the number of t digits 1, is t + 1. -/
theorem markerPoint_mersenne (t : ℕ) : markerPoint (2 ^ t - 1) = t + 1 := by
  have h := markerPoint_ones t 0
  rw [Nat.zero_add, mul_one, markerPoint_zero] at h
  exact h

/-- The point of h 2^(t + 1) + 2^t - 1, the digits of h ≥ 1 above a 0 and t digits 1: t and
    then the quotient that the point of h gives with 1 more. -/
theorem markerPoint_ht {h : ℕ} (hh : 1 ≤ h) (t : ℕ) :
    markerPoint (h * 2 ^ (t + 1) + 2 ^ t - 1) = t + 1 / (markerPoint h + 1) := by
  have hx : h * 2 ^ (t + 1) + 2 ^ t = 2 ^ t * (2 * h + 1) := by
    rw [pow_succ]
    ring
  rw [hx, markerPoint_ones, markerPoint_bit_zero hh]

/-- For h ≥ 1 the point of h 2^(t + 1) + 2^t - 1 is above t. -/
theorem lt_markerPoint_ht {h : ℕ} (hh : 1 ≤ h) (t : ℕ) :
    (t : ℚ) < markerPoint (h * 2 ^ (t + 1) + 2 ^ t - 1) := by
  have hy := markerPoint_pos h
  have hpos : (0 : ℚ) < 1 / (markerPoint h + 1) := div_pos one_pos (by linarith)
  rw [markerPoint_ht hh]
  linarith

/-- For h ≥ 1 the point of h 2^(t + 1) + 2^t - 1 is below t + 1. -/
theorem markerPoint_ht_lt {h : ℕ} (hh : 1 ≤ h) (t : ℕ) :
    markerPoint (h * 2 ^ (t + 1) + 2 ^ t - 1) < t + 1 := by
  have hy := markerPoint_pos h
  have hlt : 1 / (markerPoint h + 1) < 1 := by
    rw [div_lt_iff₀ (by linarith)]
    linarith
  rw [markerPoint_ht hh]
  linarith

/-- 27 = 11011 in binary, runs 2 and 2: the point is 2 + 1/4 = 9/4. -/
example : markerPoint 27 = 9 / 4 := by
  have h := markerPoint_ht (h := 3) (by omega) 2
  have h3 := markerPoint_mersenne 2
  norm_num at h h3
  rw [h, h3]
  norm_num

end AcceleratedCollatz
