-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TBlockRecord
import AcceleratedCollatz.TSmoothNextQ

/-!
  The 3-smooth numbers 2^j 3^i in increasing order (paper fig:smooth), the q = 3 case of
  `TSmoothNextQ`. From 2^j 3^i the next one is reached by the upper step, times
  2^p2(b) / 3^b for the last upper record Order b ≤ i, or by the lower step, times
  3^a / 2^(p2(a) - 1) for the last lower record Order a with p2(a) - 1 ≤ j: both give a
  larger number (`lt_upperStep`, `lt_lowerStep`), and every larger 2^j' 3^i' is at least
  one of the two (`smooth_next`); from a power of 3 only the upper step is there
  (`smooth_next_of_pow_three`). The exponents are written i = b + r and
  j + 1 = p2(a) + s.
-/

namespace AcceleratedCollatz

/-- The upper step leads to a larger number. -/
theorem lt_upperStep (j b r : ℕ) : 2 ^ j * 3 ^ (b + r) < 2 ^ (j + p2_of b) * 3 ^ r :=
  lt_upperStepQ le_rfl j b r

/-- The lower step leads to a larger number. -/
theorem lt_lowerStep {a j s : ℕ} (ha1 : 1 ≤ a) (hj : j + 1 = p2_of a + s) (i : ℕ) :
    2 ^ j * 3 ^ i < 2 ^ s * 3 ^ (i + a) :=
  lt_lowerStepQ (by decide) le_rfl ha1 hj i

/-- The next 3-smooth number after 2^j 3^(b + r): every larger 2^j' 3^i' is at least the
    upper step or at least the lower step. Here b is the last upper record Order up to
    i = b + r, and a the last lower record Order with p2(a) ≤ j + 1 = p2(a) + s. -/
theorem smooth_next {a b r s j : ℕ} (hj : j + 1 = p2_of a + s) (hRb : UpperRecord b)
    (hnb : ∀ x, b < x → x ≤ b + r → ¬UpperRecord x) (hRa : LowerRecord a)
    (hna : ∀ x, a < x → p2_of x ≤ j + 1 → ¬LowerRecord x) {j' i' : ℕ}
    (hlt : 2 ^ j * 3 ^ (b + r) < 2 ^ j' * 3 ^ i') :
    2 ^ (j + p2_of b) * 3 ^ r ≤ 2 ^ j' * 3 ^ i' ∨
      2 ^ s * 3 ^ (b + r + a) ≤ 2 ^ j' * 3 ^ i' :=
  smoothQ_next (by decide) le_rfl hj hRb hnb hRa hna hlt

/-- From a power of 3 the next 3-smooth number is the upper step. -/
theorem smooth_next_of_pow_three {b r : ℕ} (hRb : UpperRecord b)
    (hnb : ∀ x, b < x → x ≤ b + r → ¬UpperRecord x) {j' i' : ℕ}
    (hlt : 3 ^ (b + r) < 2 ^ j' * 3 ^ i') : 2 ^ p2_of b * 3 ^ r ≤ 2 ^ j' * 3 ^ i' := by
  have hj : 0 + 1 < p2Q 3 1 := by
    unfold p2Q
    rw [Nat.log_eq_of_pow_le_of_lt_pow (m := 1) (by norm_num) (by norm_num)]
    norm_num
  have hlt' : 2 ^ 0 * 3 ^ (b + r) < 2 ^ j' * 3 ^ i' := by
    rw [pow_zero, one_mul]
    exact hlt
  have h := smoothQ_next_of_lt (by decide) le_rfl hj hRb hnb hlt'
  rw [Nat.zero_add] at h
  exact h

end AcceleratedCollatz
