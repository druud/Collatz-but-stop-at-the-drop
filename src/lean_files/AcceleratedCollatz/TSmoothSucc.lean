-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TSmoothNext
import AcceleratedCollatz.TSmoothSuccQ

/-!
  Neighbouring 3-smooth numbers, the q = 3 case of TSmoothSuccQ: the larger one is the upper
  step or the lower step of the smaller (`smooth_succ`); after a power of 3 it is the
  upper step (`smooth_succ_of_pow_three`). So, walking up through the 3-smooth numbers,
  for instance from 3^n to 2^p2(n), the exponent of 3 goes from i = b + r to r, minus the
  last upper record Order b ≤ i, or to i + a, plus the last lower record Order a with
  p2(a) ≤ j + 1.
-/

namespace AcceleratedCollatz

/-- The 3-smooth number after 2^j 3^(b + r), when nothing lies between: the upper step
    2^(j + p2(b)) 3^r or the lower step 2^s 3^(b + r + a). -/
theorem smooth_succ {a b r s j : ℕ} (ha1 : 1 ≤ a) (hj : j + 1 = p2_of a + s)
    (hRb : UpperRecord b) (hnb : ∀ x, b < x → x ≤ b + r → ¬UpperRecord x)
    (hRa : LowerRecord a) (hna : ∀ x, a < x → p2_of x ≤ j + 1 → ¬LowerRecord x) {j' i' : ℕ}
    (hlt : 2 ^ j * 3 ^ (b + r) < 2 ^ j' * 3 ^ i')
    (hnone : ∀ j'' i'', 2 ^ j * 3 ^ (b + r) < 2 ^ j'' * 3 ^ i'' →
      ¬2 ^ j'' * 3 ^ i'' < 2 ^ j' * 3 ^ i') :
    (j' = j + p2_of b ∧ i' = r) ∨ (j' = s ∧ i' = b + r + a) :=
  smoothQ_succ (by decide) le_rfl ha1 hj hRb hnb hRa hna hlt hnone

/-- The 3-smooth number after 3^(b + r), when nothing lies between: the upper step
    2^p2(b) 3^r. -/
theorem smooth_succ_of_pow_three {b r : ℕ} (hRb : UpperRecord b)
    (hnb : ∀ x, b < x → x ≤ b + r → ¬UpperRecord x) {j' i' : ℕ}
    (hlt : 3 ^ (b + r) < 2 ^ j' * 3 ^ i')
    (hnone : ∀ j'' i'', 3 ^ (b + r) < 2 ^ j'' * 3 ^ i'' →
      ¬2 ^ j'' * 3 ^ i'' < 2 ^ j' * 3 ^ i') :
    j' = p2_of b ∧ i' = r := by
  have hc : Nat.Coprime 2 3 := by
    decide
  have h := smooth_next_of_pow_three hRb hnb hlt
  have he : 2 ^ p2_of b * 3 ^ r = 2 ^ j' * 3 ^ i' := by
    by_contra hne
    have hu : 3 ^ (b + r) < 2 ^ p2_of b * 3 ^ r := by
      have h0 := lt_upperStep 0 b r
      rw [pow_zero, Nat.one_mul, Nat.zero_add] at h0
      exact h0
    exact hnone _ _ hu (lt_of_le_of_ne h hne)
  obtain ⟨h1, h2⟩ := pow_mul_pow_inj hc (by norm_num) (by norm_num) he
  exact ⟨h1.symm, h2.symm⟩

end AcceleratedCollatz
