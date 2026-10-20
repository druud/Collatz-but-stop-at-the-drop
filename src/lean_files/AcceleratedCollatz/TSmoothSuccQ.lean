-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TSmoothNextQ
import AcceleratedCollatz.TSmoothPlaceQ

/-!
  Neighbouring numbers 2^j q^i (odd q ≥ 3): the larger one is the upper step or the lower
  step of the smaller (`smoothQ_succ`); when no lower record Order fits (j + 1 < p2Q(1),
  among them the powers of q) it is the upper step (`smoothQ_succ_of_lt`). So, walking up
  through the numbers 2^j q^i, the exponent of q goes from i = b + r to r, minus the last
  upper record Order b ≤ i, or to i + a, plus the last lower record Order a with
  p2Q(a) ≤ j + 1.
-/

namespace AcceleratedCollatz

variable {q : ℕ}

/-- The number after 2^j q^(b + r), when nothing lies between: the upper step
    2^(j + p2Q(b)) q^r or the lower step 2^s q^(b + r + a). -/
theorem smoothQ_succ (hodd : Odd q) (hq : 3 ≤ q) {a b r s j : ℕ} (ha1 : 1 ≤ a)
    (hj : j + 1 = p2Q q a + s) (hRb : UpperRecordQ q b)
    (hnb : ∀ x, b < x → x ≤ b + r → ¬UpperRecordQ q x) (hRa : LowerRecordQ q a)
    (hna : ∀ x, a < x → p2Q q x ≤ j + 1 → ¬LowerRecordQ q x) {j' i' : ℕ}
    (hlt : 2 ^ j * q ^ (b + r) < 2 ^ j' * q ^ i')
    (hnone : ∀ j'' i'', 2 ^ j * q ^ (b + r) < 2 ^ j'' * q ^ i'' →
      ¬2 ^ j'' * q ^ i'' < 2 ^ j' * q ^ i') :
    (j' = j + p2Q q b ∧ i' = r) ∨ (j' = s ∧ i' = b + r + a) := by
  have hc : Nat.Coprime 2 q := Nat.coprime_two_left.mpr hodd
  rcases smoothQ_next hodd hq hj hRb hnb hRa hna hlt with h | h
  · left
    have he : 2 ^ (j + p2Q q b) * q ^ r = 2 ^ j' * q ^ i' := by
      by_contra hne
      exact hnone _ _ (lt_upperStepQ hq j b r) (lt_of_le_of_ne h hne)
    obtain ⟨h1, h2⟩ := pow_mul_pow_inj hc (by norm_num) (by omega) he
    exact ⟨h1.symm, h2.symm⟩
  · right
    have he : 2 ^ s * q ^ (b + r + a) = 2 ^ j' * q ^ i' := by
      by_contra hne
      exact hnone _ _ (lt_lowerStepQ hodd hq ha1 hj (b + r)) (lt_of_le_of_ne h hne)
    obtain ⟨h1, h2⟩ := pow_mul_pow_inj hc (by norm_num) (by omega) he
    exact ⟨h1.symm, h2.symm⟩

/-- When no lower record Order fits (j + 1 < p2Q(1)), the number after 2^j q^(b + r), when
    nothing lies between, is the upper step 2^(j + p2Q(b)) q^r. -/
theorem smoothQ_succ_of_lt (hodd : Odd q) (hq : 3 ≤ q) {b r j : ℕ} (hj : j + 1 < p2Q q 1)
    (hRb : UpperRecordQ q b) (hnb : ∀ x, b < x → x ≤ b + r → ¬UpperRecordQ q x) {j' i' : ℕ}
    (hlt : 2 ^ j * q ^ (b + r) < 2 ^ j' * q ^ i')
    (hnone : ∀ j'' i'', 2 ^ j * q ^ (b + r) < 2 ^ j'' * q ^ i'' →
      ¬2 ^ j'' * q ^ i'' < 2 ^ j' * q ^ i') :
    j' = j + p2Q q b ∧ i' = r := by
  have hc : Nat.Coprime 2 q := Nat.coprime_two_left.mpr hodd
  have h := smoothQ_next_of_lt hodd hq hj hRb hnb hlt
  have he : 2 ^ (j + p2Q q b) * q ^ r = 2 ^ j' * q ^ i' := by
    by_contra hne
    exact hnone _ _ (lt_upperStepQ hq j b r) (lt_of_le_of_ne h hne)
  obtain ⟨h1, h2⟩ := pow_mul_pow_inj hc (by norm_num) (by omega) he
  exact ⟨h1.symm, h2.symm⟩

end AcceleratedCollatz
