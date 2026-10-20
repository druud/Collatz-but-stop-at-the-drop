-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TRecordGapQ

/-!
  The numbers 2^j q^i in increasing order (odd q ≥ 3; paper fig:smooth for q = 3). From
  2^j q^i the next one is reached by one of two steps: times 2^p2Q(b) / q^b for the last
  upper record Order b ≤ i, or times q^a / 2^(p2Q(a) - 1) for the last lower record
  Order a with p2Q(a) - 1 ≤ j. Both give a larger number (`lt_upperStepQ`,
  `lt_lowerStepQ`), and every larger 2^j' q^i' is at least one of the two
  (`smoothQ_next`); when no lower record Order fits, it is at least the first
  (`smoothQ_next_of_lt`). The exponents are written i = b + r and
  j + 1 = p2Q(a) + s.
-/

namespace AcceleratedCollatz

variable {q : ℕ}

/-- Up to i, the last upper record Order b has the largest block factor, as cross
    products. -/
theorem upperRecordQ_best (hodd : Odd q) (hq : 3 ≤ q) {b i : ℕ} (hRb : UpperRecordQ q b)
    (hnb : ∀ x, b < x → x ≤ i → ¬UpperRecordQ q x) {d : ℕ} (hd : d ≤ i) :
    q ^ d * 2 ^ p2Q q b ≤ q ^ b * 2 ^ p2Q q d := by
  by_contra hlt
  push Not at hlt
  have hf : blockFactorQ q b < blockFactorQ q d := (blockFactorQ_lt_iff q b d).mpr hlt
  rcases Nat.lt_trichotomy d b with hdb | hdb | hdb
  · rcases Nat.eq_zero_or_pos d with hd0 | hd1
    · rw [hd0, p2Q_zero, pow_zero, pow_one, one_mul] at hlt
      have hlow := p2Q_spec_lower hq b
      have hp := one_le_p2Q q b
      have hsplit : 2 ^ p2Q q b = 2 ^ (p2Q q b - 1) * 2 := by
        rw [← pow_succ, Nat.sub_add_cancel hp]
      omega
    · have := (upperRecordQ_iff_blockFactorQ hodd hq b).mp hRb d hd1 hdb
      exact lt_asymm hf this
  · rw [hdb] at hf
    exact lt_irrefl _ hf
  · have hnb' : ∀ x, b < x → x < i + 1 → ¬UpperRecordQ q x := fun x hbx hxi => hnb x hbx (by omega)
    exact not_blockFactorQ_lt_of_upperRecordQ hodd hq hRb hnb' hdb (by omega) hf

/-- Among the Orders d ≥ 1 with p2Q(d) ≤ j + 1, the last lower record Order a has the
    smallest block factor, as cross products. -/
theorem lowerRecordQ_best (hq : 3 ≤ q) {a j : ℕ} (hRa : LowerRecordQ q a)
    (hna : ∀ x, a < x → p2Q q x ≤ j + 1 → ¬LowerRecordQ q x) {d : ℕ} (hd1 : 1 ≤ d)
    (hdj : p2Q q d ≤ j + 1) : q ^ a * 2 ^ p2Q q d ≤ q ^ d * 2 ^ p2Q q a := by
  by_contra hlt
  push Not at hlt
  have hf : blockFactorQ q d < blockFactorQ q a := (blockFactorQ_lt_iff q d a).mpr hlt
  rcases Nat.lt_trichotomy d a with hda | hda | hda
  · have := (lowerRecordQ_iff_blockFactorQ hq a).mp hRa d hd1 hda
    exact lt_asymm hf this
  · rw [hda] at hf
    exact lt_irrefl _ hf
  · have hna' : ∀ x, a < x → x < d + 1 → ¬LowerRecordQ q x := by
      intro x hax hxd
      have := p2Q_mono hq (i := x) (n := d) (by omega)
      exact hna x hax (by omega)
    exact not_blockFactorQ_lt_of_lowerRecordQ hq hRa hna' hda (by omega) hf

/-- The upper step leads to a larger number. -/
theorem lt_upperStepQ (hq : 3 ≤ q) (j b r : ℕ) :
    2 ^ j * q ^ (b + r) < 2 ^ (j + p2Q q b) * q ^ r := by
  have h := p2Q_spec hq b
  have hpos : 0 < 2 ^ j * q ^ r := by positivity
  calc 2 ^ j * q ^ (b + r) = 2 ^ j * q ^ r * q ^ b := by ring
    _ < 2 ^ j * q ^ r * 2 ^ p2Q q b := Nat.mul_lt_mul_of_pos_left h hpos
    _ = 2 ^ (j + p2Q q b) * q ^ r := by ring

/-- The lower step leads to a larger number. -/
theorem lt_lowerStepQ (hodd : Odd q) (hq : 3 ≤ q) {a j s : ℕ} (ha1 : 1 ≤ a)
    (hj : j + 1 = p2Q q a + s) (i : ℕ) : 2 ^ j * q ^ i < 2 ^ s * q ^ (i + a) := by
  have h : 2 ^ (p2Q q a - 1) < q ^ a :=
    (two_pow_lt_q_pow_iff hodd hq ha1).mpr (by
      have := one_le_p2Q q a
      omega)
  have hjs : j = s + (p2Q q a - 1) := by
    have := one_le_p2Q q a
    omega
  have hpos : 0 < 2 ^ s * q ^ i := by positivity
  calc 2 ^ j * q ^ i = 2 ^ s * q ^ i * 2 ^ (p2Q q a - 1) := by
        rw [hjs]
        ring
    _ < 2 ^ s * q ^ i * q ^ a := Nat.mul_lt_mul_of_pos_left h hpos
    _ = 2 ^ s * q ^ (i + a) := by ring

/-- The upper step at most doubles the number. -/
theorem upperStepQ_le_two_mul (hq : 3 ≤ q) (j b r : ℕ) :
    2 ^ (j + p2Q q b) * q ^ r ≤ 2 * (2 ^ j * q ^ (b + r)) := by
  have hlow := p2Q_spec_lower hq b
  have hp := one_le_p2Q q b
  have hsplit : 2 ^ p2Q q b = 2 ^ (p2Q q b - 1) * 2 := by
    rw [← pow_succ, Nat.sub_add_cancel hp]
  calc 2 ^ (j + p2Q q b) * q ^ r = 2 ^ j * q ^ r * 2 * 2 ^ (p2Q q b - 1) := by
        rw [pow_add, hsplit]
        ring
    _ ≤ 2 ^ j * q ^ r * 2 * q ^ b := Nat.mul_le_mul_left _ hlow
    _ = 2 * (2 ^ j * q ^ (b + r)) := by ring

/-- A number 2^j' q^i' above 2^j q^(b + r) is at least the upper step from it, or it is
    a lower step from it: q^d / 2^(p2Q(d) - 1) times it, for some d ≥ 1 with
    p2Q(d) ≤ j + 1. -/
theorem smoothQ_step (hodd : Odd q) (hq : 3 ≤ q) {b r j : ℕ} (hRb : UpperRecordQ q b)
    (hnb : ∀ x, b < x → x ≤ b + r → ¬UpperRecordQ q x) {j' i' : ℕ}
    (hlt : 2 ^ j * q ^ (b + r) < 2 ^ j' * q ^ i') :
    2 ^ (j + p2Q q b) * q ^ r ≤ 2 ^ j' * q ^ i' ∨
      ∃ d, 1 ≤ d ∧ i' = b + r + d ∧ j + 1 = j' + p2Q q d := by
  have hq0 : 0 < q := by omega
  rcases Nat.lt_or_ge (b + r) i' with hi | hi
  rotate_left
  · left
    obtain ⟨d, hd⟩ : ∃ d, b + r = i' + d := ⟨b + r - i', by omega⟩
    have hqi : 0 < q ^ i' := by positivity
    have h1 : 2 ^ j * q ^ d < 2 ^ j' := by
      rw [hd] at hlt
      have h : 2 ^ j * q ^ d * q ^ i' < 2 ^ j' * q ^ i' := by
        calc 2 ^ j * q ^ d * q ^ i' = 2 ^ j * q ^ (i' + d) := by ring
          _ < 2 ^ j' * q ^ i' := hlt
      exact Nat.lt_of_mul_lt_mul_right h
    have hjj : j < j' := by
      by_contra hge
      push Not at hge
      have h2 : 2 ^ j' ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hge
      have h3 : 2 ^ j ≤ 2 ^ j * q ^ d := Nat.le_mul_of_pos_right _ (by positivity)
      omega
    obtain ⟨e, he⟩ : ∃ e, j' = j + e := ⟨j' - j, by omega⟩
    have h4 : q ^ d < 2 ^ e := by
      rw [he, pow_add] at h1
      exact Nat.lt_of_mul_lt_mul_left h1
    have hpe : p2Q q d ≤ e := (q_pow_lt_two_pow_iff hq).mp h4
    have hU := upperRecordQ_best hodd hq hRb hnb (d := d) (by omega)
    have h5 : q ^ d * 2 ^ p2Q q b ≤ q ^ b * 2 ^ e :=
      hU.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hpe))
    have hpow : q ^ r * q ^ b = q ^ i' * q ^ d := by
      rw [← pow_add, ← pow_add]
      congr 1
      omega
    have h6 : 2 ^ (j + p2Q q b) * q ^ r * q ^ b ≤ 2 ^ j' * q ^ i' * q ^ b := by
      calc 2 ^ (j + p2Q q b) * q ^ r * q ^ b = 2 ^ j * 2 ^ p2Q q b * (q ^ r * q ^ b) := by ring
        _ = 2 ^ j * 2 ^ p2Q q b * (q ^ i' * q ^ d) := by rw [hpow]
        _ = 2 ^ j * q ^ i' * (q ^ d * 2 ^ p2Q q b) := by ring
        _ ≤ 2 ^ j * q ^ i' * (q ^ b * 2 ^ e) := Nat.mul_le_mul_left _ h5
        _ = 2 ^ j' * q ^ i' * q ^ b := by
          rw [he]
          ring
    exact Nat.le_of_mul_le_mul_right h6 (by positivity)
  · obtain ⟨d, hd1, hd⟩ : ∃ d, 1 ≤ d ∧ i' = b + r + d := ⟨i' - (b + r), by omega, by omega⟩
    have hc1 := upperStepQ_le_two_mul hq j b r
    have hqd : 2 ≤ q ^ d := by
      have h : q ^ 1 ≤ q ^ d := Nat.pow_le_pow_right hq0 hd1
      rw [pow_one] at h
      omega
    rcases Nat.lt_or_ge j' j with hjj | hjj
    rotate_left
    · left
      have h2 : 2 * (2 ^ j * q ^ (b + r)) ≤ 2 ^ j' * q ^ i' := by
        have hp : 2 ^ j ≤ 2 ^ j' := Nat.pow_le_pow_right (by norm_num) hjj
        calc 2 * (2 ^ j * q ^ (b + r)) = 2 ^ j * q ^ (b + r) * 2 := by ring
          _ ≤ 2 ^ j' * q ^ (b + r) * q ^ d :=
            Nat.mul_le_mul (Nat.mul_le_mul_right _ hp) hqd
          _ = 2 ^ j' * q ^ i' := by
            rw [hd]
            ring
      exact hc1.trans h2
    · obtain ⟨e, he⟩ : ∃ e, j = j' + e := ⟨j - j', by omega⟩
      have h1 : 2 ^ e < q ^ d := by
        rw [he, hd] at hlt
        have hpos : 0 < 2 ^ j' * q ^ (b + r) := by positivity
        have h : 2 ^ j' * q ^ (b + r) * 2 ^ e < 2 ^ j' * q ^ (b + r) * q ^ d := by
          calc 2 ^ j' * q ^ (b + r) * 2 ^ e = 2 ^ (j' + e) * q ^ (b + r) := by ring
            _ < 2 ^ j' * q ^ (b + r + d) := hlt
            _ = 2 ^ j' * q ^ (b + r) * q ^ d := by ring
        exact Nat.lt_of_mul_lt_mul_left h
      have hep : e < p2Q q d := (two_pow_lt_q_pow_iff hodd hq hd1).mp h1
      rcases Nat.eq_or_lt_of_le (Nat.succ_le_of_lt hep) with heq | hlt2
      · right
        exact ⟨d, hd1, hd, by omega⟩
      · left
        have hlow := p2Q_spec_lower hq d
        have h3 : 2 ^ (e + 1) ≤ q ^ d :=
          (Nat.pow_le_pow_right (by norm_num) (by omega)).trans hlow
        have h2 : 2 * (2 ^ j * q ^ (b + r)) ≤ 2 ^ j' * q ^ i' := by
          calc 2 * (2 ^ j * q ^ (b + r)) = 2 ^ j' * q ^ (b + r) * 2 ^ (e + 1) := by
                rw [he]
                ring
            _ ≤ 2 ^ j' * q ^ (b + r) * q ^ d := Nat.mul_le_mul_left _ h3
            _ = 2 ^ j' * q ^ i' := by
              rw [hd]
              ring
        exact hc1.trans h2

/-- The next number after 2^j q^(b + r): every larger 2^j' q^i' is at least the upper
    step or at least the lower step. Here b is the last upper record Order up to
    i = b + r, and a the last lower record Order with p2Q(a) ≤ j + 1 = p2Q(a) + s. -/
theorem smoothQ_next (hodd : Odd q) (hq : 3 ≤ q) {a b r s j : ℕ}
    (hj : j + 1 = p2Q q a + s) (hRb : UpperRecordQ q b)
    (hnb : ∀ x, b < x → x ≤ b + r → ¬UpperRecordQ q x) (hRa : LowerRecordQ q a)
    (hna : ∀ x, a < x → p2Q q x ≤ j + 1 → ¬LowerRecordQ q x) {j' i' : ℕ}
    (hlt : 2 ^ j * q ^ (b + r) < 2 ^ j' * q ^ i') :
    2 ^ (j + p2Q q b) * q ^ r ≤ 2 ^ j' * q ^ i' ∨
      2 ^ s * q ^ (b + r + a) ≤ 2 ^ j' * q ^ i' := by
  rcases smoothQ_step hodd hq hRb hnb hlt with h | ⟨d, hd1, hd, hjd⟩
  · exact Or.inl h
  · right
    have hL := lowerRecordQ_best hq hRa hna hd1 (by omega)
    have hexp : 2 ^ s * 2 ^ p2Q q a = 2 ^ j' * 2 ^ p2Q q d := by
      rw [← pow_add, ← pow_add]
      congr 1
      omega
    have h : 2 ^ s * q ^ (b + r + a) * 2 ^ p2Q q d ≤ 2 ^ j' * q ^ i' * 2 ^ p2Q q d := by
      calc 2 ^ s * q ^ (b + r + a) * 2 ^ p2Q q d
          = 2 ^ s * q ^ (b + r) * (q ^ a * 2 ^ p2Q q d) := by ring
        _ ≤ 2 ^ s * q ^ (b + r) * (q ^ d * 2 ^ p2Q q a) := Nat.mul_le_mul_left _ hL
        _ = 2 ^ s * 2 ^ p2Q q a * q ^ (b + r + d) := by ring
        _ = 2 ^ j' * 2 ^ p2Q q d * q ^ (b + r + d) := by rw [hexp]
        _ = 2 ^ j' * q ^ i' * 2 ^ p2Q q d := by
          rw [hd]
          ring
    exact Nat.le_of_mul_le_mul_right h (by positivity)

/-- When no lower step fits (j + 1 < p2Q(1)), every larger 2^j' q^i' is at least the
    upper step. -/
theorem smoothQ_next_of_lt (hodd : Odd q) (hq : 3 ≤ q) {b r j : ℕ} (hj : j + 1 < p2Q q 1)
    (hRb : UpperRecordQ q b) (hnb : ∀ x, b < x → x ≤ b + r → ¬UpperRecordQ q x) {j' i' : ℕ}
    (hlt : 2 ^ j * q ^ (b + r) < 2 ^ j' * q ^ i') :
    2 ^ (j + p2Q q b) * q ^ r ≤ 2 ^ j' * q ^ i' := by
  rcases smoothQ_step hodd hq hRb hnb hlt with h | ⟨d, hd1, _, hjd⟩
  · exact h
  · have := p2Q_mono hq hd1
    omega

end AcceleratedCollatz
