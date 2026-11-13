-- SPDX-License-Identifier: MIT
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

/-!
  Levi ben Gershon (Gersonides, Leo Hebraeus), De numeris harmonicis, 1343: a power of 2
  and a power of 3 differ by 1 only in 1, 2 (2^1 - 3^0), 3, 4 (2^2 - 3^1), 2, 3 (3^1 - 2^1)
  and 8, 9 (3^2 - 2^3) (B47, 13 Nov 2026; the d = 1 blocks 0 and 10 of paper 3, Ch. 4).
  The proof: powers of 3 are 1 or 3 mod 8, and 3^(2k) - 1 = (3^k - 1)(3^k + 1) is a power
  of 2 only when the two factors are 2 and 4.
-/

namespace AcceleratedCollatz

/-- 3^b mod 8 is 1 for even b and 3 for odd b. -/
theorem three_pow_mod_eight_ite (b : ℕ) : 3 ^ b % 8 = if b % 2 = 0 then 1 else 3 := by
  induction b with
  | zero => rfl
  | succ b ih =>
    rw [pow_succ, Nat.mul_mod, ih]
    rcases Nat.mod_two_eq_zero_or_one b with h | h
    · have : (b + 1) % 2 = 1 := by omega
      simp [h, this]
    · have : (b + 1) % 2 = 0 := by omega
      simp [h, this]

/-- 3^b + 1 = 2^a only for (a, b) = (1, 0) and (2, 1). -/
theorem three_pow_add_one_eq_two_pow {a b : ℕ} (h : 3 ^ b + 1 = 2 ^ a) :
    (a = 1 ∧ b = 0) ∨ (a = 2 ∧ b = 1) := by
  have hm := three_pow_mod_eight_ite b
  rcases Nat.lt_or_ge a 3 with ha | ha
  · interval_cases a
    · simp at h
    · have h1 : b = 0 := by simpa using h
      exact Or.inl ⟨rfl, h1⟩
    · simp at h
      have h3 : 3 ^ b = 3 ^ 1 := by omega
      exact Or.inr ⟨rfl, Nat.pow_right_injective (a := 3) (by norm_num) h3⟩
  · have h8 : 2 ^ a % 8 = 0 := by
      have : 2 ^ a = 2 ^ (a - 3) * 8 := by
        rw [show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_add]
        congr 1
        omega
      rw [this, Nat.mul_mod_left]
    split_ifs at hm <;> omega

/-- A divisor of 2^a is a power of 2. -/
theorem eq_two_pow_of_dvd {x a : ℕ} (h : x ∣ 2 ^ a) : ∃ i, x = 2 ^ i := by
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h
  exact ⟨i, hi⟩

/-- Two powers of 2 two apart are 2 and 4. -/
theorem two_pow_add_two_eq_two_pow {i j : ℕ} (h : 2 ^ i + 2 = 2 ^ j) : i = 1 ∧ j = 2 := by
  rcases Nat.lt_or_ge i 2 with hi | hi
  · interval_cases i
    · simp at h
      have : 2 ^ j % 2 = 1 := by omega
      rcases j with _ | j
      · simp at h
      · rw [pow_succ] at this
        omega
    · simp at h
      exact ⟨rfl, Nat.pow_right_injective (le_refl 2) (by simpa using h.symm)⟩
  · have h4 : 2 ^ i % 4 = 0 := by
      have : 2 ^ i = 2 ^ (i - 2) * 4 := by
        rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]
        congr 1
        omega
      rw [this, Nat.mul_mod_left]
    have hj : 2 < j := by
      by_contra hj
      push Not at hj
      have : 2 ^ j ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hj
      have : 2 ^ 2 ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) hi
      omega
    have h4' : 2 ^ j % 4 = 0 := by
      have : 2 ^ j = 2 ^ (j - 2) * 4 := by
        rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]
        congr 1
        omega
      rw [this, Nat.mul_mod_left]
    omega

/-- 2^a + 1 = 3^b only for (a, b) = (1, 1) and (3, 2). -/
theorem two_pow_add_one_eq_three_pow {a b : ℕ} (h : 2 ^ a + 1 = 3 ^ b) :
    (a = 1 ∧ b = 1) ∨ (a = 3 ∧ b = 2) := by
  have hm := three_pow_mod_eight_ite b
  rcases Nat.lt_or_ge a 3 with ha | ha
  · interval_cases a
    · simp at h
      have : 3 ^ b % 2 = 1 := Nat.odd_iff.mp (Odd.pow (by decide))
      omega
    · simp at h
      have h3 : 3 ^ b = 3 ^ 1 := by omega
      exact Or.inl ⟨rfl, Nat.pow_right_injective (a := 3) (by norm_num) h3⟩
    · simp at h
      split_ifs at hm <;> omega
  · have h8 : 2 ^ a % 8 = 0 := by
      have : 2 ^ a = 2 ^ (a - 3) * 8 := by
        rw [show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_add]
        congr 1
        omega
      rw [this, Nat.mul_mod_left]
    have hb : b % 2 = 0 := by
      split_ifs at hm with hb
      · exact hb
      · omega
    obtain ⟨k, rfl⟩ : ∃ k, b = 2 * k := ⟨b / 2, by omega⟩
    have hk1 : 1 ≤ 3 ^ k := Nat.one_le_pow _ _ (by norm_num)
    have hf : (3 ^ k - 1) * (3 ^ k + 1) = 2 ^ a := by
      have : 3 ^ (2 * k) = 3 ^ k * 3 ^ k := by rw [two_mul, pow_add]
      rw [this] at h
      zify [hk1] at h ⊢
      linarith
    obtain ⟨i, hi⟩ := eq_two_pow_of_dvd (Dvd.intro _ hf)
    obtain ⟨j, hj⟩ := eq_two_pow_of_dvd (Dvd.intro_left _ hf)
    have hij : 2 ^ i + 2 = 2 ^ j := by omega
    obtain ⟨rfl, rfl⟩ := two_pow_add_two_eq_two_pow hij
    have h3 : 3 ^ k = 3 ^ 1 := by simp at hi; omega
    have hk : k = 1 := Nat.pow_right_injective (a := 3) (by norm_num) h3
    subst hk
    have h8' : 2 ^ a = 2 ^ 3 := by simp at h; omega
    exact Or.inr ⟨Nat.pow_right_injective (le_refl 2) h8', rfl⟩

end AcceleratedCollatz
