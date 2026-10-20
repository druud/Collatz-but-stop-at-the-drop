-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.Numlib

/-!
  The accelerated map R and its own properties.
-/

namespace AcceleratedCollatz

variable (x : ℕ)

/-- The fast map (paper sec:fast). 0 and 1 -> 1; even x -> x without its trailing
    zero-bits; odd x > 1 with v trailing one-bits -> its v odd T-steps and the halving
    after them, in closed form. -/
def R (x : ℕ) : ℕ :=
  if 1 < x then
    if Even x then x / 2 ^ (trailingZeros x)
    else ((3 ^ (trailingOnes x) * (x + 1) / 2 ^ (trailingOnes x)) - 1) / 2
  else 1

theorem R_odd_closed_form (hx1 : x > 1) (hx : Odd x) :
    R x = (3 ^ (trailingOnes x) * ((x + 1) / 2 ^ (trailingOnes x)) - 1) / 2 := by
  unfold R
  simp only [ite_eq_left hx1, ite_eq_right (Nat.not_even_iff_odd.mpr hx)]
  rw [Nat.mul_div_assoc _ (pow_trailingOnes_dvd x)]

/-- Closed form of the even branch of R. -/
theorem R_even_closed_form (hx1 : x > 1) (hxEven : Even x) :
    R x = x / 2 ^ (trailingZeros x) := by
  unfold R
  rw [ite_eq_left hx1, ite_eq_left hxEven]

theorem R_ge_one : R x ≥ 1 := by
  unfold R
  split_ifs with h1 h2
  rotate_right
  · rfl
  · obtain ⟨r, hr⟩ := h2
    have hv1 : trailingZeros x ≥ 1 := one_le_padicValNat_of_dvd (by omega) ⟨r, by omega⟩
    have hlt2 : (1 : ℕ) < 2 ^ (trailingZeros x) := by
      calc (1 : ℕ) < 2 := by norm_num
        _ ≤ 2 ^ (trailingZeros x) := Nat.le_self_pow (by omega) 2
    have hdvd2 : 2 ^ (trailingZeros x) ∣ x := pow_padicValNat_dvd (p := 2) (n := x)
    have heq2 : x / 2 ^ (trailingZeros x) * 2 ^ (trailingZeros x) = x := Nat.div_mul_cancel hdvd2
    rcases Nat.eq_zero_or_pos (x / 2 ^ (trailingZeros x)) with hz | hpos
    · rw [hz] at heq2
      simp at heq2
      omega
    · omega
  · have hxOdd : Odd x := Nat.not_even_iff_odd.mp h2
    set v := trailingOnes x with hv_def
    have hdvd : 2 ^ v ∣ (x + 1) := pow_padicValNat_dvd (p := 2) (n := x + 1)
    rw [Nat.mul_div_assoc _ hdvd]
    set s := (x + 1) / 2 ^ v with hs_def
    have heq : s * 2 ^ v = x + 1 := Nat.div_mul_cancel hdvd
    have hsOdd : Odd s := odd_div_pow_trailingOnes x hxOdd
    have hvpos : v ≥ 1 := by
      obtain ⟨j, hj⟩ := hxOdd
      exact one_le_padicValNat_of_dvd (by omega) ⟨j + 1, by omega⟩
    have h3v : 3 ^ v ≥ 3 := by
      calc 3 ^ v ≥ 3 ^ 1 := Nat.pow_le_pow_right (by omega) hvpos
        _ = 3 := by ring
    have hs1 : s ≥ 1 := hsOdd.pos
    have := Nat.mul_le_mul h3v hs1
    omega

theorem R_no_other_fixed_point (hx : x > 1) (hfix : R x = x) : False := by
  unfold R at hfix
  rw [ite_eq_left hx] at hfix
  split_ifs at hfix with h2
  · obtain ⟨r, hr⟩ := h2
    have hv1 : trailingZeros x ≥ 1 := one_le_padicValNat_of_dvd (by omega) ⟨r, by omega⟩
    have hlt2 : (1 : ℕ) < 2 ^ (trailingZeros x) := by
      calc (1 : ℕ) < 2 := by norm_num
        _ ≤ 2 ^ (trailingZeros x) := Nat.le_self_pow (by omega) 2
    have : x / 2 ^ (trailingZeros x) < x := Nat.div_lt_self (by omega) hlt2
    omega
  · have hxOdd : Odd x := Nat.not_even_iff_odd.mp h2
    set v := trailingOnes x with hv_def
    have hdvd : 2 ^ v ∣ (x + 1) := pow_padicValNat_dvd (p := 2) (n := x + 1)
    rw [Nat.mul_div_assoc _ hdvd] at hfix
    set s := (x + 1) / 2 ^ v with hs_def
    have heq : s * 2 ^ v = x + 1 := Nat.div_mul_cancel hdvd
    have hsOdd : Odd s := odd_div_pow_trailingOnes x hxOdd
    have hvpos : v ≥ 1 := by
      obtain ⟨j, hj⟩ := hxOdd
      exact one_le_padicValNat_of_dvd (by omega) ⟨j + 1, by omega⟩
    have h3Odd : Odd (3 ^ v) := (by decide : Odd 3).pow
    have h3vsOdd : Odd (3 ^ v * s) := h3Odd.mul hsOdd
    obtain ⟨k, hk⟩ := h3vsOdd
    have hkx : k = x := by
      have hcalc : (3 ^ v * s - 1) / 2 = x := hfix
      omega
    have hmain : 3 ^ v * s = 2 * x + 1 := by omega
    have hderive : s * 2 ^ (v + 1) = 3 ^ v * s + 1 := by
      have e1 : s * 2 ^ (v + 1) = 2 * x + 2 := by
        calc s * 2 ^ (v + 1) = s * 2 ^ v * 2 := by ring
          _ = (x + 1) * 2 := by rw [heq]
          _ = 2 * x + 2 := by ring
      omega
    have hspos : s > 0 := hsOdd.pos
    have hlt : 2 ^ (v + 1) > 3 ^ v := by
      by_contra hle
      push Not at hle
      have hmul : 2 ^ (v + 1) * s ≤ 3 ^ v * s := Nat.mul_le_mul hle (le_refl s)
      rw [mul_comm (2 ^ (v + 1)) s] at hmul
      omega
    rcases Nat.lt_or_ge v 2 with hvlt | hvge
    · have hv1 : v = 1 := by omega
      rw [hv1] at hderive
      have hs1 : s = 1 := by omega
      rw [hv1, hs1] at heq
      omega
    · have := three_pow_ge_two_pow_succ v hvge
      omega

/-- Inversion of one odd step of R: x from R x and the valuation trailingOnes x
    (paper's Correspondence argument). -/
theorem R_odd_inv (hx1 : x > 1) (hxOdd : Odd x) :
    x = (2 * R x + 1) / 3 ^ (trailingOnes x) * 2 ^ (trailingOnes x) - 1 := by
  set v := trailingOnes x with hv_def
  have hdvd : 2 ^ v ∣ (x + 1) := pow_trailingOnes_dvd x
  set s := (x + 1) / 2 ^ v with hs_def
  have heq : s * 2 ^ v = x + 1 := Nat.div_mul_cancel hdvd
  have hsOdd : Odd s := odd_div_pow_trailingOnes x hxOdd
  have h3Odd : Odd (3 ^ v) := (by decide : Odd 3).pow
  have h3vsOdd : Odd (3 ^ v * s) := h3Odd.mul hsOdd
  rw [R_odd_closed_form x hx1 hxOdd, ← hv_def, ← hs_def]
  obtain ⟨k, hk⟩ := h3vsOdd
  have hRcalc : (3 ^ v * s - 1) / 2 = k := by omega
  rw [hRcalc]
  have h2k1 : 2 * k + 1 = 3 ^ v * s := by omega
  rw [h2k1]
  have h3vpos : (0:ℕ) < 3 ^ v := by positivity
  rw [Nat.mul_div_cancel_left s h3vpos, heq]
  omega

end AcceleratedCollatz
