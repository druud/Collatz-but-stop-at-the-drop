-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TRhinBound
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
  Rhin's lower bound for a linear form in log 2 and log 3 (Rhin 1987, Proposition (7):
  |u₀ + u₁ log 2 + u₂ log 3| ≥ H^(-13.3) for integers with H = max(|u₁|, |u₂|) ≥ 2),
  stated as a hypothesis for u₀ = 0 (`RhinLog`), and the step from it to `RhinBound 1 14`
  (`rhinBound_of_rhinLog`): with Λ = p2(n) log 2 - n log 3 > 0 and H = p2(n) ≥ 2 for
  n ≥ 1, 2^p2(n) = 3^n e^Λ ≥ 3^n (1 + Λ) and Λ ≥ H^(-13.3) ≥ H^(-14). `RhinLogFrom` asks
  less (a factor c > 0 and a threshold H₀; implied by (7) and by his (8)) and gives
  `RhinBound K 14` for some K (`exists_rhinBound_of_rhinLogFrom`).
-/

namespace AcceleratedCollatz

/-- |u₁ log 2 + u₂ log 3| ≥ H^(-13.3) for all integers u₁, u₂ with
    H = max(|u₁|, |u₂|) ≥ 2. -/
def RhinLog : Prop :=
  ∀ u₁ u₂ : ℤ, 2 ≤ max |u₁| |u₂| →
    ((max |u₁| |u₂| : ℤ) : ℝ) ^ (-(133 / 10 : ℝ)) ≤
      |(u₁ : ℝ) * Real.log 2 + (u₂ : ℝ) * Real.log 3|

/-- n < p2(n) for n ≥ 1. -/
theorem lt_p2_of {n : ℕ} (hn : 1 ≤ n) : n < p2_of n := by
  have h1 : 2 ^ n < 3 ^ n := Nat.pow_lt_pow_left (by norm_num) (by omega)
  have h2 : 2 ^ n < 2 ^ p2_of n := lt_trans h1 (p2_of_spec n)
  exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp h2

/-- From c H^(-13.3) ≤ p2(n) log 2 - n log 3 with H = p2(n), c > 0, n ≥ 1:
    c 3^n ≤ p2(n)^14 (2^p2(n) - 3^n) in the reals. -/
theorem linearForm_real {n : ℕ} (hn : 1 ≤ n) {c : ℝ} (hc : 0 < c)
    (hH : c * (p2_of n : ℝ) ^ (-(133 / 10 : ℝ)) ≤
      (p2_of n : ℝ) * Real.log 2 + -(n : ℝ) * Real.log 3) :
    c * (3 : ℝ) ^ n ≤ (p2_of n : ℝ) ^ 14 * ((2 : ℝ) ^ p2_of n - (3 : ℝ) ^ n) := by
  set p := p2_of n with hpdef
  have hnp : n < p := lt_p2_of hn
  have hspec : 3 ^ n < 2 ^ p := p2_of_spec n
  have hspecR : (3 : ℝ) ^ n < (2 : ℝ) ^ p := by exact_mod_cast hspec
  have h3pos : (0 : ℝ) < (3 : ℝ) ^ n := by positivity
  have hpR : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (by omega : 1 ≤ p)
  set L := (p : ℝ) * Real.log 2 + -(n : ℝ) * Real.log 3 with hLdef
  have hLlog : L = Real.log ((2 : ℝ) ^ p / (3 : ℝ) ^ n) := by
    rw [Real.log_div (by positivity) (ne_of_gt h3pos), Real.log_pow, Real.log_pow, hLdef]
    ring
  -- c H^(-14) ≤ c H^(-13.3) ≤ L
  have hexp : (p : ℝ) ^ (-(14 : ℝ)) ≤ (p : ℝ) ^ (-(133 / 10 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hpR (by norm_num)
  have h14 : (p : ℝ) ^ (-(14 : ℝ)) = 1 / (p : ℝ) ^ 14 := by
    rw [Real.rpow_neg (by positivity), one_div]
    norm_cast
  have hL14 : c * (1 / (p : ℝ) ^ 14) ≤ L := by
    rw [← h14]
    exact le_trans (mul_le_mul_of_nonneg_left hexp hc.le) hH
  -- e^L = 2^p / 3^n ≥ 1 + L
  have hexpL : Real.exp L = (2 : ℝ) ^ p / (3 : ℝ) ^ n := by
    rw [hLlog]
    exact Real.exp_log (by positivity)
  have hone : L + 1 ≤ (2 : ℝ) ^ p / (3 : ℝ) ^ n := by
    rw [← hexpL]
    exact Real.add_one_le_exp L
  have hp14 : (0 : ℝ) < (p : ℝ) ^ 14 := by positivity
  have hstep : c / (p : ℝ) ^ 14 ≤ (2 : ℝ) ^ p / (3 : ℝ) ^ n - 1 := by
    rw [div_eq_mul_one_div]
    linarith
  have hdiv : (2 : ℝ) ^ p / (3 : ℝ) ^ n - 1 = ((2 : ℝ) ^ p - (3 : ℝ) ^ n) / (3 : ℝ) ^ n := by
    field_simp
  rw [hdiv, div_le_div_iff₀ hp14 h3pos] at hstep
  linarith

/-- The hypothesis of `RhinLog` at u₁ = p2(n), u₂ = -n, for n ≥ 1. -/
theorem max_abs_p2_of {n : ℕ} (hn : 1 ≤ n) :
    max |((p2_of n : ℕ) : ℤ)| |(-(n : ℤ))| = (p2_of n : ℤ) := by
  have hnp : n < p2_of n := lt_p2_of hn
  rw [abs_neg, abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
  exact max_eq_left (by exact_mod_cast hnp.le)

/-- Under `RhinLog`: 3^n ≤ p2(n)^14 (2^p2(n) - 3^n) in the reals, for n ≥ 1. -/
theorem rhinLog_real {n : ℕ} (hR : RhinLog) (hn : 1 ≤ n) :
    (3 : ℝ) ^ n ≤ (p2_of n : ℝ) ^ 14 * ((2 : ℝ) ^ p2_of n - (3 : ℝ) ^ n) := by
  have hnp : n < p2_of n := lt_p2_of (by omega)
  have hmax := max_abs_p2_of (n := n) (by omega)
  have hH := hR (p2_of n : ℤ) (-(n : ℤ)) (by
    rw [hmax]
    exact_mod_cast (by omega : 2 ≤ p2_of n))
  rw [hmax] at hH
  push_cast at hH
  have hspec : 3 ^ n < 2 ^ p2_of n := p2_of_spec n
  have hLpos : 0 < (p2_of n : ℝ) * Real.log 2 + -(n : ℝ) * Real.log 3 := by
    have e : (p2_of n : ℝ) * Real.log 2 + -(n : ℝ) * Real.log 3 =
        Real.log ((2 : ℝ) ^ p2_of n / (3 : ℝ) ^ n) := by
      rw [Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_pow]
      ring
    rw [e]
    apply Real.log_pos
    rw [one_lt_div (by positivity)]
    exact_mod_cast hspec
  rw [abs_of_pos hLpos] at hH
  have hH1 : (1 : ℝ) * (p2_of n : ℝ) ^ (-(133 / 10 : ℝ)) ≤
      (p2_of n : ℝ) * Real.log 2 + -(n : ℝ) * Real.log 3 := by
    rw [one_mul]
    exact hH
  have h := linearForm_real (n := n) (by omega) one_pos hH1
  linarith

/-- `RhinLog` gives `RhinBound 1 14`. -/
theorem rhinBound_of_rhinLog (hR : RhinLog) : RhinBound 1 14 := by
  intro n hn
  have hreal := rhinLog_real hR hn
  have hle : 3 ^ n ≤ 2 ^ p2_of n := (p2_of_spec n).le
  rw [one_mul]
  have hcast : ((p2_of n ^ 14 * (2 ^ p2_of n - 3 ^ n) : ℕ) : ℝ) =
      (p2_of n : ℝ) ^ 14 * ((2 : ℝ) ^ p2_of n - (3 : ℝ) ^ n) := by
    push_cast [Nat.cast_sub hle]
    ring
  have h : ((3 ^ n : ℕ) : ℝ) ≤ ((p2_of n ^ 14 * (2 ^ p2_of n - 3 ^ n) : ℕ) : ℝ) := by
    rw [hcast]
    push_cast
    exact hreal
  exact_mod_cast h

/-- |u₁ log 2 + u₂ log 3| ≥ c H^(-13.3) for some c > 0, for all integers u₁, u₂ with
    H = max(|u₁|, |u₂|) ≥ 2 and H ≥ H₀ for some H₀: implied by Rhin's (7), and by his (8)
    (H^(-7.616) beyond an effective H₀). -/
def RhinLogFrom : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ H₀ : ℕ, ∀ u₁ u₂ : ℤ, 2 ≤ max |u₁| |u₂| → (H₀ : ℤ) ≤ max |u₁| |u₂| →
    c * ((max |u₁| |u₂| : ℤ) : ℝ) ^ (-(133 / 10 : ℝ)) ≤
      |(u₁ : ℝ) * Real.log 2 + (u₂ : ℝ) * Real.log 3|

/-- `RhinLog` gives `RhinLogFrom` (c = 1, H₀ = 0). -/
theorem rhinLogFrom_of_rhinLog (hR : RhinLog) : RhinLogFrom :=
  ⟨1, one_pos, 0, fun u₁ u₂ h3 _ => by
    rw [one_mul]
    exact hR u₁ u₂ h3⟩

/-- `RhinLogFrom` gives `RhinBound K 14` for some K. -/
theorem exists_rhinBound_of_rhinLogFrom (hR : RhinLogFrom) : ∃ K, RhinBound K 14 := by
  obtain ⟨c, hc, H₀, hH₀⟩ := hR
  set K := ⌈1 / c⌉₊ with hK
  have hKc : 1 / c ≤ (K : ℝ) := Nat.le_ceil (1 / c)
  have hfrom : RhinBoundFrom K 14 (H₀ + 2) := by
    intro n hn
    have hnp : n < p2_of n := lt_p2_of (by omega)
    have hmax := max_abs_p2_of (n := n) (by omega)
    have hH := hH₀ (p2_of n : ℤ) (-(n : ℤ))
      (by
        rw [hmax]
        exact_mod_cast (by omega : 2 ≤ p2_of n))
      (by
        rw [hmax]
        exact_mod_cast (by omega : H₀ ≤ p2_of n))
    rw [hmax] at hH
    push_cast at hH
    have hspec : 3 ^ n < 2 ^ p2_of n := p2_of_spec n
    have hle : 3 ^ n ≤ 2 ^ p2_of n := hspec.le
    have hLpos : 0 < (p2_of n : ℝ) * Real.log 2 + -(n : ℝ) * Real.log 3 := by
      have e : (p2_of n : ℝ) * Real.log 2 + -(n : ℝ) * Real.log 3 =
          Real.log ((2 : ℝ) ^ p2_of n / (3 : ℝ) ^ n) := by
        rw [Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_pow]
        ring
      rw [e]
      apply Real.log_pos
      rw [one_lt_div (by positivity)]
      exact_mod_cast hspec
    rw [abs_of_pos hLpos] at hH
    have hreal := linearForm_real (n := n) (by omega) hc hH
    have hD : (0 : ℝ) ≤ (p2_of n : ℝ) ^ 14 * ((2 : ℝ) ^ p2_of n - (3 : ℝ) ^ n) := by
      have : (3 : ℝ) ^ n ≤ (2 : ℝ) ^ p2_of n := by exact_mod_cast hle
      have h0 : (0 : ℝ) ≤ (2 : ℝ) ^ p2_of n - (3 : ℝ) ^ n := by linarith
      positivity
    have h3 : (3 : ℝ) ^ n ≤ (K : ℝ) * ((p2_of n : ℝ) ^ 14 *
        ((2 : ℝ) ^ p2_of n - (3 : ℝ) ^ n)) := by
      have e1 : (3 : ℝ) ^ n = 1 / c * (c * (3 : ℝ) ^ n) := by
        rw [← mul_assoc, one_div_mul_cancel hc.ne', one_mul]
      calc (3 : ℝ) ^ n = 1 / c * (c * (3 : ℝ) ^ n) := e1
        _ ≤ 1 / c * ((p2_of n : ℝ) ^ 14 * ((2 : ℝ) ^ p2_of n - (3 : ℝ) ^ n)) :=
            mul_le_mul_of_nonneg_left hreal (by positivity)
        _ ≤ (K : ℝ) * ((p2_of n : ℝ) ^ 14 * ((2 : ℝ) ^ p2_of n - (3 : ℝ) ^ n)) :=
            mul_le_mul_of_nonneg_right hKc hD
    have hcast : ((K * p2_of n ^ 14 * (2 ^ p2_of n - 3 ^ n) : ℕ) : ℝ) =
        (K : ℝ) * ((p2_of n : ℝ) ^ 14 * ((2 : ℝ) ^ p2_of n - (3 : ℝ) ^ n)) := by
      push_cast [Nat.cast_sub hle]
      ring
    have h : ((3 ^ n : ℕ) : ℝ) ≤ ((K * p2_of n ^ 14 * (2 ^ p2_of n - 3 ^ n) : ℕ) : ℝ) := by
      rw [hcast]
      push_cast
      exact h3
    exact_mod_cast h
  exact ⟨K + 3 ^ (H₀ + 2), rhinBound_of_rhinBoundFrom hfrom⟩

end AcceleratedCollatz
