-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.Core

/-!
  Affine shift of one R-step (R-side counterpart of affine_classId, paper
  sec:numbers; the R-analogue of the Novgorodtsev identity): one R-step under
  x -> x + i*2^Q, for Q above the step's valuation. `minCorrection`: the least
  number of halvings that brings x below x0, with its sufficiency, minimality
  and uniqueness.
-/

namespace AcceleratedCollatz

variable (x0 x : ℕ)

theorem trailingOnes_shift (x_init i Q : ℕ) (hxodd : Odd x_init)
    (hQ : Q ≥ trailingOnes x_init + 1) :
    trailingOnes (x_init + i * 2 ^ Q) = trailingOnes x_init := by
  set v := trailingOnes x_init with hv_def
  have hdvd : 2 ^ v ∣ (x_init + 1) := pow_trailingOnes_dvd x_init
  have hodd_part : Odd ((x_init + 1) / 2 ^ v) := odd_div_pow_trailingOnes x_init hxodd
  have heq : x_init + i * 2 ^ Q + 1 = 2 ^ v * ((x_init + 1) / 2 ^ v + i * 2 ^ (Q - v)) := by
    have h1 : (x_init + 1) / 2 ^ v * 2 ^ v = x_init + 1 := Nat.div_mul_cancel hdvd
    have h2 : 2 ^ Q = 2 ^ v * 2 ^ (Q - v) := by
      rw [← pow_add]
      congr 1
      omega
    calc x_init + i * 2 ^ Q + 1
        = (x_init + 1) + i * 2 ^ Q := by ring
      _ = (x_init + 1) / 2 ^ v * 2 ^ v + i * (2 ^ v * 2 ^ (Q - v)) := by rw [h1, h2]
      _ = 2 ^ v * ((x_init + 1) / 2 ^ v + i * 2 ^ (Q - v)) := by ring
  have hsum_odd : Odd ((x_init + 1) / 2 ^ v + i * 2 ^ (Q - v)) := by
    obtain ⟨k, hk⟩ := hodd_part
    have hQv : Q - v ≥ 1 := by omega
    have hi_even : i * 2 ^ (Q - v) = i * 2 ^ (Q - v - 1) * 2 := by
      rw [mul_assoc, ← pow_succ]
      congr 2
      omega
    exact ⟨k + i * 2 ^ (Q - v - 1), by omega⟩
  unfold trailingOnes
  rw [heq]
  have hS := hsum_odd
  set S := (x_init + 1) / 2 ^ v + i * 2 ^ (Q - v) with hS_def
  have hSpos : S ≠ 0 := by
    obtain ⟨k, hk⟩ := hS
    omega
  have hNpos : 2 ^ v * S ≠ 0 := by
    have h2vpos : (2:ℕ) ^ v ≠ 0 := by positivity
    exact Nat.mul_ne_zero h2vpos hSpos
  have hlow : v ≤ padicValNat 2 (2 ^ v * S) := by
    rcases (padicValNat_dvd_iff (p := 2) v (2 ^ v * S)).mp
        ⟨S, rfl⟩ with h | h
    · exact absurd h hNpos
    · exact h
  have hhigh : ¬ 2 ^ (v + 1) ∣ (2 ^ v * S) := by
    intro hdvd2
    obtain ⟨c, hc⟩ := hdvd2
    obtain ⟨k, hk⟩ := hS
    have h2vpos : 0 < (2:ℕ) ^ v := by positivity
    have heq2 : 2 ^ v * S = 2 ^ v * (2 * c) := by
      rw [hc, pow_succ]
      ring
    have hcancel : S = 2 * c := Nat.eq_of_mul_eq_mul_left h2vpos heq2
    omega
  have hup : ¬ (v + 1 ≤ padicValNat 2 (2 ^ v * S)) := by
    intro hcon
    exact hhigh
      ((padicValNat_dvd_iff (p := 2) (v + 1) (2 ^ v * S)).mpr (Or.inr hcon))
  omega

theorem R_shift_odd (x_init i Q : ℕ) (hx1 : x_init > 1) (hxodd : Odd x_init)
    (hQ : Q ≥ trailingOnes x_init + 1) :
    R (x_init + i * 2 ^ Q) =
      R x_init + 3 ^ (trailingOnes x_init) * i * 2 ^ (Q - trailingOnes x_init - 1) := by
  set v := trailingOnes x_init with hv_def
  have hxi_odd : Odd (x_init + i * 2 ^ Q) := by
    have hQ1 : Q ≥ 1 := by omega
    obtain ⟨j, hj⟩ := hxodd
    refine ⟨j + i * 2 ^ (Q - 1), ?_⟩
    have h2 : i * 2 ^ Q = i * 2 ^ (Q - 1) * 2 := by
      rw [mul_assoc, ← pow_succ]
      congr 2
      omega
    omega
  have hvshift : trailingOnes (x_init + i * 2 ^ Q) = v := trailingOnes_shift x_init i Q hxodd hQ
  have hx1' : x_init + i * 2 ^ Q > 1 := by omega
  rw [R_odd_closed_form (x_init + i * 2 ^ Q) hx1' hxi_odd, hvshift,
      R_odd_closed_form x_init hx1 hxodd]
  rw [← hv_def]
  have hdvd : 2 ^ v ∣ (x_init + 1) := pow_trailingOnes_dvd x_init
  have heq : (x_init + i * 2 ^ Q + 1) / 2 ^ v = (x_init + 1) / 2 ^ v + i * 2 ^ (Q - v) := by
    have h1 : (x_init + 1) / 2 ^ v * 2 ^ v = x_init + 1 := Nat.div_mul_cancel hdvd
    have h2 : 2 ^ Q = 2 ^ v * 2 ^ (Q - v) := by
      rw [← pow_add]
      congr 1
      omega
    have h3 : x_init + i * 2 ^ Q + 1 =
        2 ^ v * ((x_init + 1) / 2 ^ v + i * 2 ^ (Q - v)) := by
      calc x_init + i * 2 ^ Q + 1
          = (x_init + 1) + i * 2 ^ Q := by ring
        _ = (x_init + 1) / 2 ^ v * 2 ^ v + i * (2 ^ v * 2 ^ (Q - v)) := by rw [h1, h2]
        _ = 2 ^ v * ((x_init + 1) / 2 ^ v + i * 2 ^ (Q - v)) := by ring
    rw [h3]
    have h2vpos : (0:ℕ) < 2 ^ v := by positivity
    rw [Nat.mul_div_cancel_left _ h2vpos]
  rw [heq]
  set s0 := (x_init + 1) / 2 ^ v with hs0_def
  have hsub : s0 ≥ 1 := by
    rcases Nat.eq_zero_or_pos s0 with hz | hpos
    · exfalso
      have h1 : s0 * 2 ^ v = x_init + 1 := Nat.div_mul_cancel hdvd
      rw [hz] at h1
      simp at h1
    · exact hpos
  have hQv1 : Q - v ≥ 1 := by omega
  have hpow : 2 ^ (Q - v) = 2 * 2 ^ (Q - v - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hmul : 3 ^ v * (s0 + i * 2 ^ (Q - v)) =
      3 ^ v * s0 + 3 ^ v * i * 2 ^ (Q - v) := by ring
  rw [hmul]
  have h3vs0 : 3 ^ v * s0 ≥ 1 := by
    have : (3:ℕ) ^ v ≥ 1 := Nat.one_le_iff_ne_zero.mpr (by positivity)
    nlinarith [hsub]
  rw [hpow]
  have hfinal : 3 ^ v * i * (2 * 2 ^ (Q - v - 1)) = (3 ^ v * i * 2 ^ (Q - v - 1)) * 2 := by ring
  rw [hfinal]
  omega

/-- Even-branch companion to trailingOnes_shift: shifting by i*2^Q, Q above the
    trailing-zero count of x, leaves trailingZeros unchanged. -/
theorem trailingZeros_shift (x i Q : ℕ) (hxpos : x ≠ 0) (hQ : Q ≥ trailingZeros x + 1) :
    trailingZeros (x + i * 2 ^ Q) = trailingZeros x := by
  set w := trailingZeros x with hw_def
  have hdvd : 2 ^ w ∣ x := pow_padicValNat_dvd (p := 2) (n := x)
  set s := x / 2 ^ w with hs_def
  have heq : x + i * 2 ^ Q = 2 ^ w * (s + i * 2 ^ (Q - w)) := by
    have h1 : s * 2 ^ w = x := Nat.div_mul_cancel hdvd
    have h2 : 2 ^ Q = 2 ^ w * 2 ^ (Q - w) := by
      rw [← pow_add]
      congr 1
      omega
    calc x + i * 2 ^ Q = s * 2 ^ w + i * (2 ^ w * 2 ^ (Q - w)) := by rw [h1, h2]
      _ = 2 ^ w * (s + i * 2 ^ (Q - w)) := by ring
  have hsOdd : Odd s := odd_div_pow_trailingZeros x hxpos
  have hsumOdd : Odd (s + i * 2 ^ (Q - w)) := by
    obtain ⟨k, hk⟩ := hsOdd
    have hQw : Q - w ≥ 1 := by omega
    have hi_even : i * 2 ^ (Q - w) = i * 2 ^ (Q - w - 1) * 2 := by
      rw [mul_assoc, ← pow_succ]
      congr 2
      omega
    exact ⟨k + i * 2 ^ (Q - w - 1), by omega⟩
  unfold trailingZeros
  rw [heq]
  set S := s + i * 2 ^ (Q - w) with hS_def
  have hSpos : S ≠ 0 := by
    obtain ⟨k, hk⟩ := hsumOdd
    omega
  have hNpos : 2 ^ w * S ≠ 0 := by
    have h2wpos : (2:ℕ) ^ w ≠ 0 := by positivity
    exact Nat.mul_ne_zero h2wpos hSpos
  have hlow : w ≤ padicValNat 2 (2 ^ w * S) := by
    rcases (padicValNat_dvd_iff (p := 2) w (2 ^ w * S)).mp ⟨S, rfl⟩ with h | h
    · exact absurd h hNpos
    · exact h
  have hhigh : ¬ 2 ^ (w + 1) ∣ (2 ^ w * S) := by
    intro hdvd2
    obtain ⟨c, hc⟩ := hdvd2
    obtain ⟨k, hk⟩ := hsumOdd
    have h2wpos : 0 < (2:ℕ) ^ w := by positivity
    have heq2 : 2 ^ w * S = 2 ^ w * (2 * c) := by
      rw [hc, pow_succ]
      ring
    have hcancel : S = 2 * c := Nat.eq_of_mul_eq_mul_left h2wpos heq2
    omega
  have hup : ¬ (w + 1 ≤ padicValNat 2 (2 ^ w * S)) := by
    intro hcon
    exact hhigh ((padicValNat_dvd_iff (p := 2) (w + 1) (2 ^ w * S)).mpr (Or.inr hcon))
  omega

/-- Even-branch analogue of R_shift_odd: the shift i*2^Q becomes i*2^(Q - trailingZeros x). -/
theorem R_shift_even (x i Q : ℕ) (hxpos : x ≠ 0) (hxEven : Even x)
    (hQ : Q ≥ trailingZeros x + 1) :
    R (x + i * 2 ^ Q) = R x + i * 2 ^ (Q - trailingZeros x) := by
  set w := trailingZeros x with hw_def
  have hvshift : trailingZeros (x + i * 2 ^ Q) = w := trailingZeros_shift x i Q hxpos hQ
  have hx1 : x > 1 := by
    obtain ⟨r, hr⟩ := hxEven
    omega
  have hxi_even : Even (x + i * 2 ^ Q) := by
    obtain ⟨r, hr⟩ := hxEven
    have hQ1 : Q ≥ 1 := by omega
    exact ⟨r + i * 2 ^ (Q - 1), by
      have h2 : i * 2 ^ Q = i * 2 ^ (Q - 1) * 2 := by
        rw [mul_assoc, ← pow_succ]
        congr 2
        omega
      omega⟩
  have hx1' : x + i * 2 ^ Q > 1 := by omega
  unfold R
  rw [ite_eq_left (by omega), ite_eq_left hxi_even, ite_eq_left (by omega),
    ite_eq_left hxEven, hvshift, ← hw_def]
  have hdvd : 2 ^ w ∣ x := pow_padicValNat_dvd (p := 2) (n := x)
  have heq : x + i * 2 ^ Q = 2 ^ w * (x / 2 ^ w + i * 2 ^ (Q - w)) := by
    have h1 : x / 2 ^ w * 2 ^ w = x := Nat.div_mul_cancel hdvd
    have h2 : 2 ^ Q = 2 ^ w * 2 ^ (Q - w) := by
      rw [← pow_add]
      congr 1
      omega
    calc x + i * 2 ^ Q = x / 2 ^ w * 2 ^ w + i * (2 ^ w * 2 ^ (Q - w)) := by rw [h1, h2]
      _ = 2 ^ w * (x / 2 ^ w + i * 2 ^ (Q - w)) := by ring
  rw [heq]
  have h2wpos : (0:ℕ) < 2 ^ w := by positivity
  rw [Nat.mul_div_cancel_left _ h2wpos]

/-- The minimal-crossing correction: the least number of halvings that brings x
    strictly below x0 (0 for x = 0). -/
def minCorrection (x0 x : ℕ) : ℕ :=
  if x < x0 ∨ x = 0 then 0
  else minCorrection x0 (x / 2) + 1
termination_by x
decreasing_by omega

theorem minCorrection_eq :
    minCorrection x0 x =
      if x < x0 ∨ x = 0 then 0 else minCorrection x0 (x / 2) + 1 := by
  conv_lhs => rw [minCorrection]

/-- Sufficiency: x halved `minCorrection x0 x` times is below x0. -/
theorem minCorrection_suff (hx0 : x0 ≥ 1) :
    x / 2 ^ (minCorrection x0 x) < x0 := by
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    rw [minCorrection_eq]
    by_cases hcond : x < x0 ∨ x = 0
    · simp only [hcond, ite_true]
      rcases hcond with h | h
      · simpa using h
      · simp [h]
        omega
    · simp only [hcond, ite_false]
      push Not at hcond
      obtain ⟨hge, hxne⟩ := hcond
      have hlt : x / 2 < x := Nat.div_lt_self (by omega) (by omega)
      have hrec := ih (x / 2) hlt
      have heq : x / 2 ^ (minCorrection x0 (x / 2) + 1) =
          (x / 2) / 2 ^ (minCorrection x0 (x / 2)) := by
        rw [Nat.div_div_eq_div_mul, pow_succ, mul_comm]
      rw [heq]
      exact hrec

/-- Minimality: for `minCorrection x0 x` ≥ 1, x halved one time fewer is not
    below x0. -/
theorem minCorrection_min (hx0 : x0 ≥ 1) (hpos : minCorrection x0 x ≥ 1) :
    x / 2 ^ (minCorrection x0 x - 1) ≥ x0 := by
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    rw [minCorrection_eq] at hpos ⊢
    by_cases hcond : x < x0 ∨ x = 0
    · simp only [hcond, ite_true] at hpos
      omega
    · simp only [hcond, ite_false] at hpos ⊢
      push Not at hcond
      obtain ⟨hge, hxne⟩ := hcond
      simp only [Nat.add_sub_cancel]
      rcases Nat.eq_zero_or_pos (minCorrection x0 (x / 2)) with hz | hp
      · rw [hz]
        simpa using hge
      · have hlt : x / 2 < x := Nat.div_lt_self (by omega) (by omega)
        have hrec := ih (x / 2) hlt hp
        have heq : x / 2 ^ (minCorrection x0 (x / 2)) =
            (x / 2) / 2 ^ (minCorrection x0 (x / 2) - 1) := by
          rw [Nat.div_div_eq_div_mul]
          congr 1
          rw [← pow_succ']
          congr 1
          omega
        rw [heq]
        exact hrec

/-- Uniqueness: any w with the sufficiency and minimality bounds equals
    `minCorrection`. -/
theorem minCorrection_unique (x0 x w : ℕ) (hx0 : x0 ≥ 1)
    (hsuff : x / 2 ^ w < x0) (hmin : w = 0 ∨ x / 2 ^ (w - 1) ≥ x0) :
    minCorrection x0 x = w := by
  have hs0 := minCorrection_suff x0 x hx0
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · -- case minCorrection x0 x < w
    have hwpos : w ≥ 1 := by omega
    rcases hmin with h0 | hm
    · omega
    · have hmono : x / 2 ^ (w - 1) ≤ x / 2 ^ (minCorrection x0 x) :=
        Nat.div_le_div_left (Nat.pow_le_pow_right (by norm_num) (by omega)) (by positivity)
      have : x / 2 ^ (w - 1) < x0 := lt_of_le_of_lt hmono hs0
      omega
  · -- case w < minCorrection x0 x
    have hmcpos : minCorrection x0 x ≥ 1 := by omega
    have hm0 := minCorrection_min x0 x hx0 hmcpos
    have hmono : x / 2 ^ (minCorrection x0 x - 1) ≤ x / 2 ^ w :=
      Nat.div_le_div_left (Nat.pow_le_pow_right (by norm_num) (by omega)) (by positivity)
    have : x0 ≤ x / 2 ^ w := le_trans hm0 hmono
    omega

end AcceleratedCollatz
