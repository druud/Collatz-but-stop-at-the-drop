-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.PowDiff
import AcceleratedCollatz.TRhinLog
import AcceleratedCollatz.TRhinCheck

/-!
# The numbers |2^i - 3^j| for every bound, under Rhin's bound

Companion of `PowDiff` (A014121 and A363999 below 5·10^11, unconditional). Here, under
`RhinLog` (Rhin 1987, Proposition (7), cited as a hypothesis, see `TRhinLog`), every v is
decided by a finite search. With H = max(i, j) ≥ 2:

* min(2^i, 3^j) ≤ H^14 |2^i - 3^j| (`min_le_of_rhinLog`), from min(a, b) |log(a/b)| ≤ |a - b|
  (`min_mul_abs_log_le`, by log x ≤ x - 1) and |i log 2 - j log 3| ≥ H^(-13.3);
* so 2^H ≤ (H^14 + 1) |2^i - 3^j| (`two_pow_max_le`);
* for B ≥ 28 with (B^14 + 1) v < 2^B, every H ≥ B has (H^14 + 1) v < 2^H
  (`lt_two_pow_of_le`, by (H + 1)^14 ≤ 2 H^14), so v = |2^i - 3^j| needs i, j < B
  (`isPowDiff_iff_lt`), and `searchB lo v B` decides it (`isPowDiff_iff_searchB`).

For v ≤ 10^30, B = 300 will do (`isPowDiff_iff_searchB_300`).
-/

namespace PowDiff

open AcceleratedCollatz

/-- min(a, b) |log(a/b)| ≤ |a - b| for a, b > 0. -/
theorem min_mul_abs_log_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    min a b * |Real.log (a / b)| ≤ |a - b| := by
  rcases le_total b a with h | h
  · have hl : 0 ≤ Real.log (a / b) := Real.log_nonneg ((one_le_div hb).mpr h)
    rw [min_eq_right h, abs_of_nonneg hl, abs_of_nonneg (by linarith)]
    have h1 := Real.log_le_sub_one_of_pos (div_pos ha hb)
    calc b * Real.log (a / b) ≤ b * (a / b - 1) := mul_le_mul_of_nonneg_left h1 hb.le
      _ = a - b := by field_simp
  · have he : Real.log (a / b) = -Real.log (b / a) := by
      rw [← Real.log_inv, inv_div]
    have hl : 0 ≤ Real.log (b / a) := Real.log_nonneg ((one_le_div ha).mpr h)
    rw [min_eq_left h, he, abs_neg, abs_of_nonneg hl, abs_of_nonpos (by linarith)]
    have h1 := Real.log_le_sub_one_of_pos (div_pos hb ha)
    calc a * Real.log (b / a) ≤ a * (b / a - 1) := mul_le_mul_of_nonneg_left h1 ha.le
      _ = -(a - b) := by field_simp; ring

/-- Under `RhinLog`: min(2^i, 3^j) ≤ H^14 |2^i - 3^j| with H = max(i, j) ≥ 2. -/
theorem min_le_of_rhinLog (hR : RhinLog) {i j : ℕ} (hH : 2 ≤ max i j) :
    min (2 ^ i) (3 ^ j) ≤ max i j ^ 14 * D (2 ^ i) (3 ^ j) := by
  set H := max i j with hHdef
  have hmax : max |(i : ℤ)| |(-(j : ℤ))| = (H : ℤ) := by
    rw [abs_neg, abs_of_nonneg (by positivity), abs_of_nonneg (by positivity), hHdef]
    push_cast
    rfl
  have hr := hR (i : ℤ) (-(j : ℤ)) (by rw [hmax]; exact_mod_cast hH)
  rw [hmax] at hr
  push_cast at hr
  have ha : (0 : ℝ) < 2 ^ i := by positivity
  have hb : (0 : ℝ) < 3 ^ j := by positivity
  have hlog : (i : ℝ) * Real.log 2 + -(j : ℝ) * Real.log 3 = Real.log ((2 : ℝ) ^ i / 3 ^ j) := by
    rw [Real.log_div ha.ne' hb.ne', Real.log_pow, Real.log_pow]
    ring
  rw [hlog] at hr
  have hHR : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast (by omega : 1 ≤ H)
  have hexp : (H : ℝ) ^ (-(14 : ℝ)) ≤ (H : ℝ) ^ (-(133 / 10 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hHR (by norm_num)
  have h14 : (H : ℝ) ^ (-(14 : ℝ)) = 1 / (H : ℝ) ^ 14 := by
    rw [Real.rpow_neg (by positivity), one_div]
    norm_cast
  have hm := min_mul_abs_log_le ha hb
  have hminpos : (0 : ℝ) ≤ min ((2 : ℝ) ^ i) (3 ^ j) := le_min ha.le hb.le
  have hH14 : (0 : ℝ) < (H : ℝ) ^ 14 := by positivity
  have hstep : min ((2 : ℝ) ^ i) (3 ^ j) * (1 / (H : ℝ) ^ 14) ≤ |(2 : ℝ) ^ i - 3 ^ j| := by
    rw [← h14]
    exact le_trans (mul_le_mul_of_nonneg_left (hexp.trans hr) hminpos) hm
  have hreal : min ((2 : ℝ) ^ i) (3 ^ j) ≤ (H : ℝ) ^ 14 * |(2 : ℝ) ^ i - 3 ^ j| := by
    rw [mul_one_div, div_le_iff₀ hH14] at hstep
    linarith
  have hD : ((D (2 ^ i) (3 ^ j) : ℕ) : ℝ) = |(2 : ℝ) ^ i - 3 ^ j| := by
    rw [← natAbs_eq_D]
    rw [Nat.cast_natAbs]
    push_cast
    rfl
  have hmin : ((min (2 ^ i) (3 ^ j) : ℕ) : ℝ) = min ((2 : ℝ) ^ i) (3 ^ j) := by
    push_cast
    rfl
  have h : ((min (2 ^ i) (3 ^ j) : ℕ) : ℝ) ≤ ((H ^ 14 * D (2 ^ i) (3 ^ j) : ℕ) : ℝ) := by
    rw [hmin]
    push_cast
    rw [hD]
    exact hreal
  exact_mod_cast h

/-- Under `RhinLog`: 2^H ≤ (H^14 + 1) |2^i - 3^j| with H = max(i, j) ≥ 2. -/
theorem two_pow_max_le (hR : RhinLog) {i j : ℕ} (hH : 2 ≤ max i j) :
    2 ^ max i j ≤ (max i j ^ 14 + 1) * D (2 ^ i) (3 ^ j) := by
  have hm := min_le_of_rhinLog hR hH
  have h2 : 2 ^ max i j ≤ max (2 ^ i) (3 ^ j) := by
    rcases le_total j i with h | h
    · rw [max_eq_left h]
      exact le_max_left _ _
    · rw [max_eq_right h]
      exact le_trans (Nat.pow_le_pow_left (by decide) j) (le_max_right _ _)
  unfold D at hm ⊢
  have he : max (2 ^ i) (3 ^ j) = min (2 ^ i) (3 ^ j) + (2 ^ i - 3 ^ j + (3 ^ j - 2 ^ i)) := by
    omega
  rw [he] at h2
  nlinarith

/-- (B^14 + 1) v < 2^B with B ≥ 28 gives (H^14 + 1) v < 2^H for every H ≥ B. -/
theorem lt_two_pow_of_le {B v : ℕ} (hB : 28 ≤ B) (hv : (B ^ 14 + 1) * v < 2 ^ B) :
    ∀ H, B ≤ H → (H ^ 14 + 1) * v < 2 ^ H := by
  intro H hH
  induction H, hH using Nat.le_induction with
  | base => exact hv
  | succ H hBH ih =>
    have hs : (H + 1) ^ 14 ≤ 2 * H ^ 14 := succ_pow_le_two_mul (by omega)
    calc ((H + 1) ^ 14 + 1) * v ≤ 2 * ((H ^ 14 + 1) * v) := by nlinarith
      _ < 2 * 2 ^ H := by omega
      _ = 2 ^ (H + 1) := by ring

/-- Under `RhinLog`, for B ≥ 28 with (B^14 + 1) v < 2^B: v = |2^i - 3^j| with i, j ≥ lo
    exactly when it is so with i, j < B. -/
theorem isPowDiff_iff_lt (hR : RhinLog) {lo v B : ℕ} (hB : 28 ≤ B)
    (hv : (B ^ 14 + 1) * v < 2 ^ B) :
    IsPowDiff lo v ↔ ∃ i j, i < B ∧ j < B ∧ lo ≤ i ∧ lo ≤ j ∧ D (2 ^ i) (3 ^ j) = v := by
  constructor
  · rintro ⟨i, j, hi, hj, he⟩
    rw [natAbs_eq_D] at he
    refine ⟨i, j, ?_, ?_, hi, hj, he⟩ <;>
    · by_contra hc
      have hH : B ≤ max i j := by omega
      have h1 := two_pow_max_le hR (i := i) (j := j) (by omega)
      have h2 := lt_two_pow_of_le hB hv (max i j) hH
      rw [he] at h1
      omega
  · rintro ⟨i, j, -, -, hi, hj, he⟩
    exact ⟨i, j, hi, hj, by rw [natAbs_eq_D, he]⟩

/-- The search over i, j < B. -/
def searchB (lo v B : ℕ) : Bool :=
  (List.range B).any fun i => (List.range B).any fun j =>
    decide (lo ≤ i) && decide (lo ≤ j) && decide (D (2 ^ i) (3 ^ j) = v)

theorem searchB_iff {lo v B : ℕ} :
    searchB lo v B = true ↔ ∃ i j, i < B ∧ j < B ∧ lo ≤ i ∧ lo ≤ j ∧ D (2 ^ i) (3 ^ j) = v := by
  simp only [searchB, List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨i, hi, j, hj, ⟨hli, hlj⟩, he⟩
    exact ⟨i, j, hi, hj, hli, hlj, he⟩
  · rintro ⟨i, j, hi, hj, hli, hlj, he⟩
    exact ⟨i, hi, j, hj, ⟨hli, hlj⟩, he⟩

/-- Under `RhinLog`, the search decides v. -/
theorem isPowDiff_iff_searchB (hR : RhinLog) {lo v B : ℕ} (hB : 28 ≤ B)
    (hv : (B ^ 14 + 1) * v < 2 ^ B) : IsPowDiff lo v ↔ searchB lo v B = true := by
  rw [isPowDiff_iff_lt hR hB hv, searchB_iff]

set_option exponentiation.threshold 500 in
/-- Under `RhinLog`, every v ≤ 10^30 is decided by the search over i, j < 300. -/
theorem isPowDiff_iff_searchB_300 (hR : RhinLog) {lo v : ℕ} (hv : v ≤ 10 ^ 30) :
    IsPowDiff lo v ↔ searchB lo v 300 = true := by
  apply isPowDiff_iff_searchB hR (by decide)
  have h : (300 ^ 14 + 1) * 10 ^ 30 < 2 ^ 300 := by decide +kernel
  calc (300 ^ 14 + 1) * v ≤ (300 ^ 14 + 1) * 10 ^ 30 := Nat.mul_le_mul_left _ hv
    _ < 2 ^ 300 := h

end PowDiff
