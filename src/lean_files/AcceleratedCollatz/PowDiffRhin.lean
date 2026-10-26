-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.PowDiff
import AcceleratedCollatz.TRhinCheck

/-!
# The numbers |2^i - 3^j| for every bound, under an integer form of Rhin's bound

Companion of `PowDiff` (A014121 and A363999 up to a(3000) of A014121, unconditional).
Here, under `RhinInt`, every v is decided by a finite search. In integers only:

* `RhinInt`: when 2^i and 3^n lie within a factor 2 of each other (i ≥ 2, n ≥ 1), the
  smaller of the two is at most i^14 |2^i - 3^n|;
* so min(2^i, 3^j) ≤ H^14 |2^i - 3^j| for H = max(i, j) ≥ 2 (`min_le_of_rhinInt`): outside
  a factor 2 the bound is trivial;
* so 2^H ≤ (H^14 + 1) |2^i - 3^j| (`two_pow_max_le`);
* for B ≥ 28 with (B^14 + 1) v < 2^B, every H ≥ B has (H^14 + 1) v < 2^H
  (`lt_two_pow_of_le`, by (H + 1)^14 ≤ 2 H^14), so v = |2^i - 3^j| needs i, j < B
  (`isPowDiff_iff_lt`), and `searchB lo v B` decides it (`isPowDiff_iff_searchB`).

For v ≤ 10^30, B = 300 will do (`isPowDiff_iff_searchB_300`).

`RhinInt` follows from Rhin 1987, Proposition (7) (|u₁ log 2 + u₂ log 3| ≥ H^(-13.3) for
integers with H = max(|u₁|, |u₂|) ≥ 2), with u₁ = i, u₂ = -n, H = i, and
min(a, b) |log(a/b)| ≤ |a - b| (from log x ≤ x - 1). That step uses the reals and is not
part of this file (`TRhinLog` takes it for the upper side, `rhinBound_of_rhinLog`). For
n ≤ 10^60 the two sides hold with exponent 2 instead of 14, in integers only, by a certified
Stern-Brocot walk (`TRhinCheck`, `PowDiffWalk`).
-/

namespace PowDiff

open AcceleratedCollatz

/-- The integer form of Rhin's bound: for 2^i within a factor 2 of 3^n (i ≥ 2, n ≥ 1),
    the smaller of the two is at most i^14 |2^i - 3^n|. -/
structure RhinInt : Prop where
  upper : ∀ i n, 2 ≤ i → 1 ≤ n → 3 ^ n < 2 ^ i → 2 ^ i < 2 * 3 ^ n →
    3 ^ n ≤ i ^ 14 * (2 ^ i - 3 ^ n)
  lower : ∀ i n, 2 ≤ i → 1 ≤ n → 2 ^ i < 3 ^ n → 3 ^ n < 2 * 2 ^ i →
    2 ^ i ≤ i ^ 14 * (3 ^ n - 2 ^ i)

/-- Under `RhinInt`: min(2^i, 3^j) ≤ H^14 |2^i - 3^j| with H = max(i, j) ≥ 2. -/
theorem min_le_of_rhinInt (hR : RhinInt) {i j : ℕ} (hH : 2 ≤ max i j) :
    min (2 ^ i) (3 ^ j) ≤ max i j ^ 14 * D (2 ^ i) (3 ^ j) := by
  have hH1 : 1 ≤ max i j ^ 14 := Nat.one_le_pow _ _ (by omega)
  have hi : i ^ 14 ≤ max i j ^ 14 := Nat.pow_le_pow_left (le_max_left i j) 14
  have h2 : 2 ^ i ≤ 2 ^ 1 ∨ 4 ≤ 2 ^ i := by
    rcases Nat.lt_or_ge i 2 with h | h
    · exact Or.inl (Nat.pow_le_pow_right (by decide) (by omega))
    · exact Or.inr (by simpa using Nat.pow_le_pow_right (by decide : 0 < 2) h)
  have h3 : j = 0 ∨ 3 ≤ 3 ^ j := by
    rcases Nat.eq_zero_or_pos j with h | h
    · exact Or.inl h
    · exact Or.inr (by simpa using Nat.pow_le_pow_right (by decide : 0 < 3) h)
  have h9 : j ≤ 1 ∨ 9 ≤ 3 ^ j := by
    rcases Nat.lt_or_ge j 2 with h | h
    · exact Or.inl (by omega)
    · exact Or.inr (by simpa using Nat.pow_le_pow_right (by decide : 0 < 3) h)
  have hpos : 1 ≤ 2 ^ i := Nat.one_le_two_pow
  unfold D
  by_cases hm : min (2 ^ i) (3 ^ j) ≤ 2 ^ i - 3 ^ j + (3 ^ j - 2 ^ i)
  · exact hm.trans (Nat.le_mul_of_pos_left _ hH1)
  rcases lt_trichotomy (3 ^ j) (2 ^ i) with hlt | heq | hgt
  · -- 3^j < 2^i < 2 3^j: the upper side
    rw [min_eq_right hlt.le] at hm ⊢
    have hj : 1 ≤ j := by
      rcases h3 with h | h
      · subst h; rw [pow_zero] at hm hlt; omega
      · rcases Nat.eq_zero_or_pos j with h' | h'
        · subst h'; simp at h
        · exact h'
    have hi2 : 2 ≤ i := by
      rcases h2 with h | h
      · rcases h3 with h' | h' <;> omega
      · by_contra hc
        have : 2 ^ i ≤ 2 ^ 1 := Nat.pow_le_pow_right (by decide) (by omega)
        omega
    have hu := hR.upper i j hi2 hj hlt (by omega)
    calc 3 ^ j ≤ i ^ 14 * (2 ^ i - 3 ^ j) := hu
      _ ≤ max i j ^ 14 * (2 ^ i - 3 ^ j) := Nat.mul_le_mul_right _ hi
      _ = max i j ^ 14 * (2 ^ i - 3 ^ j + (3 ^ j - 2 ^ i)) := by
        rw [Nat.sub_eq_zero_of_le hlt.le, Nat.add_zero]
  · -- 2^i = 3^j only for i = j = 0: 3^j is odd, 2^i even for i ≥ 1
    rcases Nat.eq_zero_or_pos i with h' | h'
    · subst h'
      rw [pow_zero] at heq
      rcases h3 with h | h
      · subst h; simp at hH
      · omega
    · have he : Even (2 ^ i) := (Nat.even_pow' (by omega)).mpr even_two
      have ho : Odd (3 ^ j) := Odd.pow (by decide)
      rw [heq] at ho
      exact absurd he (Nat.not_even_iff_odd.mpr ho)
  · -- 2^i < 3^j < 2 2^i: the lower side
    rw [min_eq_left hgt.le] at hm ⊢
    have hj : 1 ≤ j := by
      rcases Nat.eq_zero_or_pos j with h | h
      · subst h; rw [pow_zero] at hgt; omega
      · exact h
    have hi2 : 2 ≤ i := by
      by_contra hc
      have : 2 ^ i ≤ 2 ^ 1 := Nat.pow_le_pow_right (by decide) (by omega)
      rcases h9 with h | h
      · omega
      · omega
    have hl := hR.lower i j hi2 hj hgt (by omega)
    calc 2 ^ i ≤ i ^ 14 * (3 ^ j - 2 ^ i) := hl
      _ ≤ max i j ^ 14 * (3 ^ j - 2 ^ i) := Nat.mul_le_mul_right _ hi
      _ = max i j ^ 14 * (2 ^ i - 3 ^ j + (3 ^ j - 2 ^ i)) := by
        rw [Nat.sub_eq_zero_of_le hgt.le, Nat.zero_add]

/-- Under `RhinInt`: 2^H ≤ (H^14 + 1) |2^i - 3^j| with H = max(i, j) ≥ 2. -/
theorem two_pow_max_le (hR : RhinInt) {i j : ℕ} (hH : 2 ≤ max i j) :
    2 ^ max i j ≤ (max i j ^ 14 + 1) * D (2 ^ i) (3 ^ j) := by
  have hm := min_le_of_rhinInt hR hH
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

/-- Under `RhinInt`, for B ≥ 28 with (B^14 + 1) v < 2^B: v = |2^i - 3^j| with i, j ≥ lo
    exactly when it is so with i, j < B. -/
theorem isPowDiff_iff_lt (hR : RhinInt) {lo v B : ℕ} (hB : 28 ≤ B)
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

/-- Under `RhinInt`, the search decides v. -/
theorem isPowDiff_iff_searchB (hR : RhinInt) {lo v B : ℕ} (hB : 28 ≤ B)
    (hv : (B ^ 14 + 1) * v < 2 ^ B) : IsPowDiff lo v ↔ searchB lo v B = true := by
  rw [isPowDiff_iff_lt hR hB hv, searchB_iff]

set_option exponentiation.threshold 500 in
/-- Under `RhinInt`, every v ≤ 10^30 is decided by the search over i, j < 300. -/
theorem isPowDiff_iff_searchB_300 (hR : RhinInt) {lo v : ℕ} (hv : v ≤ 10 ^ 30) :
    IsPowDiff lo v ↔ searchB lo v 300 = true := by
  apply isPowDiff_iff_searchB hR (by decide)
  have h : (300 ^ 14 + 1) * 10 ^ 30 < 2 ^ 300 := by decide +kernel
  calc (300 ^ 14 + 1) * v ≤ (300 ^ 14 + 1) * 10 ^ 30 := Nat.mul_le_mul_left _ hv
    _ < 2 ^ 300 := h

end PowDiff
