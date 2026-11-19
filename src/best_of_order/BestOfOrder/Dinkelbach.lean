-- SPDX-License-Identifier: MIT
import BestOfOrder.Bridge
import Mathlib.Algebra.Order.Field.Basic

/-!
  Dinkelbach's method on a finite set (paper, Lemma 5.1; Dinkelbach 1967), for the fractional
  program max num/den with den > 0, here num = rho and den = the class id. With
  F(λ) = max (num - λ den): F is strictly decreasing (`F_strictAnti`), F(λ*) = 0 at the largest
  ratio λ* (`F_lamStar`), F(λ) = 0 only at λ* (`eq_lamStar_of_F_eq_zero`), F is nonnegative at
  every ratio of the set (`F_ratio_nonneg`), and a step from a ratio with F > 0 to an argmax
  strictly raises the ratio (`step_lt`): from any start the steps reach λ* in finitely many.
-/

namespace BestOfOrder

variable {ι : Type*} (S : Finset ι) (hS : S.Nonempty) (num den : ι → ℚ)

/-- F(λ) = max over S of num - λ den. -/
def dinkF (lam : ℚ) : ℚ := S.sup' hS (fun i => num i - lam * den i)

/-- λ* = the largest num/den over S. -/
def lamStar : ℚ := S.sup' hS (fun i => num i / den i)

variable {S hS num den}

theorem F_strictAnti (hden : ∀ i ∈ S, 0 < den i) : StrictAnti (dinkF S hS num den) := by
  intro l1 l2 h12
  obtain ⟨i, hi, he⟩ := Finset.exists_mem_eq_sup' hS (fun i => num i - l2 * den i)
  unfold dinkF
  rw [he]
  have hle := Finset.le_sup' (fun i => num i - l1 * den i) hi
  have : num i - l2 * den i < num i - l1 * den i := by nlinarith [hden i hi]
  exact lt_of_lt_of_le this hle

theorem F_lamStar (hden : ∀ i ∈ S, 0 < den i) : dinkF S hS num den (lamStar S hS num den) = 0 := by
  apply le_antisymm
  · apply Finset.sup'_le
    intro i hi
    have h := Finset.le_sup' (fun i => num i / den i) hi
    have h' : num i / den i ≤ lamStar S hS num den := h
    rw [div_le_iff₀ (hden i hi)] at h'
    linarith
  · obtain ⟨j, hj, he⟩ := Finset.exists_mem_eq_sup' hS (fun i => num i / den i)
    have hle := Finset.le_sup' (fun i => num i - lamStar S hS num den * den i) hj
    have h0 : num j - lamStar S hS num den * den j = 0 := by
      have : lamStar S hS num den = num j / den j := he
      rw [this, div_mul_cancel₀ _ (hden j hj).ne']
      ring
    unfold dinkF
    linarith

theorem eq_lamStar_of_F_eq_zero (hden : ∀ i ∈ S, 0 < den i) {lam : ℚ}
    (h : dinkF S hS num den lam = 0) : lam = lamStar S hS num den :=
  (F_strictAnti hden).injective (h.trans (F_lamStar hden).symm)

theorem F_ratio_nonneg (hden : ∀ i ∈ S, 0 < den i) {i : ι} (hi : i ∈ S) :
    0 ≤ dinkF S hS num den (num i / den i) := by
  have hle := Finset.le_sup' (fun j => num j - num i / den i * den j) hi
  have h0 : num i - num i / den i * den i = 0 := by
    rw [div_mul_cancel₀ _ (hden i hi).ne']
    ring
  unfold dinkF
  linarith

/-- The step: an argmax j of num - λ den at λ = num i/den i with F(λ) > 0 has a larger ratio. -/
theorem step_lt (hden : ∀ i ∈ S, 0 < den i) {i j : ι} (hj : j ∈ S)
    (hmax : num j - num i / den i * den j = dinkF S hS num den (num i / den i))
    (hpos : 0 < dinkF S hS num den (num i / den i)) : num i / den i < num j / den j := by
  rw [lt_div_iff₀ (hden j hj)]
  linarith

end BestOfOrder
