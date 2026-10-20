-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.DropEquivalence
import AcceleratedCollatz.TCovering

/-!
  Global link between R and T. For x > 1, R x = T^(rSteps x) x with
  rSteps x ≥ 1, and every T-value inside that macro-step is at least
  min(x, R x) (`R_eq_tStep_iterate`). Hence x drops under R iff it drops
  under T (`rDrop_iff_tDrop`), and DropConjecture lies between
  Covering ∧ WidthIdentity and Covering.
-/

namespace AcceleratedCollatz

variable (x : ℕ)

open DescendToMinimum

/-- Number of T-steps in one R-step. -/
def rSteps (x : ℕ) : ℕ := if x % 2 = 1 then trailingOnes x + 1 else trailingZeros x

/-- One R-step is rSteps x T-steps, with no T-value below min(x, R x). -/
theorem R_eq_tStep_iterate (hx : 1 < x) :
    R x = tStep^[rSteps x] x ∧ 1 ≤ rSteps x ∧
      ∀ j ≤ rSteps x, min x (R x) ≤ tStep^[j] x := by
  by_cases hodd : x % 2 = 1
  · obtain ⟨_, hb, hc⟩ := traceOK_odd x x hx hodd le_rfl
    have hlen : (List.replicate (trailingOnes x) true ++ [false]).length = trailingOnes x + 1 := by
      simp
    rw [hlen] at hb hc
    have hr : rSteps x = trailingOnes x + 1 := by
      simp [rSteps, hodd]
    rw [hr]
    refine ⟨hb.symm, by omega, ?_⟩
    intro j hj
    rcases Nat.lt_or_ge j (trailingOnes x + 1) with hlt | hge
    · have := hc j hlt
      omega
    · have hj' : j = trailingOnes x + 1 := by
        omega
      rw [hj', hb]
      omega
  · have hEven : Even x := Nat.even_iff.mpr (by omega)
    have hdvd : 2 ^ trailingZeros x ∣ x := pow_padicValNat_dvd
    have hit := tStep_iterate_of_pow_dvd x (trailingZeros x) hdvd
    have hRx : R x = x / 2 ^ trailingZeros x := R_even_closed_form x hx hEven
    have hr : rSteps x = trailingZeros x := by
      simp [rSteps, hodd]
    have hv1 : 1 ≤ trailingZeros x := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact one_le_padicValNat_of_dvd (by omega) (even_iff_two_dvd.mp hEven)
    rw [hr]
    refine ⟨by rw [hRx, hit (trailingZeros x) le_rfl], hv1, ?_⟩
    intro j hj
    rw [hit j hj]
    have hle : x / 2 ^ trailingZeros x ≤ x / 2 ^ j :=
      Nat.div_le_div_left (Nat.pow_le_pow_right (by norm_num) hj) (by positivity)
    omega

/-- R-iterates are T-iterates while all intermediate R-values exceed 1. -/
theorem rIterate_eq_tIterate :
    ∀ k y, (∀ j < k, 1 < R^[j] y) → ∃ M, k ≤ M ∧ R^[k] y = tStep^[M] y := by
  intro k
  induction k with
  | zero =>
    intro y _
    exact ⟨0, le_rfl, rfl⟩
  | succ k ih =>
    intro y h
    have hy : 1 < y := h 0 (by omega)
    obtain ⟨hR, hr1, _⟩ := R_eq_tStep_iterate y hy
    have h' : ∀ j < k, 1 < R^[j] (R y) := by
      intro j hj
      have := h (j + 1) (by omega)
      rwa [Function.iterate_succ_apply] at this
    obtain ⟨M, hM, hMeq⟩ := ih (R y) h'
    refine ⟨M + rSteps y, by omega, ?_⟩
    rw [Function.iterate_succ_apply, hMeq, hR, ← Function.iterate_add_apply]

/-- A T-value below x, reached from an R-point y ≥ x, forces an R-value below x. -/
theorem exists_rIterate_lt (hx : 1 < x) :
    ∀ n y, x ≤ y → tStep^[n] y < x → ∃ k, R^[k] y < x := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro y hy hn
    obtain ⟨hR, hr1, hmin⟩ := R_eq_tStep_iterate y (by omega)
    by_cases hle : n ≤ rSteps y
    · have hm := hmin n hle
      refine ⟨1, ?_⟩
      rw [Function.iterate_one]
      omega
    · by_cases hRy : R y < x
      · refine ⟨1, ?_⟩
        rw [Function.iterate_one]
        exact hRy
      · have hsplit : tStep^[n] y = tStep^[n - rSteps y] (R y) := by
          rw [hR, ← Function.iterate_add_apply, Nat.sub_add_cancel (by omega)]
        rw [hsplit] at hn
        obtain ⟨k, hk⟩ := ih (n - rSteps y) (by omega) (R y) (by omega) hn
        refine ⟨k + 1, ?_⟩
        rw [Function.iterate_succ_apply]
        exact hk

/-- For x > 1: x drops under R iff x drops under T. -/
theorem rDrop_iff_tDrop_at (hx : 1 < x) :
    (∃ k ≥ 1, R^[k] x < x) ↔ (∃ n ≥ 1, tStep^[n] x < x) := by
  constructor
  · intro h
    have hex : ∃ k, 1 ≤ k ∧ R^[k] x < x := by
      obtain ⟨k, hk1, hk⟩ := h
      exact ⟨k, hk1, hk⟩
    obtain ⟨hk1, hk⟩ := Nat.find_spec hex
    have hpre : ∀ j < Nat.find hex, 1 < R^[j] x := by
      intro j hj
      rcases Nat.eq_zero_or_pos j with h0 | hpos
      · rw [h0, Function.iterate_zero, id_eq]
        exact hx
      · have hmin := Nat.find_min hex hj
        push Not at hmin
        have := hmin hpos
        omega
    obtain ⟨M, hM, hMeq⟩ := rIterate_eq_tIterate (Nat.find hex) x hpre
    refine ⟨M, by omega, ?_⟩
    rw [← hMeq]
    exact hk
  · rintro ⟨n, _, hn⟩
    obtain ⟨k, hk⟩ := exists_rIterate_lt x hx n x le_rfl hn
    refine ⟨k, ?_, hk⟩
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · rw [h0, Function.iterate_zero, id_eq] at hk
      omega
    · exact hpos

theorem rDrop_iff_tDrop : DropConjecture ↔ DropsToward tStep 1 := by
  constructor
  · intro h x hx
    exact (rDrop_iff_tDrop_at x hx).mp (h x hx)
  · intro h x hx
    exact (rDrop_iff_tDrop_at x hx).mpr (h x hx)

/-- Covering ∧ WidthIdentity → DropConjecture. -/
theorem drop_of_covering_width (hC : Covering) (hW : WidthIdentity) : DropConjecture :=
  rDrop_iff_tDrop.mpr (drops_of_covering_width hC hW)

/-- DropConjecture → Covering. -/
theorem covering_of_drop (h : DropConjecture) : Covering :=
  covering_of_drops (rDrop_iff_tDrop.mp h)

end AcceleratedCollatz
