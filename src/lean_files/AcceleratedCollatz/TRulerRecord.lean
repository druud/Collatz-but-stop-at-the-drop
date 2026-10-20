-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.SmoothRuler
import AcceleratedCollatz.TBlockRecord
import AcceleratedCollatz.TCovering
import AcceleratedCollatz.TPersistent

/-!
  The steps of SmoothRuler.lean in the terms of the record Orders. A step that raises the
  exponent of 2 by P and lowers that of 3 by β (`StepAt 2 3 P β j`) is a step of an upper
  record Order: P = p2(β), β is an upper record Order, and every lower step 3^a / 2^(p2(a)-1)
  that fits at the start (p2(a) - 1 ≤ j) goes up by more (`stepAt_two_three_iff`). A step
  that raises the exponent of 3 by P and lowers that of 2 by β (`StepAt 3 2 P β j`) is a
  step of a lower record Order: β = p2(P) - 1, P ≥ 1 is a lower record Order, and every
  upper step 2^p2(i) / 3^i that fits at the start (i ≤ j) goes up by more
  (`stepAt_three_two_iff`).
-/

namespace AcceleratedCollatz

/-- 3^a 2^x ≠ 3^n 2^y for a < n. -/
theorem three_pow_mul_two_pow_ne {a n : ℕ} (h : a < n) (x y : ℕ) :
    3 ^ a * 2 ^ x ≠ 3 ^ n * 2 ^ y := by
  intro he
  have hd : 3 ^ (a + 1) ∣ 3 ^ a * 2 ^ x := by
    rw [he]
    exact Dvd.dvd.mul_right (Nat.pow_dvd_pow 3 h) _
  rw [pow_succ] at hd
  have h3 : 3 ∣ 2 ^ x := Nat.dvd_of_mul_dvd_mul_left (Nat.pow_pos (by norm_num)) hd
  have hc : Nat.Coprime 3 (2 ^ x) := Nat.Coprime.pow_right x (by decide)
  have h1 : 3 ∣ 1 := by
    rw [← Nat.Coprime.gcd_eq_one hc]
    exact Nat.dvd_gcd (dvd_refl 3) h3
  omega

/-- The block factors of 1 ≤ a and n compared as cross products. -/
theorem blockFactor_lt_iff_nat (a n : ℕ) :
    blockFactor a < blockFactor n ↔ 3 ^ a * 2 ^ p2_of n < 3 ^ n * 2 ^ p2_of a := by
  rw [blockFactor_eq, blockFactor_eq,
    div_lt_div_iff₀ (by positivity) (by positivity)]
  exact_mod_cast Iff.rfl

/-- 3^u < 2^v gives p2(u) ≤ v. -/
theorem p2_of_le_of_three_pow_lt {u v : ℕ} (h : 3 ^ u < 2 ^ v) : p2_of u ≤ v := by
  by_contra hlt
  push Not at hlt
  have h1 : 2 ^ v ≤ 2 ^ (p2_of u - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 := p2_of_spec_lower u
  omega

/-- A step 2^P / 3^β from a number with j factors 2 is a step of an upper record Order β
    with P = p2(β), and every lower step 3^a / 2^(p2(a)-1) that fits at the start goes up
    by more. -/
theorem stepAt_two_three_iff {P β j : ℕ} :
    SmoothRuler.StepAt 2 3 P β j ↔
      P = p2_of β ∧ UpperRecord β ∧
        ∀ a, 1 ≤ a → p2_of a - 1 ≤ j → 2 ^ (p2_of β + (p2_of a - 1)) < 3 ^ (a + β) := by
  constructor
  · rintro ⟨s1, s2, s3⟩
    have hP : P = p2_of β := by
      have h1 := s2 (p2_of β) β le_rfl (p2_of_spec β)
      have h2 : 2 ^ P ≤ 2 ^ p2_of β := Nat.le_of_mul_le_mul_right h1 (Nat.pow_pos (by norm_num))
      have h3 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h2
      have h4 := p2_of_spec_lower β
      have h5 : p2_of β - 1 < P := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp
        (lt_of_le_of_lt h4 s1)
      omega
    subst hP
    refine ⟨rfl, ?_, ?_⟩
    · rw [upperRecord_iff_blockFactor]
      intro a ha hab
      rw [blockFactor_lt_iff_nat]
      have h1 := s2 (p2_of a) a hab.le (p2_of_spec a)
      have h2 := three_pow_mul_two_pow_ne hab (p2_of β) (p2_of a)
      rw [Nat.mul_comm (2 ^ p2_of β), Nat.mul_comm (2 ^ p2_of a)] at h1
      omega
    · intro a ha hj
      have hlt : 2 ^ (p2_of a - 1) < 3 ^ a := by
        rw [two_pow_lt_three_pow_iff _ _ ha]
        have := p2_of_spec_lower 0
        have h2 : 1 ≤ p2_of a := by
          unfold p2_of
          omega
        omega
      have h1 := s3 (p2_of a - 1) a hj hlt
      have h2 := two_pow_ne_three_pow (p2_of β + (p2_of a - 1)) (a + β) (by
        unfold p2_of
        omega)
      omega
  · rintro ⟨rfl, hR, h3⟩
    have hp1 : 1 ≤ p2_of β := by
      unfold p2_of
      omega
    refine ⟨p2_of_spec β, ?_, ?_⟩
    · intro P' β' hβ hlt
      have hP' : p2_of β' ≤ P' := p2_of_le_of_three_pow_lt hlt
      have h2P : 2 ^ p2_of β' ≤ 2 ^ P' := Nat.pow_le_pow_right (by norm_num) hP'
      rcases Nat.lt_or_ge β' β with hb | hb
      · rcases Nat.eq_zero_or_pos β' with h0 | h0
        · subst h0
          have h2 := p2_of_spec_lower β
          have e : 2 ^ p2_of β = 2 * 2 ^ (p2_of β - 1) := by
            rw [← pow_succ', Nat.sub_add_cancel hp1]
          have h1 : p2_of 0 = 1 := by
            simp [p2_of]
          rw [h1, pow_one] at h2P
          rw [pow_zero, Nat.mul_one]
          calc 2 ^ p2_of β = 2 * 2 ^ (p2_of β - 1) := e
            _ ≤ 2 * 3 ^ β := Nat.mul_le_mul_left 2 h2
            _ ≤ 2 ^ P' * 3 ^ β := Nat.mul_le_mul_right _ h2P
        · have hf := (blockFactor_lt_iff_nat β' β).mp
            ((upperRecord_iff_blockFactor β).mp hR β' h0 hb)
          calc 2 ^ p2_of β * 3 ^ β' = 3 ^ β' * 2 ^ p2_of β := Nat.mul_comm _ _
            _ ≤ 3 ^ β * 2 ^ p2_of β' := hf.le
            _ ≤ 3 ^ β * 2 ^ P' := Nat.mul_le_mul_left _ h2P
            _ = 2 ^ P' * 3 ^ β := Nat.mul_comm _ _
      · have he : β' = β := le_antisymm hβ hb
        subst he
        exact Nat.mul_le_mul_right _ h2P
    · intro u' v' hu' hlt
      have hv : 1 ≤ v' := by
        by_contra h
        push Not at h
        rw [Nat.lt_one_iff.mp h, pow_zero] at hlt
        have := Nat.one_le_two_pow (n := u')
        omega
      have hu : u' < p2_of v' := (two_pow_lt_three_pow_iff _ _ hv).mp hlt
      rcases Nat.lt_or_ge j (p2_of v' - 1) with hj | hj
      · have e1 : p2_of β + u' ≤ (p2_of β - 1) + (p2_of v' - 1) := by
          omega
        calc 2 ^ (p2_of β + u') ≤ 2 ^ ((p2_of β - 1) + (p2_of v' - 1)) :=
              Nat.pow_le_pow_right (by norm_num) e1
          _ = 2 ^ (p2_of β - 1) * 2 ^ (p2_of v' - 1) := pow_add _ _ _
          _ ≤ 3 ^ β * 3 ^ v' := Nat.mul_le_mul (p2_of_spec_lower β) (p2_of_spec_lower v')
          _ = 3 ^ (v' + β) := by
              rw [pow_add, Nat.mul_comm]
      · have h1 := h3 v' hv hj
        have e1 : p2_of β + u' ≤ p2_of β + (p2_of v' - 1) := by
          omega
        exact le_trans (Nat.pow_le_pow_right (by norm_num) e1) h1.le

/-- 2^p2(n) = 2 · 2^(p2(n) - 1). -/
theorem two_pow_p2_of_eq (n : ℕ) : 2 ^ p2_of n = 2 * 2 ^ (p2_of n - 1) := by
  have h : 1 ≤ p2_of n := by
    unfold p2_of
    omega
  rw [← pow_succ', Nat.sub_add_cancel h]

/-- A step 3^P / 2^β from a number with j factors 3 is a step of a lower record Order P ≥ 1
    with β = p2(P) - 1, and every upper step 2^p2(i) / 3^i that fits at the start goes up
    by more. -/
theorem stepAt_three_two_iff {P β j : ℕ} :
    SmoothRuler.StepAt 3 2 P β j ↔
      1 ≤ P ∧ β = p2_of P - 1 ∧ LowerRecord P ∧
        ∀ i, i ≤ j → 3 ^ (P + i) < 2 ^ (p2_of i + β) := by
  constructor
  · rintro ⟨s1, s2, s3⟩
    have hP1 : 1 ≤ P := by
      by_contra h
      push Not at h
      rw [Nat.lt_one_iff.mp h, pow_zero] at s1
      have := Nat.one_le_two_pow (n := β)
      omega
    have hlt : β < p2_of P := (two_pow_lt_three_pow_iff _ _ hP1).mp s1
    have hge : p2_of P ≤ 1 + β := by
      have h1 := s3 0 1 (Nat.zero_le j) (by norm_num)
      have h2 := two_pow_ne_three_pow (1 + β) (P + 0) (by omega)
      exact p2_of_le_of_three_pow_lt (lt_of_le_of_ne h1 (Ne.symm h2))
    have hβ : β = p2_of P - 1 := by
      omega
    subst hβ
    refine ⟨hP1, rfl, ?_, ?_⟩
    · rw [lowerRecord_iff_blockFactor]
      intro a ha hab
      rw [blockFactor_lt_iff_nat]
      have hla : 2 ^ (p2_of a - 1) < 3 ^ a := by
        have h1 := p2_of_spec_lower a
        have h2 := two_pow_ne_three_pow (p2_of a - 1) a (by
          have := (two_pow_lt_three_pow_iff 1 a ha).mp (by
            calc 2 ^ 1 < 3 ^ 1 := by norm_num
              _ ≤ 3 ^ a := Nat.pow_le_pow_right (by norm_num) ha)
          omega)
        omega
      have hle : p2_of a - 1 ≤ p2_of P - 1 := by
        have h1 : 2 ^ (p2_of a - 1) < 2 ^ p2_of P :=
          lt_trans hla (lt_trans (Nat.pow_lt_pow_right (by norm_num) hab) (p2_of_spec P))
        have h2 := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp h1
        omega
      have h1 := s2 a (p2_of a - 1) hle hla
      have h2 := three_pow_mul_two_pow_ne hab (p2_of P) (p2_of a)
      have e1 := two_pow_p2_of_eq a
      have e2 := two_pow_p2_of_eq P
      have h3 : 3 ^ P * 2 ^ p2_of a ≤ 3 ^ a * 2 ^ p2_of P := by
        rw [e1, e2, Nat.mul_left_comm, Nat.mul_left_comm (3 ^ a)]
        exact Nat.mul_le_mul_left 2 h1
      omega
    · intro i hi
      have h1 := s3 i (p2_of i) hi (p2_of_spec i)
      have h2 := two_pow_ne_three_pow (p2_of i + (p2_of P - 1)) (P + i) (by
        unfold p2_of
        omega)
      omega
  · rintro ⟨hP1, rfl, hR, h3⟩
    have hp2 : 2 ≤ p2_of P := by
      have := (two_pow_lt_three_pow_iff 1 P hP1).mp (by
        calc 2 ^ 1 < 3 ^ 1 := by norm_num
          _ ≤ 3 ^ P := Nat.pow_le_pow_right (by norm_num) hP1)
      omega
    refine ⟨?_, ?_, ?_⟩
    · have h1 := p2_of_spec_lower P
      have h2 := two_pow_ne_three_pow (p2_of P - 1) P (by omega)
      omega
    · intro P' β' hβ hlt
      have hP'1 : 1 ≤ P' := by
        by_contra h
        push Not at h
        rw [Nat.lt_one_iff.mp h, pow_zero] at hlt
        have := Nat.one_le_two_pow (n := β')
        omega
      have hβ' : β' ≤ p2_of P' - 1 := by
        have := (two_pow_lt_three_pow_iff _ _ hP'1).mp hlt
        omega
      rcases Nat.lt_or_ge P' P with hP | hP
      · have hf := (blockFactor_lt_iff_nat P P').mp
          ((lowerRecord_iff_blockFactor P).mp hR P' hP'1 hP)
        have e1 := two_pow_p2_of_eq P'
        have e2 := two_pow_p2_of_eq P
        have h4 : 3 ^ P * 2 ^ (p2_of P' - 1) < 3 ^ P' * 2 ^ (p2_of P - 1) := by
          rw [e1, e2, Nat.mul_left_comm, Nat.mul_left_comm (3 ^ P')] at hf
          omega
        calc 3 ^ P * 2 ^ β' ≤ 3 ^ P * 2 ^ (p2_of P' - 1) :=
              Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hβ')
          _ ≤ 3 ^ P' * 2 ^ (p2_of P - 1) := h4.le
      · exact Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) hP)
          (Nat.pow_le_pow_right (by norm_num) hβ)
    · intro u' v' hu' hlt
      have h1 := h3 u' hu'
      have h2 : p2_of u' + (p2_of P - 1) ≤ v' + (p2_of P - 1) := by
        have := p2_of_le_of_three_pow_lt hlt
        omega
      exact le_trans h1.le (Nat.pow_le_pow_right (by norm_num) h2)

/-- The statement on exponents for the steps to fewer factors 3, over the upper record
    Orders β only. -/
def UpperGapRecords (M N : ℕ) : Prop :=
  ∀ β j u v : ℕ, p2_of β ≤ M → u ≤ M → β ≤ N → v ≤ N → UpperRecord β →
    (∀ a, 1 ≤ a → p2_of a - 1 ≤ j → 2 ^ (p2_of β + (p2_of a - 1)) < 3 ^ (a + β)) →
    j < u → u ≤ j + p2_of β → ¬SmoothRuler.GapAt 2 3 (p2_of β) β u v

/-- The statement on exponents for the steps to more factors 3, over the lower record
    Orders P ≥ 1 only. -/
def LowerGapRecords (M N : ℕ) : Prop :=
  ∀ P j u v : ℕ, P ≤ M → u ≤ M → p2_of P - 1 ≤ N → v ≤ N → 1 ≤ P → LowerRecord P →
    (∀ i, i ≤ j → 3 ^ (P + i) < 2 ^ (p2_of i + (p2_of P - 1))) →
    j < u → u ≤ j + P → ¬SmoothRuler.GapAt 3 2 P (p2_of P - 1) u v

/-- `OrdersGapFrame 2 3` is its statement over the upper record Orders. -/
theorem ordersGapFrame_two_three_iff {M N : ℕ} :
    SmoothRuler.OrdersGapFrame 2 3 M N ↔ UpperGapRecords M N := by
  constructor
  · intro h β j u v hP hu hβ hv hR hj hju huP
    exact h (p2_of β) β u v j hP hu hβ hv (stepAt_two_three_iff.mpr ⟨rfl, hR, hj⟩) hju huP
  · intro h P β u v j hP hu hβ hv hs hju huP
    obtain ⟨rfl, hR, hj⟩ := stepAt_two_three_iff.mp hs
    exact h β j u v hP hu hβ hv hR hj hju huP

/-- `OrdersGapFrame 3 2` is its statement over the lower record Orders. -/
theorem ordersGapFrame_three_two_iff {M N : ℕ} :
    SmoothRuler.OrdersGapFrame 3 2 M N ↔ LowerGapRecords M N := by
  constructor
  · intro h P j u v hP hu hβ hv hP1 hR hj hju huP
    exact h P (p2_of P - 1) u v j hP hu hβ hv (stepAt_three_two_iff.mpr ⟨hP1, rfl, hR, hj⟩)
      hju huP
  · intro h P β u v j hP hu hβ hv hs hju huP
    obtain ⟨hP1, rfl, hR, hj⟩ := stepAt_three_two_iff.mp hs
    exact h P j u v hP hu hβ hv hP1 hR hj hju huP

/-- The ruler gap for exponents of 2 up to J and of 3 up to I from the two statements over
    the record Orders. -/
theorem rulerGapUpTo_of_records {J I : ℕ} (hU : UpperGapRecords J I)
    (hL : LowerGapRecords I J) : SmoothRuler.RulerGapUpTo J I :=
  SmoothRuler.rulerGapUpTo_of_ordersGapFrame (ordersGapFrame_two_three_iff.mpr hU)
    (ordersGapFrame_three_two_iff.mpr hL)

/-- `RulerGap` is the two statements over the record Orders, without bounds. -/
theorem rulerGap_iff_records :
    SmoothRuler.RulerGap ↔ (∀ M N, UpperGapRecords M N) ∧ (∀ M N, LowerGapRecords M N) := by
  rw [SmoothRuler.rulerGap_iff_ordersGap, SmoothRuler.OrdersGap]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun M N => ordersGapFrame_two_three_iff.mp (h1 M N),
      fun M N => ordersGapFrame_three_two_iff.mp (h2 M N)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun M N => ordersGapFrame_two_three_iff.mpr (h1 M N),
      fun M N => ordersGapFrame_three_two_iff.mpr (h2 M N)⟩

end AcceleratedCollatz
