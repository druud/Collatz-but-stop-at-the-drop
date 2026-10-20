-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TRhinCheck
import AcceleratedCollatz.TRulerPair

/-!
  The pair conditions of `rulerGap_iff_pairs` for every pair of neighbouring record Orders
  up to 10^60: for upper record Orders b < b' ≤ 10^60 with no upper record Order between
  them, no upper record Order c with b' ≤ c ≤ b + b' has `UpperDeficitLt b c`
  (`upperPairs_upTo`); for lower record Orders 1 ≤ P < P' ≤ 10^60 with no lower record Order
  between them, no lower record Order c with P' ≤ c < P + P' has `LowerDeficitLt P c`
  (`lowerPairs_upTo`).
  Both inequalities fail when (Y_b - X_b)^2 Y_c ≤ (Y_c - X_c) Y_b^2, with X = 3^n,
  Y = 2^p2(n) for the upper ones and X = 2^(p2(n) - 1), Y = 3^n for the lower ones
  (`not_upperDeficitLt_of`, `not_lowerDeficitLt_of`). That form is checked exactly for
  c ≤ 100 and otherwise from a bracket 2^lo ≤ 3^K < 2^hi: X^K 2^m ≤ Y^K gives
  Y < (M + 1)(Y - X) (`lt_mul_sub_of_pow`), Y^K ≤ X^K 2^m gives (N + 1)(Y - X) < Y
  (`mul_sub_lt_of_pow`), and M + 1 ≤ (N + 1)^2 closes it (`gapSq_of_bounds`).
  A certified walk at K = 2^500 stops at every step that changes the denominator above
  (below) and scans the window of that pair (`rulerPairWalk_spec`, `rulerWin_spec`); it is
  computed by the kernel (`rulerUpWalk_ok`, `rulerLowWalk_ok`).
  With an upper and a lower record Order between 10^59 and 10^60 (`exists_records_between`)
  every record Order b, P ≤ 10^59 has its next one at most 10^60, so the ruler gap holds for
  every exponent of 2 and every exponent of 3 up to 10^59 (`rulerGapUpTo_ten_pow`).
-/

namespace AcceleratedCollatz

/-! ### The gap from powers -/

/-- X^K 2^m ≤ Y^K with K/(M/2) + 1 < m gives Y < (M + 1)(Y - X). -/
theorem lt_mul_sub_of_pow {X Y K m M : ℕ} (hX : 1 ≤ X) (hM : 2 ≤ M)
    (h : X ^ K * 2 ^ m ≤ Y ^ K) (hm : K / (M / 2) + 1 < m) : Y < (M + 1) * (Y - X) := by
  have hXK : 0 < X ^ K := Nat.pow_pos (by omega)
  rcases Nat.lt_or_ge X Y with hXY | hXY
  · obtain ⟨D, rfl⟩ : ∃ D, Y = X + D := ⟨Y - X, by omega⟩
    rw [Nat.add_sub_cancel_left]
    by_contra hle
    push Not at hle
    have h1 : M * D ≤ X := by nlinarith
    have h2 : M * (X + D) ≤ (M + 1) * X := by nlinarith
    have h3 : M ^ K * (X + D) ^ K ≤ (M + 1) ^ K * X ^ K := by
      rw [← Nat.mul_pow, ← Nat.mul_pow]
      exact Nat.pow_le_pow_left h2 K
    have h4 := succ_pow_le hM K
    have hMK : 0 < M ^ K := Nat.pow_pos (by omega)
    have h5 : M ^ K * (X + D) ^ K ≤ M ^ K * (2 ^ (K / (M / 2) + 1) * X ^ K) := by
      calc M ^ K * (X + D) ^ K ≤ (M + 1) ^ K * X ^ K := h3
        _ ≤ 2 ^ (K / (M / 2) + 1) * M ^ K * X ^ K := Nat.mul_le_mul_right _ h4
        _ = M ^ K * (2 ^ (K / (M / 2) + 1) * X ^ K) := by ring
    have h6 := Nat.le_of_mul_le_mul_left h5 hMK
    have h7 : X ^ K * 2 ^ m ≤ X ^ K * 2 ^ (K / (M / 2) + 1) := by
      calc X ^ K * 2 ^ m ≤ (X + D) ^ K := h
        _ ≤ 2 ^ (K / (M / 2) + 1) * X ^ K := h6
        _ = X ^ K * 2 ^ (K / (M / 2) + 1) := Nat.mul_comm _ _
    have h8 := Nat.le_of_mul_le_mul_left h7 hXK
    have h9 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h8
    omega
  · exfalso
    have h1 : Y ^ K ≤ X ^ K := Nat.pow_le_pow_left hXY K
    have h2 : X ^ K * 2 ^ m ≤ X ^ K * 1 := by
      rw [Nat.mul_one]
      exact h.trans h1
    have h3 := Nat.le_of_mul_le_mul_left h2 hXK
    have hm1 : 1 ≤ m := (Nat.lt_of_le_of_lt (Nat.le_add_left 1 (K / (M / 2))) hm).le
    have h4 : 2 ^ 1 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm1
    omega

/-- Y^K ≤ X^K 2^m with m < 2 (K/(2N)) gives (N + 1)(Y - X) < Y. -/
theorem mul_sub_lt_of_pow {X Y K m N : ℕ} (hX : 1 ≤ X) (hY : 1 ≤ Y) (hN : 1 ≤ N)
    (h : Y ^ K ≤ X ^ K * 2 ^ m) (hm : m < 2 * (K / (2 * N))) : (N + 1) * (Y - X) < Y := by
  rcases Nat.lt_or_ge X Y with hXY | hXY
  · obtain ⟨D, rfl⟩ : ∃ D, Y = X + D := ⟨Y - X, by omega⟩
    rw [Nat.add_sub_cancel_left]
    by_contra hle
    push Not at hle
    have h1 : X ≤ N * D := by nlinarith
    have h2 : (N + 1) * X ≤ N * (X + D) := by nlinarith
    have h3 : (N + 1) ^ K * X ^ K ≤ N ^ K * (X + D) ^ K := by
      rw [← Nat.mul_pow, ← Nat.mul_pow]
      exact Nat.pow_le_pow_left h2 K
    have hk : 2 * (K / (2 * N)) * N ≤ K := by
      have := Nat.div_mul_le_self K (2 * N)
      calc 2 * (K / (2 * N)) * N = K / (2 * N) * (2 * N) := by ring
        _ ≤ K := this
    have h4 := four_pow_mul_le hN hk
    have hNX : 0 < N ^ K * X ^ K := Nat.mul_pos (Nat.pow_pos (by omega)) (Nat.pow_pos (by omega))
    have h5 : N ^ K * X ^ K * 4 ^ (K / (2 * N)) ≤ N ^ K * X ^ K * 2 ^ m := by
      calc N ^ K * X ^ K * 4 ^ (K / (2 * N)) = 4 ^ (K / (2 * N)) * N ^ K * X ^ K := by ring
        _ ≤ (N + 1) ^ K * X ^ K := Nat.mul_le_mul_right _ h4
        _ ≤ N ^ K * (X + D) ^ K := h3
        _ ≤ N ^ K * (X ^ K * 2 ^ m) := Nat.mul_le_mul_left _ h
        _ = N ^ K * X ^ K * 2 ^ m := by ring
    have h6 := Nat.le_of_mul_le_mul_left h5 hNX
    have e : (4 : ℕ) ^ (K / (2 * N)) = 2 ^ (2 * (K / (2 * N))) := by
      rw [pow_mul]
      norm_num
    rw [e] at h6
    have h7 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h6
    omega
  · rw [Nat.sub_eq_zero_of_le hXY, Nat.mul_zero]
    omega

/-- Y_c < (M + 1)(Y_c - X_c), (N + 1)(Y_b - X_b) < Y_b and M + 1 ≤ (N + 1)^2 give
    (Y_b - X_b)^2 Y_c ≤ (Y_c - X_c) Y_b^2. -/
theorem gapSq_of_bounds {Xb Yb Xc Yc M N : ℕ} (hc : Yc < (M + 1) * (Yc - Xc))
    (hb : (N + 1) * (Yb - Xb) < Yb) (hMN : M + 1 ≤ (N + 1) ^ 2) :
    (Yb - Xb) ^ 2 * Yc ≤ (Yc - Xc) * Yb ^ 2 := by
  have h1 : ((N + 1) * (Yb - Xb)) ^ 2 ≤ Yb ^ 2 := Nat.pow_le_pow_left hb.le 2
  calc (Yb - Xb) ^ 2 * Yc ≤ (Yb - Xb) ^ 2 * ((M + 1) * (Yc - Xc)) :=
        Nat.mul_le_mul_left _ hc.le
    _ ≤ (Yb - Xb) ^ 2 * ((N + 1) ^ 2 * (Yc - Xc)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hMN)
    _ = ((N + 1) * (Yb - Xb)) ^ 2 * (Yc - Xc) := by ring
    _ ≤ Yb ^ 2 * (Yc - Xc) := Nat.mul_le_mul_right _ h1
    _ = (Yc - Xc) * Yb ^ 2 := Nat.mul_comm _ _

/-! ### The checks at a pair -/

/-- The two gap bounds from mc (at c) and mb (at b), with M = 2 (K/(mc - 2) + 1) and
    N = K/(mb + 2). -/
def gapBoundsOK (K mc mb : ℕ) : Bool :=
  decide (1 ≤ K / (mb + 2)) && decide (2 ≤ 2 * (K / (mc - 2) + 1)) &&
    decide (K / (2 * (K / (mc - 2) + 1) / 2) + 1 < mc) &&
    decide (mb < 2 * (K / (2 * (K / (mb + 2))))) &&
    decide (2 * (K / (mc - 2) + 1) + 1 ≤ (K / (mb + 2) + 1) ^ 2)

/-- The checked bounds give numbers M, N for `gapSq_of_bounds`. -/
theorem gapBoundsOK_spec {K mc mb : ℕ} (h : gapBoundsOK K mc mb = true) :
    ∃ M N, 2 ≤ M ∧ 1 ≤ N ∧ K / (M / 2) + 1 < mc ∧ mb < 2 * (K / (2 * N)) ∧
      M + 1 ≤ (N + 1) ^ 2 := by
  unfold gapBoundsOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨_, _, h2, h1, h3, h4, h5⟩

/-- The upper check at b < c with numerators pb, pc: exact for c ≤ 100, else from the
    bracket lo, hi of log2 3 at K. -/
def rulerUpOK (K lo hi pb b pc c : ℕ) : Bool :=
  if c ≤ 100 then decide ((2 ^ pb - 3 ^ b) ^ 2 * 2 ^ pc ≤ (2 ^ pc - 3 ^ c) * (2 ^ pb) ^ 2)
  else gapBoundsOK K (pc * K - hi * c) (pb * K - lo * b)

/-- The lower check at P < c with numerators pP, pc: exact for c ≤ 100, else from the
    bracket lo, hi of log2 3 at K. -/
def rulerLowOK (K lo hi pP P pc c : ℕ) : Bool :=
  if c ≤ 100 then decide ((3 ^ P - 2 ^ pP) ^ 2 * 3 ^ c ≤ (3 ^ c - 2 ^ pc) * (3 ^ P) ^ 2)
  else gapBoundsOK K (lo * c - pc * K) (hi * P - pP * K)

/-- (3^n)^K = (3^K)^n. -/
theorem pow_pow_comm (x n K : ℕ) : (x ^ n) ^ K = (x ^ K) ^ n := by
  rw [← pow_mul, ← pow_mul, Nat.mul_comm]

/-- The upper check gives (2^pb - 3^b)^2 2^pc ≤ (2^pc - 3^c) (2^pb)^2. -/
theorem rulerUpOK_spec {K lo hi pb b pc c : ℕ} (hbr : Log2Bracket K lo hi)
    (h : rulerUpOK K lo hi pb b pc c = true) :
    (2 ^ pb - 3 ^ b) ^ 2 * 2 ^ pc ≤ (2 ^ pc - 3 ^ c) * (2 ^ pb) ^ 2 := by
  unfold rulerUpOK at h
  by_cases hc : c ≤ 100
  · rw [ite_eq_left hc] at h
    exact of_decide_eq_true h
  · rw [ite_eq_right hc] at h
    obtain ⟨M, N, hM, hN, hmc, hmb, hMN⟩ := gapBoundsOK_spec h
    have hlo : (2 ^ lo) ^ b ≤ (3 ^ K) ^ b := Nat.pow_le_pow_left hbr.1 b
    have hhi : (3 ^ K) ^ c ≤ (2 ^ hi) ^ c := Nat.pow_le_pow_left hbr.2.le c
    have hmc1 : 1 ≤ pc * K - hi * c :=
      (Nat.lt_of_le_of_lt (Nat.le_add_left 1 (K / (M / 2))) hmc).le
    have hXc : (3 ^ c) ^ K * 2 ^ (pc * K - hi * c) ≤ (2 ^ pc) ^ K := by
      calc (3 ^ c) ^ K * 2 ^ (pc * K - hi * c) = (3 ^ K) ^ c * 2 ^ (pc * K - hi * c) := by
            rw [pow_pow_comm]
        _ ≤ (2 ^ hi) ^ c * 2 ^ (pc * K - hi * c) := Nat.mul_le_mul_right _ hhi
        _ = 2 ^ (hi * c + (pc * K - hi * c)) := by
            rw [← pow_mul, ← pow_add]
        _ = 2 ^ (pc * K) := by
            congr 1
            omega
        _ = (2 ^ pc) ^ K := pow_mul _ _ _
    have hYb : (2 ^ pb) ^ K ≤ (3 ^ b) ^ K * 2 ^ (pb * K - lo * b) := by
      calc (2 ^ pb) ^ K = 2 ^ (pb * K) := (pow_mul _ _ _).symm
        _ ≤ 2 ^ (lo * b + (pb * K - lo * b)) := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = (2 ^ lo) ^ b * 2 ^ (pb * K - lo * b) := by
            rw [← pow_mul, ← pow_add]
        _ ≤ (3 ^ K) ^ b * 2 ^ (pb * K - lo * b) := Nat.mul_le_mul_right _ hlo
        _ = (3 ^ b) ^ K * 2 ^ (pb * K - lo * b) := by
            rw [pow_pow_comm 3 b]
    exact gapSq_of_bounds (lt_mul_sub_of_pow (Nat.pow_pos (by norm_num)) hM hXc hmc)
      (mul_sub_lt_of_pow (Nat.pow_pos (by norm_num)) Nat.one_le_two_pow hN hYb hmb) hMN

/-- The lower check gives (3^P - 2^pP)^2 3^c ≤ (3^c - 2^pc) (3^P)^2. -/
theorem rulerLowOK_spec {K lo hi pP P pc c : ℕ} (hbr : Log2Bracket K lo hi)
    (h : rulerLowOK K lo hi pP P pc c = true) :
    (3 ^ P - 2 ^ pP) ^ 2 * 3 ^ c ≤ (3 ^ c - 2 ^ pc) * (3 ^ P) ^ 2 := by
  unfold rulerLowOK at h
  by_cases hc : c ≤ 100
  · rw [ite_eq_left hc] at h
    exact of_decide_eq_true h
  · rw [ite_eq_right hc] at h
    obtain ⟨M, N, hM, hN, hmc, hmb, hMN⟩ := gapBoundsOK_spec h
    have hlo : (2 ^ lo) ^ c ≤ (3 ^ K) ^ c := Nat.pow_le_pow_left hbr.1 c
    have hhi : (3 ^ K) ^ P ≤ (2 ^ hi) ^ P := Nat.pow_le_pow_left hbr.2.le P
    have hmc1 : 1 ≤ lo * c - pc * K :=
      (Nat.lt_of_le_of_lt (Nat.le_add_left 1 (K / (M / 2))) hmc).le
    have hXc : (2 ^ pc) ^ K * 2 ^ (lo * c - pc * K) ≤ (3 ^ c) ^ K := by
      calc (2 ^ pc) ^ K * 2 ^ (lo * c - pc * K) = 2 ^ (pc * K + (lo * c - pc * K)) := by
            rw [← pow_mul, ← pow_add]
        _ = (2 ^ lo) ^ c := by
            rw [← pow_mul]
            congr 1
            omega
        _ ≤ (3 ^ K) ^ c := hlo
        _ = (3 ^ c) ^ K := (pow_pow_comm 3 c K).symm
    have hYb : (3 ^ P) ^ K ≤ (2 ^ pP) ^ K * 2 ^ (hi * P - pP * K) := by
      calc (3 ^ P) ^ K = (3 ^ K) ^ P := pow_pow_comm 3 P K
        _ ≤ (2 ^ hi) ^ P := hhi
        _ = 2 ^ (hi * P) := (pow_mul _ _ _).symm
        _ ≤ 2 ^ (pP * K + (hi * P - pP * K)) := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = (2 ^ pP) ^ K * 2 ^ (hi * P - pP * K) := by
            rw [← pow_mul, ← pow_add]
    exact gapSq_of_bounds (lt_mul_sub_of_pow Nat.one_le_two_pow hM hXc hmc)
      (mul_sub_lt_of_pow Nat.one_le_two_pow (Nat.pow_pos (by norm_num)) hN hYb hmb) hMN

/-! ### From the gap form to the deficit inequalities -/

/-- The gap form at b and c gives `¬UpperDeficitLt b c`. -/
theorem not_upperDeficitLt_of {b c : ℕ}
    (h : (2 ^ p2_of b - 3 ^ b) ^ 2 * 2 ^ p2_of c ≤ (2 ^ p2_of c - 3 ^ c) * (2 ^ p2_of b) ^ 2) :
    ¬UpperDeficitLt b c := by
  have hb := (p2_of_spec b).le
  have hc := (p2_of_spec c).le
  have h' : (((2 ^ p2_of b - 3 ^ b) ^ 2 * 2 ^ p2_of c : ℕ) : ℤ) ≤
      (((2 ^ p2_of c - 3 ^ c) * (2 ^ p2_of b) ^ 2 : ℕ) : ℤ) := by
    exact_mod_cast h
  push_cast [Nat.cast_sub hb, Nat.cast_sub hc] at h'
  have e : (4 : ℤ) ^ p2_of b = ((2 : ℤ) ^ p2_of b) ^ 2 := by
    rw [show (4 : ℤ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul, Nat.mul_comm]
  unfold UpperDeficitLt
  rw [e]
  linarith

/-- The gap form at P and c gives `¬LowerDeficitLt P c`. -/
theorem not_lowerDeficitLt_of {P c : ℕ}
    (h : (3 ^ P - 2 ^ (p2_of P - 1)) ^ 2 * 3 ^ c ≤
      (3 ^ c - 2 ^ (p2_of c - 1)) * (3 ^ P) ^ 2) :
    ¬LowerDeficitLt P c := by
  have hP := p2_of_spec_lower P
  have hc := p2_of_spec_lower c
  have h' : (((3 ^ P - 2 ^ (p2_of P - 1)) ^ 2 * 3 ^ c : ℕ) : ℤ) ≤
      (((3 ^ c - 2 ^ (p2_of c - 1)) * (3 ^ P) ^ 2 : ℕ) : ℤ) := by
    exact_mod_cast h
  push_cast [Nat.cast_sub hP, Nat.cast_sub hc] at h'
  have eP : (2 : ℤ) ^ p2_of P = 2 * 2 ^ (p2_of P - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel (one_le_p2_of P)]
  have ec : (2 : ℤ) ^ p2_of c = 2 * 2 ^ (p2_of c - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel (one_le_p2_of c)]
  have hPz : ((2 : ℕ) : ℤ) ^ (p2_of P - 1) ≤ (3 : ℤ) ^ P := by
    exact_mod_cast hP
  have hcz : ((2 : ℕ) : ℤ) ^ (p2_of c - 1) ≤ (3 : ℤ) ^ c := by
    exact_mod_cast hc
  push_cast at hPz hcz
  unfold LowerDeficitLt
  rw [eP, ec]
  set x := (2 : ℤ) ^ (p2_of P - 1)
  set y := (3 : ℤ) ^ P
  set u := (2 : ℤ) ^ (p2_of c - 1)
  set v := (3 : ℤ) ^ c
  have key : (2 * v - 2 * u) * (4 * y - 2 * x) * (2 * x) - (2 * y - 2 * x) ^ 2 * (2 * u) =
      8 * ((v - u) * y ^ 2 - (y - x) ^ 2 * v) := by
    ring
  have h0 : 0 ≤ (v - u) * y ^ 2 - (y - x) ^ 2 * v := by
    linarith
  intro hlt
  linarith

/-! ### Monotone denominators along the walk -/

/-- One step keeps or raises both denominators. -/
theorem sbWalk_den_succ (i : ℕ) :
    (sbWalk i).hiDen ≤ (sbWalk (i + 1)).hiDen ∧ (sbWalk i).loDen ≤ (sbWalk (i + 1)).loDen ∧
      (sbWalk i).loDen + (sbWalk i).hiDen ≤ (sbWalk (i + 1)).loDen + (sbWalk (i + 1)).hiDen := by
  change (sbWalkQ 3 i).hiDen ≤ (sbWalkQ 3 (i + 1)).hiDen ∧
    (sbWalkQ 3 i).loDen ≤ (sbWalkQ 3 (i + 1)).loDen ∧
    (sbWalkQ 3 i).loDen + (sbWalkQ 3 i).hiDen ≤
      (sbWalkQ 3 (i + 1)).loDen + (sbWalkQ 3 (i + 1)).hiDen
  rw [sbWalkQ_succ]
  rcases sbStepQ_den 3 (sbWalkQ 3 i) with h | h
  · rw [h.1, h.2]
    omega
  · rw [h.1, h.2]
    omega

/-- A denominator that changes in a step becomes the sum of the two. -/
theorem sbWalk_den_change (i : ℕ) :
    ((sbWalk (i + 1)).hiDen ≠ (sbWalk i).hiDen →
        (sbWalk (i + 1)).hiDen = (sbWalk i).loDen + (sbWalk i).hiDen) ∧
      ((sbWalk (i + 1)).loDen ≠ (sbWalk i).loDen →
        (sbWalk (i + 1)).loDen = (sbWalk i).loDen + (sbWalk i).hiDen) := by
  change ((sbWalkQ 3 (i + 1)).hiDen ≠ (sbWalkQ 3 i).hiDen →
        (sbWalkQ 3 (i + 1)).hiDen = (sbWalkQ 3 i).loDen + (sbWalkQ 3 i).hiDen) ∧
      ((sbWalkQ 3 (i + 1)).loDen ≠ (sbWalkQ 3 i).loDen →
        (sbWalkQ 3 (i + 1)).loDen = (sbWalkQ 3 i).loDen + (sbWalkQ 3 i).hiDen)
  rw [sbWalkQ_succ]
  rcases sbStepQ_den 3 (sbWalkQ 3 i) with h | h
  · rw [h.1, h.2]
    exact ⟨fun _ => rfl, fun hne => absurd rfl hne⟩
  · rw [h.1, h.2]
    exact ⟨fun hne => absurd rfl hne, fun _ => rfl⟩

/-- The denominators and their sum do not fall along the walk. -/
theorem sbWalk_den_mono {i j : ℕ} (h : i ≤ j) :
    (sbWalk i).hiDen ≤ (sbWalk j).hiDen ∧ (sbWalk i).loDen ≤ (sbWalk j).loDen ∧
      (sbWalk i).loDen + (sbWalk i).hiDen ≤ (sbWalk j).loDen + (sbWalk j).hiDen := by
  induction j, h using Nat.le_induction with
  | base => exact ⟨le_rfl, le_rfl, le_rfl⟩
  | succ j _ ih =>
    have hs := sbWalk_den_succ j
    exact ⟨ih.1.trans hs.1, ih.2.1.trans hs.2.1, ih.2.2.trans hs.2.2⟩

/-! ### The certified walks -/

/-- The window scan from node s: every node whose denominator `d` is at most w passes `ok`
    (numerator, denominator); the scan ends at the first node past w. -/
def rulerWin (K lo hi : ℕ) (d nm : SBNode → ℕ) (ok : ℕ → ℕ → Bool) (w : ℕ) :
    ℕ → SBNode → Bool
  | 0, _ => false
  | f + 1, s =>
    if d s ≤ w then
      ok (nm s) (d s) &&
        match sbCertStep K lo hi s with
        | some t => rulerWin K lo hi d nm ok w f t
        | none => false
    else true

/-- A successful scan from node j passes every node k ≥ j up to which `d` stays at most w. -/
theorem rulerWin_spec {K lo hi : ℕ} (h : Log2Bracket K lo hi) (hK : 1 ≤ K)
    {d nm : SBNode → ℕ} {ok : ℕ → ℕ → Bool} {w : ℕ} :
    ∀ f j, rulerWin K lo hi d nm ok w f (sbWalk j) = true →
      ∀ k, j ≤ k → (∀ i, j ≤ i → i ≤ k → d (sbWalk i) ≤ w) →
        ok (nm (sbWalk k)) (d (sbWalk k)) = true := by
  intro f
  induction f with
  | zero =>
    intro j hw
    exact absurd hw (by simp [rulerWin])
  | succ f ih =>
    intro j hw k hjk hall
    have hdj := hall j le_rfl hjk
    rw [rulerWin, ite_eq_left hdj, Bool.and_eq_true] at hw
    obtain ⟨hok, hrest⟩ := hw
    rcases Nat.eq_or_lt_of_le hjk with heq | hlt
    · rw [← heq]
      exact hok
    · cases ht : sbCertStep K lo hi (sbWalk j) with
      | none =>
        rw [ht] at hrest
        exact absurd hrest (by simp)
      | some t =>
        rw [ht] at hrest
        have hs : 1 ≤ (sbWalk j).loDen := one_le_sbWalkQ_loDen 3 j
        have htw : t = sbWalk (j + 1) := by
          rw [sbCertStep_eq h hK hs ht]
          exact (sbWalkQ_succ 3 j).symm
        rw [htw] at hrest
        exact ih (j + 1) hrest k (by omega) fun i hi1 hi2 => hall i (by omega) hi2

/-- The certified walk over the pairs: at a step that changes `d` from b ≥ 1 to b' ≤ N it
    scans the window `wf b b'` from the new node with `okp` (numerator and denominator of
    b, then of c); it stops once the sum of the denominators passes N. -/
def rulerPairWalk (K lo hi : ℕ) (d nm : SBNode → ℕ) (okp : ℕ → ℕ → ℕ → ℕ → Bool)
    (wf : ℕ → ℕ → ℕ) (N : ℕ) : ℕ → SBNode → Bool
  | 0, _ => false
  | f + 1, s =>
    match sbCertStep K lo hi s with
    | none => false
    | some t =>
      (if d t ≠ d s ∧ 1 ≤ d s ∧ d t ≤ N then
          rulerWin K lo hi d nm (okp (nm s) (d s)) (wf (d s) (d t)) 1000 t
        else true) &&
        (decide (N < s.loDen + s.hiDen) || rulerPairWalk K lo hi d nm okp wf N f t)

/-- A successful pair walk from node j has scanned the window of every step i ≥ j that
    changes `d` from b ≥ 1 to b' ≤ N. -/
theorem rulerPairWalk_spec {K lo hi : ℕ} (h : Log2Bracket K lo hi) (hK : 1 ≤ K)
    {d nm : SBNode → ℕ} {okp : ℕ → ℕ → ℕ → ℕ → Bool} {wf : ℕ → ℕ → ℕ} {N : ℕ}
    (hchg : ∀ i, d (sbWalk (i + 1)) ≠ d (sbWalk i) →
      d (sbWalk (i + 1)) = (sbWalk i).loDen + (sbWalk i).hiDen) :
    ∀ f j, rulerPairWalk K lo hi d nm okp wf N f (sbWalk j) = true →
      ∀ i, j ≤ i → d (sbWalk (i + 1)) ≠ d (sbWalk i) → 1 ≤ d (sbWalk i) →
        d (sbWalk (i + 1)) ≤ N →
        rulerWin K lo hi d nm (okp (nm (sbWalk i)) (d (sbWalk i)))
          (wf (d (sbWalk i)) (d (sbWalk (i + 1)))) 1000 (sbWalk (i + 1)) = true := by
  intro f
  induction f with
  | zero =>
    intro j hw
    exact absurd hw (by simp [rulerPairWalk])
  | succ f ih =>
    intro j hw i hji hne h1 hN
    rw [rulerPairWalk] at hw
    cases ht : sbCertStep K lo hi (sbWalk j) with
    | none =>
      rw [ht] at hw
      exact absurd hw (by simp)
    | some t =>
      rw [ht] at hw
      have hs : 1 ≤ (sbWalk j).loDen := one_le_sbWalkQ_loDen 3 j
      have htw : t = sbWalk (j + 1) := by
        rw [sbCertStep_eq h hK hs ht]
        exact (sbWalkQ_succ 3 j).symm
      rw [htw, Bool.and_eq_true, Bool.or_eq_true] at hw
      obtain ⟨hA, hB⟩ := hw
      rcases Nat.eq_or_lt_of_le hji with heq | hlt
      · subst heq
        rw [ite_eq_left (show d (sbWalk (j + 1)) ≠ d (sbWalk j) ∧ 1 ≤ d (sbWalk j) ∧
            d (sbWalk (j + 1)) ≤ N from ⟨hne, h1, hN⟩)] at hA
        exact hA
      · rcases hB with hstop | hrec
        · exfalso
          have hst := of_decide_eq_true hstop
          have hm := (sbWalk_den_mono (show j ≤ i by omega)).2.2
          have hc := hchg i hne
          omega
        · exact ih (j + 1) hrec i (by omega) hne h1 hN

/-! ### Small steps of the walk -/

theorem sbWalk_zero : sbWalk 0 = ⟨0, 1, 1, 0⟩ := rfl

theorem sbWalk_one : sbWalk 1 = ⟨1, 1, 1, 0⟩ := by
  decide

theorem sbWalk_two : sbWalk 2 = ⟨1, 1, 2, 1⟩ := by
  decide

/-- A step i with an upper denominator at least 1 has i ≥ 2. -/
theorem two_le_of_hiDen {i : ℕ} (h : 1 ≤ (sbWalk i).hiDen) : 2 ≤ i := by
  rcases Nat.lt_or_ge i 2 with hlt | hge
  · exfalso
    interval_cases i
    · rw [sbWalk_zero] at h
      exact absurd h (by decide)
    · rw [sbWalk_one] at h
      exact absurd h (by decide)
  · exact hge

/-- A step i after which the lower denominator changes has i ≥ 2. -/
theorem two_le_of_loDen_change {i : ℕ} (h : (sbWalk (i + 1)).loDen ≠ (sbWalk i).loDen) :
    2 ≤ i := by
  rcases Nat.lt_or_ge i 2 with hlt | hge
  · exfalso
    interval_cases i
    · rw [sbWalk_one, sbWalk_zero] at h
      exact h rfl
    · rw [sbWalk_two, sbWalk_one] at h
      exact h rfl
  · exact hge

/-! ### From the records to the walk -/

/-- For neighbouring records b < b' of a kind whose Orders n ≥ 1 are exactly the values of a
    denominator `d` that does not fall along the walk, some step changes `d` from b to b'. -/
theorem exists_den_change {d : SBNode → ℕ} {R : ℕ → Prop}
    (hmono : ∀ i j, i ≤ j → d (sbWalk i) ≤ d (sbWalk j))
    (hR : ∀ n, 1 ≤ n → (R n ↔ ∃ k, d (sbWalk k) = n)) {b b' : ℕ} (h0 : d (sbWalk 0) < b')
    (hb : 1 ≤ b) (hbb : b < b') (hRb : R b) (hRb' : R b')
    (hn : ∀ x, b < x → x < b' → ¬R x) :
    ∃ i, d (sbWalk i) = b ∧ d (sbWalk (i + 1)) = b' := by
  classical
  have hex : ∃ k, d (sbWalk k) = b' := (hR b' (by omega)).mp hRb'
  obtain ⟨i', hi', hmin⟩ : ∃ i', d (sbWalk i') = b' ∧ ∀ k, k < i' → d (sbWalk k) ≠ b' :=
    ⟨Nat.find hex, Nat.find_spec hex, fun k hk => Nat.find_min hex hk⟩
  obtain ⟨kb, hkb⟩ := (hR b hb).mp hRb
  have hpos : i' ≠ 0 := by
    intro h
    rw [h] at hi'
    omega
  obtain ⟨i, rfl⟩ : ∃ i, i' = i + 1 := ⟨i' - 1, by omega⟩
  have hne := hmin i (by omega)
  have hle : d (sbWalk i) ≤ b' := by
    rw [← hi']
    exact hmono i (i + 1) (by omega)
  have hkbi : kb ≤ i := by
    by_contra hlt
    have := hmono (i + 1) kb (by omega)
    omega
  have hge : b ≤ d (sbWalk i) := by
    rw [← hkb]
    exact hmono kb i hkbi
  refine ⟨i, ?_, hi'⟩
  by_contra hneb
  exact hn _ (by omega) (by omega) ((hR _ (by omega)).mpr ⟨i, rfl⟩)

/-- A record c ≥ b' after the step i that changes `d` to b' is the value of `d` at a step
    k ≥ i + 1, and `d` stays at most c from i + 1 to k. -/
theorem exists_den_after {d : SBNode → ℕ} {R : ℕ → Prop}
    (hmono : ∀ i j, i ≤ j → d (sbWalk i) ≤ d (sbWalk j))
    (hR : ∀ n, 1 ≤ n → (R n ↔ ∃ k, d (sbWalk k) = n)) {i c : ℕ}
    (hic : d (sbWalk i) < c) (hRc : R c) :
    ∃ k, i + 1 ≤ k ∧ d (sbWalk k) = c ∧ ∀ j, i + 1 ≤ j → j ≤ k → d (sbWalk j) ≤ c := by
  obtain ⟨k, hk⟩ := (hR c (by omega)).mp hRc
  have hik : i + 1 ≤ k := by
    by_contra hlt
    have := hmono k i (by omega)
    omega
  exact ⟨k, hik, hk, fun j _ hj => hk ▸ hmono j k hj⟩

/-- The bracket of log2 3 at K = 2^500, from 1003 bits. -/
theorem rulerBracket : Log2Bracket (2 ^ 500) (log2Lo 3 1003 500) (log2Hi 3 1003 500) :=
  log2Bracket_pow3 1003 500

set_option exponentiation.threshold 600 in
/-- The upper pair walk at K = 2^500 up to 10^60, fuel 2000, computed by the kernel. -/
theorem rulerUpWalk_ok :
    rulerPairWalk (2 ^ 500) (log2Lo 3 1003 500) (log2Hi 3 1003 500) SBNode.hiDen SBNode.hiNum
      (rulerUpOK (2 ^ 500) (log2Lo 3 1003 500) (log2Hi 3 1003 500)) (fun b b' => b + b')
      (10 ^ 60) 2000 (sbWalk 0) = true := by
  decide +kernel

set_option exponentiation.threshold 600 in
/-- The lower pair walk at K = 2^500 up to 10^60, fuel 2000, computed by the kernel. -/
theorem rulerLowWalk_ok :
    rulerPairWalk (2 ^ 500) (log2Lo 3 1003 500) (log2Hi 3 1003 500) SBNode.loDen SBNode.loNum
      (rulerLowOK (2 ^ 500) (log2Lo 3 1003 500) (log2Hi 3 1003 500)) (fun P P' => P + P' - 1)
      (10 ^ 60) 2000 (sbWalk 0) = true := by
  decide +kernel

/-! ### The pairs up to 10^60 -/

set_option exponentiation.threshold 600 in
/-- For neighbouring upper record Orders 1 ≤ b < b' ≤ 10^60, no upper record Order c with
    b' ≤ c ≤ b + b' has `UpperDeficitLt b c`. -/
theorem upperPairs_upTo {b b' c : ℕ} (hb : 1 ≤ b) (hbb : b < b') (hR : UpperRecord b)
    (hR' : UpperRecord b') (hn : ∀ x, b < x → x < b' → ¬UpperRecord x) (hbc : b' ≤ c)
    (hcb : c ≤ b + b') (hRc : UpperRecord c) (hN : b' ≤ 10 ^ 60) : ¬UpperDeficitLt b c := by
  have hK : 1 ≤ 2 ^ 500 := Nat.one_le_two_pow
  have hmono : ∀ i j, i ≤ j → (sbWalk i).hiDen ≤ (sbWalk j).hiDen :=
    fun i j h => (sbWalk_den_mono h).1
  have hRs : ∀ n, 1 ≤ n → (UpperRecord n ↔ ∃ k, (sbWalk k).hiDen = n) :=
    fun n hn1 => upperRecord_iff_sbWalk hn1
  have h0 : (sbWalk 0).hiDen < b' := by
    rw [sbWalk_zero]
    change 0 < b'
    omega
  obtain ⟨i, hib, hib'⟩ := exists_den_change hmono hRs h0 hb hbb hR hR' hn
  have hw := rulerPairWalk_spec rulerBracket hK (fun i => (sbWalk_den_change i).1) 2000 0
    rulerUpWalk_ok i (Nat.zero_le i) (by omega) (by omega) (by omega)
  rw [hib, hib'] at hw
  obtain ⟨k, hik, hk, hall⟩ := exists_den_after hmono hRs (show (sbWalk i).hiDen < c by omega) hRc
  have hok := rulerWin_spec rulerBracket hK 1000 (i + 1) hw k hik
    fun j h1 h2 => (hall j h1 h2).trans hcb
  rw [hk, sbWalk_hiNum (two_le_of_hiDen (show 1 ≤ (sbWalk i).hiDen by omega)), hib,
    sbWalk_hiNum (two_le_of_hiDen (show 1 ≤ (sbWalk k).hiDen by omega)), hk] at hok
  exact not_upperDeficitLt_of (rulerUpOK_spec rulerBracket hok)

set_option exponentiation.threshold 600 in
/-- For neighbouring lower record Orders 1 ≤ P < P' ≤ 10^60, no lower record Order c with
    P' ≤ c < P + P' has `LowerDeficitLt P c`. -/
theorem lowerPairs_upTo {P P' c : ℕ} (hP : 1 ≤ P) (hPP : P < P') (hR : LowerRecord P)
    (hR' : LowerRecord P') (hn : ∀ x, P < x → x < P' → ¬LowerRecord x) (hPc : P' ≤ c)
    (hcP : c < P + P') (hRc : LowerRecord c) (hN : P' ≤ 10 ^ 60) : ¬LowerDeficitLt P c := by
  have hK : 1 ≤ 2 ^ 500 := Nat.one_le_two_pow
  have hmono : ∀ i j, i ≤ j → (sbWalk i).loDen ≤ (sbWalk j).loDen :=
    fun i j h => (sbWalk_den_mono h).2.1
  have hRs : ∀ n, 1 ≤ n → (LowerRecord n ↔ ∃ k, (sbWalk k).loDen = n) :=
    fun n hn1 => lowerRecord_iff_sbWalk hn1
  have h0 : (sbWalk 0).loDen < P' := by
    rw [sbWalk_zero]
    change 1 < P'
    omega
  obtain ⟨i, hiP, hiP'⟩ := exists_den_change hmono hRs h0 hP hPP hR hR' hn
  have hchg : (sbWalk (i + 1)).loDen ≠ (sbWalk i).loDen := by
    omega
  have hw := rulerPairWalk_spec rulerBracket hK (fun i => (sbWalk_den_change i).2) 2000 0
    rulerLowWalk_ok i (Nat.zero_le i) hchg (by omega) (by omega)
  rw [hiP, hiP'] at hw
  obtain ⟨k, hik, hk, hall⟩ := exists_den_after hmono hRs (show (sbWalk i).loDen < c by omega) hRc
  have hok := rulerWin_spec rulerBracket hK 1000 (i + 1) hw k hik
    fun j h1 h2 => (hall j h1 h2).trans (by omega)
  have hi2 := two_le_of_loDen_change hchg
  have hk2 : 2 ≤ k := by
    omega
  have hloi := sbWalk_loNum hi2
  have hlok := sbWalk_loNum hk2
  rw [hiP] at hloi
  rw [hk] at hlok
  rw [hk, show (sbWalk i).loNum = p2_of P - 1 by omega,
    show (sbWalk k).loNum = p2_of c - 1 by omega] at hok
  exact not_lowerDeficitLt_of (rulerLowOK_spec rulerBracket hok)

/-- The two pair conditions of `rulerGap_iff_pairs` for the pairs up to 10^60. -/
theorem rulerPairs_upTo :
    (∀ b b' c : ℕ, 1 ≤ b → b < b' → UpperRecord b → UpperRecord b' →
        (∀ x, b < x → x < b' → ¬UpperRecord x) → b' ≤ c → c ≤ b + b' → UpperRecord c →
        b' ≤ 10 ^ 60 → ¬UpperDeficitLt b c) ∧
      (∀ P P' c : ℕ, 1 ≤ P → P < P' → LowerRecord P → LowerRecord P' →
        (∀ x, P < x → x < P' → ¬LowerRecord x) → P' ≤ c → c < P + P' → LowerRecord c →
        P' ≤ 10 ^ 60 → ¬LowerDeficitLt P c) :=
  ⟨fun _ _ _ hb hbb hR hR' hn hbc hcb hRc hN => upperPairs_upTo hb hbb hR hR' hn hbc hcb hRc hN,
    fun _ _ _ hP hPP hR hR' hn hPc hcP hRc hN =>
      lowerPairs_upTo hP hPP hR hR' hn hPc hcP hRc hN⟩

/-! ### The ruler gap for exponents of 3 up to 10^59 -/

/-- The denominators of a node of the certified walk are record Orders. -/
theorem records_of_sbCert {K lo hi : ℕ} (hbr : Log2Bracket K lo hi) (hK : 1 ≤ K) (f : ℕ) :
    (1 ≤ (sbCert K lo hi f sbRoot).hiDen → UpperRecord (sbCert K lo hi f sbRoot).hiDen) ∧
      (1 ≤ (sbCert K lo hi f sbRoot).loDen → LowerRecord (sbCert K lo hi f sbRoot).loDen) := by
  obtain ⟨k, hk⟩ := exists_sbCert hbr hK f
  rw [hk]
  exact ⟨fun h => (upperRecord_iff_sbWalk h).mpr ⟨k, rfl⟩,
    fun h => (lowerRecord_iff_sbWalk h).mpr ⟨k, rfl⟩⟩

set_option exponentiation.threshold 600 in
/-- After 638 steps of the certified walk at K = 2^500 the denominator above lies between
    10^59 and 10^60, computed by the kernel. -/
theorem sbCert_hiDen_638 :
    10 ^ 59 < (sbCert (2 ^ 500) (log2Lo 3 1003 500) (log2Hi 3 1003 500) 638 sbRoot).hiDen ∧
      (sbCert (2 ^ 500) (log2Lo 3 1003 500) (log2Hi 3 1003 500) 638 sbRoot).hiDen ≤
        10 ^ 60 := by
  decide +kernel

set_option exponentiation.threshold 600 in
/-- After 649 steps of the certified walk at K = 2^500 the denominator below lies between
    10^59 and 10^60, computed by the kernel. -/
theorem sbCert_loDen_649 :
    10 ^ 59 < (sbCert (2 ^ 500) (log2Lo 3 1003 500) (log2Hi 3 1003 500) 649 sbRoot).loDen ∧
      (sbCert (2 ^ 500) (log2Lo 3 1003 500) (log2Hi 3 1003 500) 649 sbRoot).loDen ≤
        10 ^ 60 := by
  decide +kernel

set_option exponentiation.threshold 600 in
/-- An upper and a lower record Order between 10^59 and 10^60. -/
theorem exists_records_between :
    (∃ R, 10 ^ 59 < R ∧ R ≤ 10 ^ 60 ∧ UpperRecord R) ∧
      ∃ R, 10 ^ 59 < R ∧ R ≤ 10 ^ 60 ∧ LowerRecord R :=
  ⟨⟨_, sbCert_hiDen_638.1, sbCert_hiDen_638.2,
      (records_of_sbCert rulerBracket Nat.one_le_two_pow 638).1
        (Nat.lt_of_le_of_lt (Nat.zero_le _) sbCert_hiDen_638.1)⟩,
    ⟨_, sbCert_loDen_649.1, sbCert_loDen_649.2,
      (records_of_sbCert rulerBracket Nat.one_le_two_pow 649).2
        (Nat.lt_of_le_of_lt (Nat.zero_le _) sbCert_loDen_649.1)⟩⟩

/-- The ruler gap for every exponent of 2 and every exponent of 3 up to 10^59. -/
theorem rulerGapUpTo_ten_pow (J : ℕ) : SmoothRuler.RulerGapUpTo J (10 ^ 59) := by
  obtain ⟨⟨Ru, hu1, hu2, hRu⟩, ⟨Rl, hl1, hl2, hRl⟩⟩ := exists_records_between
  apply rulerGapUpTo_of_records
  · apply upperGapRecords_iff_deficit.mpr
    intro b v _ _ hbN _ hR hv ht
    apply upper_deficit_of_pairs _ hR hv ht
    intro b' c hb hbb hR' hn hbc hcb hRc _
    have hb' : b' ≤ Ru := by
      by_contra h
      exact hn Ru (by omega) (by omega) hRu
    exact upperPairs_upTo hb hbb hR hR' hn hbc hcb hRc (by omega)
  · apply lowerGapRecords_iff_deficit.mpr
    intro P u hPM _ _ _ hP hR hu ht
    apply lower_deficit_of_pairs _ hP hR hu ht
    intro P' c hPP hR' hn hPc hcP hRc _
    have hP' : P' ≤ Rl := by
      by_contra h
      exact hn Rl (by omega) (by omega) hRl
    exact lowerPairs_upTo hP hPP hR hR' hn hPc hcP hRc (by omega)

end AcceleratedCollatz
