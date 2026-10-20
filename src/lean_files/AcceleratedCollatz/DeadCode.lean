-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.MarkedVectorShift
import AcceleratedCollatz.TChain
import AcceleratedCollatz.Tree

/-!
  Unused declarations, moved out of the main tree (not imported by
  `AcceleratedCollatz.lean`); `lake build` builds it with the rest (the `globs` of
  `lakefile.lean`).
-/

namespace AcceleratedCollatz

-- from RMap

@[simp] theorem R_one : R 1 = 1 := by
  unfold R
  simp

theorem R_iterate_ge_one (k : ℕ) (hk : k ≥ 1) (x : ℕ) : R^[k] x ≥ 1 := by
  match k, hk with
  | (k' + 1), _ =>
    rw [Function.iterate_succ', Function.comp_apply]
    exact R_ge_one _

-- from Core

theorem stepOrder_pos_iff (x : ℕ) : stepOrder x > 0 ↔ Odd x := by
  unfold stepOrder
  split_ifs with hx
  · simp only [hx, iff_true]
    obtain ⟨j, hj⟩ := hx
    exact one_le_padicValNat_of_dvd (by omega) ⟨j + 1, by omega⟩
  · simp [hx]

-- from RShift

/-- If the odd step of x_init drops below x_init, the odd step of x_init + i*2^Q
    drops below x_init + i*2^Q. -/
theorem R_shift_odd_terminates (x_init i Q : ℕ) (hx1 : x_init > 1) (hxodd : Odd x_init)
    (hQ : Q ≥ trailingOnes x_init + 1) (hterm : R x_init < x_init) :
    R (x_init + i * 2 ^ Q) < x_init + i * 2 ^ Q := by
  set v := trailingOnes x_init with hv_def
  have hdvd : 2 ^ v ∣ (x_init + 1) := pow_trailingOnes_dvd x_init
  set s := (x_init + 1) / 2 ^ v with hs_def
  have heq : s * 2 ^ v = x_init + 1 := Nat.div_mul_cancel hdvd
  have hsOdd : Odd s := odd_div_pow_trailingOnes x_init hxodd
  have h3Odd : Odd (3 ^ v) := (by decide : Odd 3).pow
  have h3vsOdd : Odd (3 ^ v * s) := h3Odd.mul hsOdd
  obtain ⟨k, hk⟩ := h3vsOdd
  have hkx : k < x_init := by
    have hRcalc : (3 ^ v * s - 1) / 2 = R x_init := by
      rw [R_odd_closed_form x_init hx1 hxodd, ← hv_def, ← hs_def]
    omega
  have hderive : s * 2 ^ (v + 1) = 2 * x_init + 2 := by
    calc s * 2 ^ (v + 1) = s * 2 ^ v * 2 := by ring
      _ = (x_init + 1) * 2 := by rw [heq]
      _ = 2 * x_init + 2 := by ring
  have hspos : s > 0 := hsOdd.pos
  have hlt : 3 ^ v < 2 ^ (v + 1) := by
    nlinarith [hderive, hk, hkx, hspos]
  rw [R_shift_odd x_init i Q hx1 hxodd hQ, ← hv_def]
  have hpow : (2:ℕ) ^ Q = 2 ^ (v + 1) * 2 ^ (Q - v - 1) := by
    rw [← pow_add]
    congr 1
    omega
  have hcoef : 3 ^ v * 2 ^ (Q - v - 1) < 2 ^ Q := by
    rw [hpow]
    have h2pos : (0:ℕ) < 2 ^ (Q - v - 1) := by positivity
    nlinarith [hlt, h2pos]
  have hile : 3 ^ v * i * 2 ^ (Q - v - 1) ≤ i * 2 ^ Q := by
    rcases Nat.eq_zero_or_pos i with hi0 | hipos
    · simp [hi0]
    · have heq2 : 3 ^ v * i * 2 ^ (Q - v - 1) = i * (3 ^ v * 2 ^ (Q - v - 1)) := by ring
      rw [heq2]
      exact Nat.mul_le_mul_left i (le_of_lt hcoef)
  omega

/-- Sufficiency under the shift, for any Q with 3^v < 2^Q (v = trailingOnes x_init):
    R x_init < x_init * 2^(Q - v - 1) gives the same for x_init + i*2^Q. -/
theorem minCorrection_suff_shift_gen (x_init i Q : ℕ) (hx1 : x_init > 1) (hxodd : Odd x_init)
    (hQspec : (3 : ℕ) ^ (trailingOnes x_init) < 2 ^ Q)
    (hsuff : R x_init < x_init * 2 ^ (Q - trailingOnes x_init - 1)) :
    R (x_init + i * 2 ^ Q) < (x_init + i * 2 ^ Q) * 2 ^ (Q - trailingOnes x_init - 1) := by
  set v := trailingOnes x_init with hv_def
  have hQge : Q ≥ v + 1 := by
    have h2 : (3:ℕ) ^ v ≥ 2 ^ v := Nat.pow_le_pow_left (by norm_num) v
    have h4 : v < Q := by
      by_contra hcon
      push Not at hcon
      have hcontra : (2:ℕ) ^ Q ≤ 2 ^ v := Nat.pow_le_pow_right (by norm_num) hcon
      omega
    omega
  rw [R_shift_odd x_init i Q hx1 hxodd hQge, ← hv_def]
  have hexpand : (x_init + i * 2 ^ Q) * 2 ^ (Q - v - 1) =
      x_init * 2 ^ (Q - v - 1) + i * 2 ^ Q * 2 ^ (Q - v - 1) := by ring
  rw [hexpand]
  have hile : 3 ^ v * i * 2 ^ (Q - v - 1) ≤ i * 2 ^ Q * 2 ^ (Q - v - 1) := by
    have h1 : (3:ℕ) ^ v ≤ 2 ^ Q := le_of_lt hQspec
    have h2 : 3 ^ v * (i * 2 ^ (Q - v - 1)) ≤ 2 ^ Q * (i * 2 ^ (Q - v - 1)) :=
      Nat.mul_le_mul_right _ h1
    nlinarith [h2]
  omega

theorem minCorrection_suff_shift (x_init i : ℕ) (hx1 : x_init > 1) (hxodd : Odd x_init)
    (hsuff : R x_init < x_init * 2 ^ (p2_of (trailingOnes x_init) - trailingOnes x_init - 1)) :
    R (x_init + i * 2 ^ (p2_of (trailingOnes x_init))) <
      (x_init + i * 2 ^ (p2_of (trailingOnes x_init))) *
        2 ^ (p2_of (trailingOnes x_init) - trailingOnes x_init - 1) :=
  minCorrection_suff_shift_gen x_init i (p2_of (trailingOnes x_init)) hx1 hxodd
    (p2_of_spec (trailingOnes x_init)) hsuff

/-- R of the start shifted by i*2^(p2_of v), halved p2_of v - v - 1 times, is
    that of x_init plus i*3^v (v = trailingOnes x_init). -/
theorem xdrop_affine_shift (x_init i : ℕ) (hx1 : x_init > 1) (hxodd : Odd x_init) :
    R (x_init + i * 2 ^ (p2_of (trailingOnes x_init))) /
        2 ^ (p2_of (trailingOnes x_init) - trailingOnes x_init - 1) =
      R x_init / 2 ^ (p2_of (trailingOnes x_init) - trailingOnes x_init - 1) +
        i * 3 ^ (trailingOnes x_init) := by
  set v := trailingOnes x_init with hv_def
  set Q := p2_of v with hQ_def
  have hQspec : (3:ℕ) ^ v < 2 ^ Q := p2_of_spec v
  have hQge : Q ≥ v + 1 := by
    have h2 : (3:ℕ) ^ v ≥ 2 ^ v := Nat.pow_le_pow_left (by norm_num) v
    have h4 : v < Q := by
      by_contra hcon
      push Not at hcon
      have hcontra : (2:ℕ) ^ Q ≤ 2 ^ v := Nat.pow_le_pow_right (by norm_num) hcon
      omega
    omega
  rw [R_shift_odd x_init i Q hx1 hxodd hQge, ← hv_def]
  have hswap : 3 ^ v * i * 2 ^ (Q - v - 1) = (3 ^ v * i) * 2 ^ (Q - v - 1) := by ring
  rw [hswap]
  have h2wpos : (0:ℕ) < 2 ^ (Q - v - 1) := by positivity
  rw [Nat.add_mul_div_right (R x_init) (3 ^ v * i) h2wpos]
  ring

/-- Minimality under the shift i*2^(p2_of v): R x_init ≥ x_init * 2^(p2_of v - v - 2)
    gives the same for the shifted start (v = trailingOnes x_init). -/
theorem minCorrection_min_shift (x_init i : ℕ) (hx1 : x_init > 1) (hxodd : Odd x_init)
    (hQge2 : p2_of (trailingOnes x_init) ≥ trailingOnes x_init + 2)
    (hmin : R x_init ≥ x_init * 2 ^ (p2_of (trailingOnes x_init) - trailingOnes x_init - 2)) :
    R (x_init + i * 2 ^ (p2_of (trailingOnes x_init))) ≥
      (x_init + i * 2 ^ (p2_of (trailingOnes x_init))) *
        2 ^ (p2_of (trailingOnes x_init) - trailingOnes x_init - 2) := by
  set v := trailingOnes x_init with hv_def
  set Q := p2_of v with hQ_def
  have hQspec : (2:ℕ) ^ (Q - 1) ≤ 3 ^ v := p2_of_spec_lower v
  have hQge : Q ≥ v + 1 := by omega
  rw [R_shift_odd x_init i Q hx1 hxodd hQge, ← hv_def]
  have hexpand : (x_init + i * 2 ^ Q) * 2 ^ (Q - v - 2) =
      x_init * 2 ^ (Q - v - 2) + i * 2 ^ Q * 2 ^ (Q - v - 2) := by ring
  rw [hexpand]
  have hile : 3 ^ v * i * 2 ^ (Q - v - 1) ≥ i * 2 ^ Q * 2 ^ (Q - v - 2) := by
    have heq1 : i * 2 ^ Q * 2 ^ (Q - v - 2) = i * (2 ^ Q * 2 ^ (Q - v - 2)) := by ring
    rw [heq1]
    have heq1b : (2:ℕ) ^ Q * 2 ^ (Q - v - 2) = 2 ^ (2 * Q - v - 2) := by
      rw [← pow_add]
      congr 1
      omega
    rw [heq1b]
    have heq2 : 3 ^ v * i * 2 ^ (Q - v - 1) = i * (3 ^ v * 2 ^ (Q - v - 1)) := by ring
    rw [heq2]
    have hpoweq : (2:ℕ) ^ (2 * Q - v - 2) = 2 ^ (Q - 1) * 2 ^ (Q - v - 1) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hpoweq]
    have h1 : (2:ℕ) ^ (Q - 1) * 2 ^ (Q - v - 1) ≤ 3 ^ v * 2 ^ (Q - v - 1) :=
      Nat.mul_le_mul_right _ hQspec
    have h2 : i * (2 ^ (Q - 1) * 2 ^ (Q - v - 1)) ≤ i * (3 ^ v * 2 ^ (Q - v - 1)) :=
      Nat.mul_le_mul_left i h1
    exact h2
  omega

/-- If the even step of x drops below x, the even step of x + i*2^Q drops below
    x + i*2^Q. -/
theorem R_shift_even_terminates (x i Q : ℕ) (hxpos : x ≠ 0) (hxEven : Even x)
    (hQ : Q ≥ trailingZeros x + 1) (hterm : R x < x) :
    R (x + i * 2 ^ Q) < x + i * 2 ^ Q := by
  rw [R_shift_even x i Q hxpos hxEven hQ]
  have hle : (2:ℕ) ^ (Q - trailingZeros x) ≤ 2 ^ Q := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hile : i * 2 ^ (Q - trailingZeros x) ≤ i * 2 ^ Q := Nat.mul_le_mul_left i hle
  omega

/-- `R_shift_even_terminates` with value y and threshold x0 apart:
    R y < x0 gives R (y + i*2^Q) < x0 + i*2^Q. -/
theorem R_shift_even_terminates_gen (y x0 i Q : ℕ) (hypos : y ≠ 0) (hyEven : Even y)
    (hQ : Q ≥ trailingZeros y + 1) (hterm : R y < x0) :
    R (y + i * 2 ^ Q) < x0 + i * 2 ^ Q := by
  rw [R_shift_even y i Q hypos hyEven hQ]
  have hle : (2:ℕ) ^ (Q - trailingZeros y) ≤ 2 ^ Q := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hile : i * 2 ^ (Q - trailingZeros y) ≤ i * 2 ^ Q := Nat.mul_le_mul_left i hle
  omega

-- from AdmissibleLength

theorem seqProduct_combine (a b : ℕ) (hab : a ≤ b) :
    (3 / 2 : ℚ) ^ a * (1 / 2 : ℚ) ^ (b - a) = (3 : ℚ) ^ a / (2 : ℚ) ^ b := by
  rw [div_pow, div_pow, one_pow, div_mul_div_comm]
  congr 1
  · ring
  · rw [← pow_add]
    congr 1
    omega

-- from MarkedVector

theorem rFoldFrom_append (r0 : ℚ) (a b : List Bool) :
    rFoldFrom r0 (a ++ b) = rFoldFrom (rFoldFrom r0 a) b := by
  unfold rFoldFrom
  rw [List.foldl_append]

/-- The value reached by the recursion of `markedVectorRaw`: at the drop below x0,
    or when the fuel runs out. -/
def finalX : (fuel : ℕ) → (x0 x : ℕ) → ℕ
  | 0, _, x => x
  | fuel + 1, x0, x =>
    let (_, _, x') := stepInfo x
    if x' < x0 then x' else finalX fuel x0 x'

/-- Folding n trues from r0: (3/2)^n (r0 + 1) - 1. -/
theorem rFoldFrom_replicate_true (n : ℕ) (r0 : ℚ) :
    rFoldFrom r0 (List.replicate n true) = (3 / 2) ^ n * (r0 + 1) - 1 := by
  induction n generalizing r0 with
  | zero => simp [rFoldFrom]
  | succ k ih =>
    rw [List.replicate_succ]
    unfold rFoldFrom at *
    simp only [List.foldl_cons, ite_true]
    rw [ih]
    ring

theorem rFoldFrom_replicate_false (n : ℕ) (r0 : ℚ) :
    rFoldFrom r0 (List.replicate n false) = r0 / 2 ^ n := by
  induction n generalizing r0 with
  | zero => simp [rFoldFrom]
  | succ k ih =>
    rw [List.replicate_succ]
    unfold rFoldFrom at *
    simp only [List.foldl_cons, Bool.false_eq_true, ite_false]
    rw [ih]
    ring

/-- Folding the bits of an odd step's entry from x gives R x. -/
theorem rFoldFrom_expandEntry_odd (x : ℕ) (hx1 : x > 1) (hxOdd : Odd x) :
    rFoldFrom (x : ℚ) (expandEntry (trailingOnes x : ℤ)) = (R x : ℚ) := by
  set v := trailingOnes x with hv_def
  have hvpos : v ≥ 1 := by
    obtain ⟨j, hj⟩ := hxOdd
    exact one_le_padicValNat_of_dvd (by omega) ⟨j + 1, by omega⟩
  have hdvd : 2 ^ v ∣ (x + 1) := pow_trailingOnes_dvd x
  set s := (x + 1) / 2 ^ v with hs_def
  have heq : s * 2 ^ v = x + 1 := Nat.div_mul_cancel hdvd
  have hsOdd : Odd s := odd_div_pow_trailingOnes x hxOdd
  have h3Odd : Odd (3 ^ v) := (by decide : Odd 3).pow
  have h3vsOdd : Odd (3 ^ v * s) := h3Odd.mul hsOdd
  obtain ⟨k, hk⟩ := h3vsOdd
  have hRk : R x = k := by
    rw [R_odd_closed_form x hx1 hxOdd, ← hv_def, ← hs_def]
    omega
  unfold expandEntry
  rw [ite_eq_left (by exact_mod_cast hvpos)]
  rw [rFoldFrom_append, rFoldFrom_replicate_true]
  have htoNat : (trailingOnes x : ℤ).toNat = v := by
    rw [hv_def]
    simp
  rw [htoNat]
  simp only [rFoldFrom, List.foldl_cons, List.foldl_nil, Bool.false_eq_true, ite_false]
  rw [hRk]
  have hqeq : (s : ℚ) * 2 ^ v = (x : ℚ) + 1 := by exact_mod_cast heq
  have hkeq : (3 : ℚ) ^ v * s = 2 * k + 1 := by exact_mod_cast hk
  have hpow : ((3 : ℚ) / 2) ^ v = 3 ^ v / 2 ^ v := by rw [div_pow]
  rw [hpow]
  have hkey : (3 : ℚ) ^ v * ((x : ℚ) + 1) = (2 * k + 1) * 2 ^ v := by
    rw [← hqeq, show (3 : ℚ) ^ v * ((s : ℚ) * 2 ^ v) = (3 ^ v * (s : ℚ)) * 2 ^ v from by ring,
      hkeq]
  have h2pos : (2 : ℚ) ^ v ≠ 0 := by positivity
  field_simp [h2pos]
  linarith [hkey]

/-- Folding the bits of an even step's entry from x gives R x. -/
theorem rFoldFrom_expandEntry_even (x : ℕ) (hxEven : Even x) (hx1 : x > 1) :
    rFoldFrom (x : ℚ) (expandEntry (-trailingZeros x : ℤ)) = (R x : ℚ) := by
  have hwpos : trailingZeros x ≥ 1 :=
    one_le_padicValNat_of_dvd (by omega) (even_iff_two_dvd.mp hxEven)
  unfold expandEntry
  rw [ite_eq_right (by omega)]
  rw [neg_neg]
  simp only [Int.toNat_natCast]
  rw [rFoldFrom_replicate_false]
  unfold R
  rw [ite_eq_left (by omega), ite_eq_left hxEven]
  have hdvd : 2 ^ (trailingZeros x) ∣ x := pow_padicValNat_dvd (p := 2) (n := x)
  have heq2 : (x / 2 ^ (trailingZeros x) : ℕ) * 2 ^ (trailingZeros x) = x := Nat.div_mul_cancel hdvd
  have hcast : ((x / 2 ^ (trailingZeros x) : ℕ) : ℚ) * 2 ^ (trailingZeros x) = (x : ℚ) := by
    exact_mod_cast heq2
  have h2pos : (2 : ℚ) ^ (trailingZeros x) ≠ 0 := by positivity
  field_simp [h2pos]
  linarith [hcast]

/-- Folding the decoded trajectory from x gives its endpoint `finalX`,
    for x ≥ x0 > 1. -/
theorem rFoldFrom_markedVectorRaw (fuel x0 x : ℕ) (hx0 : x0 > 1) (hxge : x ≥ x0) :
    rFoldFrom (x : ℚ) (decodeVector (markedVectorRaw fuel x0 x)) =
      (finalX fuel x0 x : ℚ) := by
  induction fuel generalizing x with
  | zero => simp [markedVectorRaw, finalX, decodeVector, rFoldFrom]
  | succ f ih =>
    have hx1 : x > 1 := by omega
    rcases Nat.even_or_odd x with hxEven | hxOdd
    · have hxne : x % 2 ≠ 1 := by
        rcases hxEven with ⟨r, hr⟩
        omega
      simp only [markedVectorRaw, finalX, stepInfo, hxne, ite_false]
      by_cases hstop : R x < x0
      · simp only [hstop, ite_true, decodeVector, List.flatMap_cons, List.flatMap_nil,
          List.append_nil, markedEntry]
        exact rFoldFrom_expandEntry_even x hxEven hx1
      · simp only [hstop, ite_false, decodeVector, List.flatMap_cons, markedEntry,
          Bool.false_eq_true, ite_false]
        rw [← decodeVector, rFoldFrom_append, rFoldFrom_expandEntry_even x hxEven hx1]
        exact ih (R x) (by omega)
    · have hxeq : x % 2 = 1 := Nat.odd_iff.mp hxOdd
      simp only [markedVectorRaw, finalX, stepInfo, hxeq, ite_true]
      by_cases hstop : R x < x0
      · simp only [hstop, ite_true, decodeVector, List.flatMap_cons, List.flatMap_nil,
          List.append_nil, markedEntry]
        exact rFoldFrom_expandEntry_odd x hx1 hxOdd
      · simp only [hstop, ite_false, decodeVector, List.flatMap_cons, markedEntry, ite_true]
        rw [← decodeVector, rFoldFrom_append, rFoldFrom_expandEntry_odd x hx1 hxOdd]
        exact ih (R x) (by omega)

/-- x0 from the endpoint, the r-fold, the length and the number of ones of its
    decoded trajectory: x0 = (endpoint - r) * 2^length / 3^ones. -/
theorem x0_recovery (fuel x0 : ℕ) (hx0 : x0 > 1) :
    (x0 : ℚ) =
      ((finalX fuel x0 x0 : ℚ) -
          rFold (decodeVector (markedVectorRaw fuel x0 x0))) *
        2 ^ (decodeVector (markedVectorRaw fuel x0 x0)).length /
        3 ^ (decodeVector (markedVectorRaw fuel x0 x0)).count true := by
  set bits := decodeVector (markedVectorRaw fuel x0 x0) with hbits_def
  have hround : rFoldFrom (x0 : ℚ) bits = (finalX fuel x0 x0 : ℚ) :=
    rFoldFrom_markedVectorRaw fuel x0 x0 hx0 (le_refl x0)
  have hlin : rFoldFrom (x0 : ℚ) bits =
      (3 : ℚ) ^ bits.count true / 2 ^ bits.length * x0 + rFold bits :=
    rFoldFrom_linear bits x0
  rw [hround] at hlin
  have h2pos : (2 : ℚ) ^ bits.length ≠ 0 := by positivity
  have h3pos : (3 : ℚ) ^ bits.count true ≠ 0 := by positivity
  field_simp
  field_simp at hlin
  linarith [hlin]

/-- One-step unfolding of `markedVectorRaw`, even branch. -/
theorem markedVectorRaw_succ_even (fuel x0 x : ℕ) (hxEven : x % 2 ≠ 1) :
    markedVectorRaw (fuel + 1) x0 x =
      if R x < x0 then [markedEntry false (trailingZeros x)]
      else markedEntry false (trailingZeros x) :: markedVectorRaw fuel x0 (R x) := by
  simp only [markedVectorRaw, stepInfo, hxEven, ite_false]

/-- One-step unfolding of `markedVectorRaw`, odd branch. -/
theorem markedVectorRaw_succ_odd (fuel x0 x : ℕ) (hxOdd : x % 2 = 1) :
    markedVectorRaw (fuel + 1) x0 x =
      if R x < x0 then [markedEntry true (trailingOnes x)]
      else markedEntry true (trailingOnes x) :: markedVectorRaw fuel x0 (R x) := by
  simp only [markedVectorRaw, stepInfo, hxOdd, ite_true]

theorem finalX_succ_odd (fuel x0 x : ℕ) (hxOdd : x % 2 = 1) :
    finalX (fuel + 1) x0 x = if R x < x0 then R x else finalX fuel x0 (R x) := by
  simp only [finalX, stepInfo, hxOdd, ite_true]

theorem finalX_succ_even (fuel x0 x : ℕ) (hxEven : x % 2 ≠ 1) :
    finalX (fuel + 1) x0 x = if R x < x0 then R x else finalX fuel x0 (R x) := by
  simp only [finalX, stepInfo, hxEven, ite_false]

/-- Shift-invariance of `markedVectorRaw` before the end: if fuel + 1 steps from x
    do not drop below x0 and Q is at least their decoded length, fuel steps from
    x + i*2^Q give the entries of fuel steps from x. -/
theorem markedVectorRaw_shift (fuel x0 x i Q : ℕ) (hx0 : x0 > 1) (hxge : x ≥ x0)
    (hcont : finalX (fuel + 1) x0 x ≥ x0)
    (hQ : Q ≥ (decodeVector (markedVectorRaw (fuel + 1) x0 x)).length) :
    markedVectorRaw fuel x0 (x + i * 2 ^ Q) = markedVectorRaw fuel x0 x := by
  induction fuel generalizing x i Q with
  | zero => simp [markedVectorRaw]
  | succ f ih =>
    have hx1 : x > 1 := by omega
    rcases Nat.even_or_odd x with hxEven | hxOdd
    · have hxne : x % 2 ≠ 1 := by
        rcases hxEven with ⟨r, hr⟩
        omega
      set w := trailingZeros x with hw_def
      have hwpos : w ≥ 1 :=
        one_le_padicValNat_of_dvd (by omega) (even_iff_two_dvd.mp hxEven)
      set x' := R x with hx'_def
      rw [finalX_succ_even (f + 1) x0 x hxne] at hcont
      have hxne0 : ¬ (x' < x0) := by
        intro hlt
        rw [ite_eq_left hlt] at hcont
        omega
      rw [ite_eq_right hxne0] at hcont
      have hcontR : finalX (f + 1) x0 x' ≥ x0 := hcont
      rw [markedVectorRaw_succ_even (f + 1) x0 x hxne, ite_eq_right hxne0] at hQ
      have hLdef : (decodeVector (markedEntry false w :: markedVectorRaw (f + 1) x0 x')).length =
          w + (decodeVector (markedVectorRaw (f + 1) x0 x')).length := by
        unfold decodeVector
        simp only [List.flatMap_cons, List.length_append]
        simp only [markedEntry_false]
        unfold expandEntry
        rw [ite_eq_right (by omega : ¬ (0:ℤ) < -(w:ℤ))]
        rw [neg_neg]
        simp
      rw [hLdef] at hQ
      have hL' : (decodeVector (markedVectorRaw (f + 1) x0 x')).length ≥ 1 := by
        rcases Nat.even_or_odd x' with hx'Even | hx'Odd
        · have hx'ne : x' % 2 ≠ 1 := by
            rcases hx'Even with ⟨r, hr⟩
            omega
          have hw'pos : trailingZeros x' ≥ 1 :=
            one_le_padicValNat_of_dvd (by omega) (even_iff_two_dvd.mp hx'Even)
          rw [markedVectorRaw_succ_even f x0 x' hx'ne]
          have hentrylen : (expandEntry (-(trailingZeros x' : ℤ))).length = trailingZeros x' := by
            unfold expandEntry
            rw [ite_eq_right (by omega : ¬ (0:ℤ) < -(trailingZeros x' : ℤ))]
            rw [neg_neg]
            simp
          split
          · simp [decodeVector, hentrylen]
            omega
          · simp only [decodeVector, List.flatMap_cons, List.length_append, markedEntry_false,
              hentrylen]
            omega
        · have hx'eq : x' % 2 = 1 := Nat.odd_iff.mp hx'Odd
          have hv'pos : trailingOnes x' ≥ 1 := by
            obtain ⟨j, hj⟩ := hx'Odd
            exact one_le_padicValNat_of_dvd (by omega) ⟨j + 1, by omega⟩
          rw [markedVectorRaw_succ_odd f x0 x' hx'eq]
          have hentrylen : (expandEntry (trailingOnes x' : ℤ)).length = trailingOnes x' + 1 := by
            unfold expandEntry
            rw [ite_eq_left (by exact_mod_cast hv'pos : (0:ℤ) < (trailingOnes x' : ℤ))]
            simp
          split
          · simp [decodeVector, hentrylen]
          · simp only [decodeVector, List.flatMap_cons, List.length_append, markedEntry_true,
              hentrylen]
            omega
      have hwQ : Q ≥ w + 1 := by omega
      have hvshift : trailingZeros (x + i * 2 ^ Q) = w := trailingZeros_shift x i Q (by omega) hwQ
      have hxine : (x + i * 2 ^ Q) % 2 ≠ 1 := by
        obtain ⟨r, hr⟩ := hxEven
        have hxi_even : Even (x + i * 2 ^ Q) := by
          have hQ1 : Q ≥ 1 := by omega
          exact ⟨r + i * 2 ^ (Q - 1), by
            have h2 : i * 2 ^ Q = i * 2 ^ (Q - 1) * 2 := by
              rw [mul_assoc, ← pow_succ]
              congr 2
              omega
            omega⟩
        obtain ⟨s, hs⟩ := hxi_even
        omega
      have hRshift : R (x + i * 2 ^ Q) = x' + i * 2 ^ (Q - w) :=
        R_shift_even x i Q (by omega) hxEven hwQ
      rw [markedVectorRaw_succ_even f x0 (x + i * 2 ^ Q) hxine, hvshift, hRshift]
      have hstopf : ¬ (x' + i * 2 ^ (Q - w) < x0) := by omega
      rw [ite_eq_right hstopf]
      rw [markedVectorRaw_succ_even f x0 x hxne, ite_eq_right hxne0]
      have hIH := ih x' i (Q - w) (by omega) hcontR (by omega)
      rw [hIH]
    · have hxeq : x % 2 = 1 := Nat.odd_iff.mp hxOdd
      set v := trailingOnes x with hv_def
      have hvpos : v ≥ 1 := by
        obtain ⟨j, hj⟩ := hxOdd
        exact one_le_padicValNat_of_dvd (by omega) ⟨j + 1, by omega⟩
      set x' := R x with hx'_def
      rw [finalX_succ_odd (f + 1) x0 x hxeq] at hcont
      have hxne0 : ¬ (x' < x0) := by
        intro hlt
        rw [ite_eq_left hlt] at hcont
        omega
      rw [ite_eq_right hxne0] at hcont
      have hcontR : finalX (f + 1) x0 x' ≥ x0 := hcont
      rw [markedVectorRaw_succ_odd (f + 1) x0 x hxeq, ite_eq_right hxne0] at hQ
      have hLdef : (decodeVector (markedEntry true v :: markedVectorRaw (f + 1) x0 x')).length =
          (v + 1) + (decodeVector (markedVectorRaw (f + 1) x0 x')).length := by
        unfold decodeVector
        simp only [List.flatMap_cons, List.length_append]
        simp only [markedEntry_true]
        unfold expandEntry
        rw [ite_eq_left (by exact_mod_cast hvpos : (0:ℤ) < (v:ℤ))]
        simp
      rw [hLdef] at hQ
      have hL' : (decodeVector (markedVectorRaw (f + 1) x0 x')).length ≥ 1 := by
        rcases Nat.even_or_odd x' with hx'Even | hx'Odd
        · have hx'ne : x' % 2 ≠ 1 := by
            rcases hx'Even with ⟨r, hr⟩
            omega
          have hw'pos : trailingZeros x' ≥ 1 :=
            one_le_padicValNat_of_dvd (by omega) (even_iff_two_dvd.mp hx'Even)
          rw [markedVectorRaw_succ_even f x0 x' hx'ne]
          have hentrylen : (expandEntry (-(trailingZeros x' : ℤ))).length = trailingZeros x' := by
            unfold expandEntry
            rw [ite_eq_right (by omega : ¬ (0:ℤ) < -(trailingZeros x' : ℤ))]
            rw [neg_neg]
            simp
          split
          · simp [decodeVector, hentrylen]
            omega
          · simp only [decodeVector, List.flatMap_cons, List.length_append, markedEntry_false,
              hentrylen]
            omega
        · have hx'eq2 : x' % 2 = 1 := Nat.odd_iff.mp hx'Odd
          have hv'pos : trailingOnes x' ≥ 1 := by
            obtain ⟨j, hj⟩ := hx'Odd
            exact one_le_padicValNat_of_dvd (by omega) ⟨j + 1, by omega⟩
          rw [markedVectorRaw_succ_odd f x0 x' hx'eq2]
          have hentrylen : (expandEntry (trailingOnes x' : ℤ)).length = trailingOnes x' + 1 := by
            unfold expandEntry
            rw [ite_eq_left (by exact_mod_cast hv'pos : (0:ℤ) < (trailingOnes x' : ℤ))]
            simp
          split
          · simp [decodeVector, hentrylen]
          · simp only [decodeVector, List.flatMap_cons, List.length_append, markedEntry_true,
              hentrylen]
            omega
      have hvQ : Q ≥ v + 1 := by omega
      have hvshift : trailingOnes (x + i * 2 ^ Q) = v := trailingOnes_shift x i Q hxOdd hvQ
      have hxine : (x + i * 2 ^ Q) % 2 = 1 := by
        have hxi_odd : Odd (x + i * 2 ^ Q) := by
          have hQ1 : Q ≥ 1 := by omega
          obtain ⟨j, hj⟩ := hxOdd
          refine ⟨j + i * 2 ^ (Q - 1), ?_⟩
          have h2 : i * 2 ^ Q = i * 2 ^ (Q - 1) * 2 := by
            rw [mul_assoc, ← pow_succ]
            congr 2
            omega
          omega
        exact Nat.odd_iff.mp hxi_odd
      have hRshift : R (x + i * 2 ^ Q) = x' + 3 ^ v * i * 2 ^ (Q - v - 1) :=
        R_shift_odd x i Q hx1 hxOdd hvQ
      rw [markedVectorRaw_succ_odd f x0 (x + i * 2 ^ Q) hxine, hvshift, hRshift]
      have hstopf : ¬ (x' + 3 ^ v * i * 2 ^ (Q - v - 1) < x0) := by omega
      rw [ite_eq_right hstopf]
      rw [markedVectorRaw_succ_odd f x0 x hxeq, ite_eq_right hxne0]
      have hIH := ih x' (3 ^ v * i) (Q - v - 1) (by omega) hcontR (by omega)
      rw [hIH]

/-- The r-fold of the decoded trajectory is the same for x_init and
    x_init + i*2^Q, under the hypotheses of `markedVectorRaw_shift`. -/
theorem rFold_class_constant (fuel x_init i Q : ℕ) (hx_init : x_init > 1)
    (hcont : finalX (fuel + 1) x_init x_init ≥ x_init)
    (hQ : Q ≥ (decodeVector (markedVectorRaw (fuel + 1) x_init x_init)).length) :
    rFold (decodeVector (markedVectorRaw fuel x_init (x_init + i * 2 ^ Q))) =
      rFold (decodeVector (markedVectorRaw fuel x_init x_init)) := by
  rw [markedVectorRaw_shift fuel x_init x_init i Q hx_init (le_refl x_init) hcont hQ]

/-- The endpoint under the shift: `finalX` of x + i*2^Q is `finalX` of x plus
    i'*2^Q', with Q' + decoded length = Q. -/
theorem markedVectorRaw_endpoint_shift (fuel x0 x i Q : ℕ) (hx0 : x0 > 1) (hxge : x ≥ x0)
    (hcont : finalX (fuel + 1) x0 x ≥ x0)
    (hQ : Q ≥ (decodeVector (markedVectorRaw (fuel + 1) x0 x)).length) :
    ∃ i' Q', finalX fuel x0 (x + i * 2 ^ Q) = finalX fuel x0 x + i' * 2 ^ Q' ∧
      Q' + (decodeVector (markedVectorRaw fuel x0 x)).length = Q := by
  induction fuel generalizing x i Q with
  | zero => exact ⟨i, Q, by simp [finalX], by simp [markedVectorRaw, decodeVector]⟩
  | succ f ih =>
    have hx1 : x > 1 := by omega
    rcases Nat.even_or_odd x with hxEven | hxOdd
    · have hxne : x % 2 ≠ 1 := by
        rcases hxEven with ⟨r, hr⟩
        omega
      set w := trailingZeros x with hw_def
      have hwpos : w ≥ 1 :=
        one_le_padicValNat_of_dvd (by omega) (even_iff_two_dvd.mp hxEven)
      set x' := R x with hx'_def
      rw [finalX_succ_even (f + 1) x0 x hxne] at hcont
      have hxne0 : ¬ (x' < x0) := by
        intro hlt
        rw [ite_eq_left hlt] at hcont
        omega
      rw [ite_eq_right hxne0] at hcont
      have hcontR : finalX (f + 1) x0 x' ≥ x0 := hcont
      rw [markedVectorRaw_succ_even (f + 1) x0 x hxne, ite_eq_right hxne0] at hQ
      have hLdef : (decodeVector (markedEntry false w :: markedVectorRaw (f + 1) x0 x')).length =
          w + (decodeVector (markedVectorRaw (f + 1) x0 x')).length := by
        unfold decodeVector
        simp only [List.flatMap_cons, List.length_append]
        simp only [markedEntry_false]
        unfold expandEntry
        rw [ite_eq_right (by omega : ¬ (0:ℤ) < -(w:ℤ))]
        rw [neg_neg]
        simp
      rw [hLdef] at hQ
      have hL' : (decodeVector (markedVectorRaw (f + 1) x0 x')).length ≥ 1 := by
        rcases Nat.even_or_odd x' with hx'Even | hx'Odd
        · have hx'ne : x' % 2 ≠ 1 := by
            rcases hx'Even with ⟨r, hr⟩
            omega
          have hw'pos : trailingZeros x' ≥ 1 :=
            one_le_padicValNat_of_dvd (by omega) (even_iff_two_dvd.mp hx'Even)
          rw [markedVectorRaw_succ_even f x0 x' hx'ne]
          have hentrylen : (expandEntry (-(trailingZeros x' : ℤ))).length = trailingZeros x' := by
            unfold expandEntry
            rw [ite_eq_right (by omega : ¬ (0:ℤ) < -(trailingZeros x' : ℤ))]
            rw [neg_neg]
            simp
          split
          · simp [decodeVector, hentrylen]
            omega
          · simp only [decodeVector, List.flatMap_cons, List.length_append, markedEntry_false,
              hentrylen]
            omega
        · have hx'eq : x' % 2 = 1 := Nat.odd_iff.mp hx'Odd
          have hv'pos : trailingOnes x' ≥ 1 := by
            obtain ⟨j, hj⟩ := hx'Odd
            exact one_le_padicValNat_of_dvd (by omega) ⟨j + 1, by omega⟩
          rw [markedVectorRaw_succ_odd f x0 x' hx'eq]
          have hentrylen : (expandEntry (trailingOnes x' : ℤ)).length = trailingOnes x' + 1 := by
            unfold expandEntry
            rw [ite_eq_left (by exact_mod_cast hv'pos : (0:ℤ) < (trailingOnes x' : ℤ))]
            simp
          split
          · simp [decodeVector, hentrylen]
          · simp only [decodeVector, List.flatMap_cons, List.length_append, markedEntry_true,
              hentrylen]
            omega
      have hwQ : Q ≥ w + 1 := by omega
      have hvshift : trailingZeros (x + i * 2 ^ Q) = w := trailingZeros_shift x i Q (by omega) hwQ
      have hxine : (x + i * 2 ^ Q) % 2 ≠ 1 := by
        obtain ⟨r, hr⟩ := hxEven
        have hxi_even : Even (x + i * 2 ^ Q) := by
          have hQ1 : Q ≥ 1 := by omega
          exact ⟨r + i * 2 ^ (Q - 1), by
            have h2 : i * 2 ^ Q = i * 2 ^ (Q - 1) * 2 := by
              rw [mul_assoc, ← pow_succ]
              congr 2
              omega
            omega⟩
        obtain ⟨s, hs⟩ := hxi_even
        omega
      have hRshift : R (x + i * 2 ^ Q) = x' + i * 2 ^ (Q - w) :=
        R_shift_even x i Q (by omega) hxEven hwQ
      rw [finalX_succ_even f x0 (x + i * 2 ^ Q) hxine, hRshift]
      have hstopf : ¬ (x' + i * 2 ^ (Q - w) < x0) := by omega
      rw [ite_eq_right hstopf]
      rw [finalX_succ_even f x0 x hxne, ite_eq_right hxne0]
      obtain ⟨i', Q', hIHeq, hIHinv⟩ := ih x' i (Q - w) (by omega) hcontR (by omega)
      refine ⟨i', Q', hIHeq, ?_⟩
      rw [markedVectorRaw_succ_even f x0 x hxne, ite_eq_right hxne0]
      have hLdef2 : (decodeVector (markedEntry false w :: markedVectorRaw f x0 x')).length =
          w + (decodeVector (markedVectorRaw f x0 x')).length := by
        unfold decodeVector
        simp only [List.flatMap_cons, List.length_append]
        simp only [markedEntry_false]
        unfold expandEntry
        rw [ite_eq_right (by omega : ¬ (0:ℤ) < -(w:ℤ))]
        rw [neg_neg]
        simp
      rw [hLdef2]
      omega
    · have hxeq : x % 2 = 1 := Nat.odd_iff.mp hxOdd
      set v := trailingOnes x with hv_def
      have hvpos : v ≥ 1 := by
        obtain ⟨j, hj⟩ := hxOdd
        exact one_le_padicValNat_of_dvd (by omega) ⟨j + 1, by omega⟩
      set x' := R x with hx'_def
      rw [finalX_succ_odd (f + 1) x0 x hxeq] at hcont
      have hxne0 : ¬ (x' < x0) := by
        intro hlt
        rw [ite_eq_left hlt] at hcont
        omega
      rw [ite_eq_right hxne0] at hcont
      have hcontR : finalX (f + 1) x0 x' ≥ x0 := hcont
      rw [markedVectorRaw_succ_odd (f + 1) x0 x hxeq, ite_eq_right hxne0] at hQ
      have hLdef : (decodeVector (markedEntry true v :: markedVectorRaw (f + 1) x0 x')).length =
          (v + 1) + (decodeVector (markedVectorRaw (f + 1) x0 x')).length := by
        unfold decodeVector
        simp only [List.flatMap_cons, List.length_append]
        simp only [markedEntry_true]
        unfold expandEntry
        rw [ite_eq_left (by exact_mod_cast hvpos : (0:ℤ) < (v:ℤ))]
        simp
      rw [hLdef] at hQ
      have hL' : (decodeVector (markedVectorRaw (f + 1) x0 x')).length ≥ 1 := by
        rcases Nat.even_or_odd x' with hx'Even | hx'Odd
        · have hx'ne : x' % 2 ≠ 1 := by
            rcases hx'Even with ⟨r, hr⟩
            omega
          have hw'pos : trailingZeros x' ≥ 1 :=
            one_le_padicValNat_of_dvd (by omega) (even_iff_two_dvd.mp hx'Even)
          rw [markedVectorRaw_succ_even f x0 x' hx'ne]
          have hentrylen : (expandEntry (-(trailingZeros x' : ℤ))).length = trailingZeros x' := by
            unfold expandEntry
            rw [ite_eq_right (by omega : ¬ (0:ℤ) < -(trailingZeros x' : ℤ))]
            rw [neg_neg]
            simp
          split
          · simp [decodeVector, hentrylen]
            omega
          · simp only [decodeVector, List.flatMap_cons, List.length_append, markedEntry_false,
              hentrylen]
            omega
        · have hx'eq2 : x' % 2 = 1 := Nat.odd_iff.mp hx'Odd
          have hv'pos : trailingOnes x' ≥ 1 := by
            obtain ⟨j, hj⟩ := hx'Odd
            exact one_le_padicValNat_of_dvd (by omega) ⟨j + 1, by omega⟩
          rw [markedVectorRaw_succ_odd f x0 x' hx'eq2]
          have hentrylen : (expandEntry (trailingOnes x' : ℤ)).length = trailingOnes x' + 1 := by
            unfold expandEntry
            rw [ite_eq_left (by exact_mod_cast hv'pos : (0:ℤ) < (trailingOnes x' : ℤ))]
            simp
          split
          · simp [decodeVector, hentrylen]
          · simp only [decodeVector, List.flatMap_cons, List.length_append, markedEntry_true,
              hentrylen]
            omega
      have hvQ : Q ≥ v + 1 := by omega
      have hvshift : trailingOnes (x + i * 2 ^ Q) = v := trailingOnes_shift x i Q hxOdd hvQ
      have hxine : (x + i * 2 ^ Q) % 2 = 1 := by
        have hxi_odd : Odd (x + i * 2 ^ Q) := by
          have hQ1 : Q ≥ 1 := by omega
          obtain ⟨j, hj⟩ := hxOdd
          refine ⟨j + i * 2 ^ (Q - 1), ?_⟩
          have h2 : i * 2 ^ Q = i * 2 ^ (Q - 1) * 2 := by
            rw [mul_assoc, ← pow_succ]
            congr 2
            omega
          omega
        exact Nat.odd_iff.mp hxi_odd
      have hRshift : R (x + i * 2 ^ Q) = x' + 3 ^ v * i * 2 ^ (Q - v - 1) :=
        R_shift_odd x i Q hx1 hxOdd hvQ
      rw [finalX_succ_odd f x0 (x + i * 2 ^ Q) hxine, hRshift]
      have hstopf : ¬ (x' + 3 ^ v * i * 2 ^ (Q - v - 1) < x0) := by omega
      rw [ite_eq_right hstopf]
      rw [finalX_succ_odd f x0 x hxeq, ite_eq_right hxne0]
      obtain ⟨i', Q', hIHeq, hIHinv⟩ := ih x' (3 ^ v * i) (Q - v - 1) (by omega) hcontR (by omega)
      refine ⟨i', Q', hIHeq, ?_⟩
      rw [markedVectorRaw_succ_odd f x0 x hxeq, ite_eq_right hxne0]
      have hLdef2 : (decodeVector (markedEntry true v :: markedVectorRaw f x0 x')).length =
          (v + 1) + (decodeVector (markedVectorRaw f x0 x')).length := by
        unfold decodeVector
        simp only [List.flatMap_cons, List.length_append]
        simp only [markedEntry_true]
        unfold expandEntry
        rw [ite_eq_left (by exact_mod_cast hvpos : (0:ℤ) < (v:ℤ))]
        simp
      rw [hLdef2]
      omega

/-- Shift-invariance of `markedVectorFinal` over two steps, odd then terminal
    even, for the shift i*2^(p2_of v). -/
theorem markedVectorFinal_shift_2 (x0 i : ℕ) (hx0 : x0 > 1) (hxodd : Odd x0)
    (hRx0ge : R x0 ≥ x0) (hRx0even : Even (R x0)) (hv2 : trailingOnes x0 ≥ 2)
    (hQge2 : p2_of (trailingOnes x0) ≥ trailingOnes x0 + 2)
    (hterm : R (R x0) < x0)
    (hsuff : R x0 < x0 * 2 ^ (p2_of (trailingOnes x0) - trailingOnes x0 - 1))
    (hmin : R x0 ≥ x0 * 2 ^ (p2_of (trailingOnes x0) - trailingOnes x0 - 2)) :
    markedVectorFinal 2 (x0 + i * 2 ^ (p2_of (trailingOnes x0)))
        (x0 + i * 2 ^ (p2_of (trailingOnes x0))) =
      markedVectorFinal 2 x0 x0 := by
  set v := trailingOnes x0 with hv_def
  set Q := p2_of v with hQ_def
  have hQge : Q ≥ v + 1 := by omega
  have hxeq : x0 % 2 = 1 := Nat.odd_iff.mp hxodd
  have hshift_odd : Odd (x0 + i * 2 ^ Q) := by
    have hQ1 : Q ≥ 1 := by omega
    obtain ⟨j, hj⟩ := hxodd
    refine ⟨j + i * 2 ^ (Q - 1), ?_⟩
    have h2 : i * 2 ^ Q = i * 2 ^ (Q - 1) * 2 := by
      rw [mul_assoc, ← pow_succ]
      congr 2
    omega
  have hshift_eq : (x0 + i * 2 ^ Q) % 2 = 1 := Nat.odd_iff.mp hshift_odd
  have hRshift : R (x0 + i * 2 ^ Q) = R x0 + 3 ^ v * i * 2 ^ (Q - v - 1) :=
    R_shift_odd x0 i Q hx0 hxodd hQge
  have hnoterm_x0 : ¬ (R x0 < x0) := by omega
  rw [markedVectorFinal_succ_odd 1 x0 x0 hxeq, ite_eq_right hnoterm_x0, ← hv_def]
  rw [markedVectorFinal_succ_odd 1 (x0 + i * 2 ^ Q) (x0 + i * 2 ^ Q) hshift_eq, hRshift]
  have h3v : (3:ℕ) ^ v ≥ 2 ^ (v + 1) := three_pow_ge_two_pow_succ v hv2
  have hnoterm_shift : ¬ (R x0 + 3 ^ v * i * 2 ^ (Q - v - 1) < x0 + i * 2 ^ Q) := by
    have hpow : (2:ℕ) ^ Q = 2 ^ (v + 1) * 2 ^ (Q - v - 1) := by
      rw [← pow_add]
      congr 1
      omega
    have hile : i * 2 ^ Q ≤ 3 ^ v * i * 2 ^ (Q - v - 1) := by
      rw [hpow]
      have heq2 : 3 ^ v * i * 2 ^ (Q - v - 1) = i * (3 ^ v * 2 ^ (Q - v - 1)) := by ring
      rw [heq2]
      exact Nat.mul_le_mul_left i (Nat.mul_le_mul_right _ h3v)
    omega
  rw [ite_eq_right hnoterm_shift]
  rw [show trailingOnes (x0 + i * 2 ^ Q) = v from trailingOnes_shift x0 i Q hxodd hQge]
  have hxeven : Even (R x0) := hRx0even
  have hRx0eq : R x0 % 2 ≠ 1 := by
    obtain ⟨r, hr⟩ := hxeven
    omega
  rw [markedVectorFinal_succ_even 0 x0 (R x0) hRx0eq]
  -- minCorrection x0 (R x0) = Q - v - 1
  have hmceq : minCorrection x0 (R x0) = Q - v - 1 :=
    minCorrection_unique x0 (R x0) (Q - v - 1) (by omega)
      ((Nat.div_lt_iff_lt_mul (by positivity)).mpr hsuff)
      (Or.inr (by
        rw [ge_iff_le, Nat.le_div_iff_mul_le (by positivity)]
        omega))
  have hReq : R (R x0) = R x0 / 2 ^ (trailingZeros (R x0)) :=
    R_even_closed_form (R x0) (by omega) hxeven
  have hv2ge : trailingZeros (R x0) ≥ Q - v - 1 := by
    have hwitness : R x0 / 2 ^ (trailingZeros (R x0)) < x0 := by
      rw [← hReq]
      exact hterm
    have := minCorrection_suff x0 (R x0) (by omega)
    by_contra hcon
    push Not at hcon
    have hmono : R x0 / 2 ^ (trailingZeros (R x0)) ≥ R x0 / 2 ^ (Q - v - 2) :=
      Nat.div_le_div_left (Nat.pow_le_pow_right (by norm_num) (by omega)) (by positivity)
    have hminDiv : R x0 / 2 ^ (Q - v - 2) ≥ x0 := by
      rw [ge_iff_le, Nat.le_div_iff_mul_le (by positivity)]
      omega
    omega
  have hRx0dvd : 2 ^ (Q - v - 1) ∣ R x0 :=
    dvd_trans (pow_dvd_pow 2 hv2ge) (pow_padicValNat_dvd (p := 2) (n := R x0))
  have hRx0ne : R x0 ≠ 0 := by omega
  have hterm_shift : R (R x0 + 3 ^ v * i * 2 ^ (Q - v - 1)) < x0 + i * 2 ^ Q := by
    have hsumdvd : 2 ^ (Q - v - 1) ∣ (R x0 + 3 ^ v * i * 2 ^ (Q - v - 1)) :=
      Dvd.dvd.add hRx0dvd ⟨3 ^ v * i, by ring⟩
    have hv2sum : trailingZeros (R x0 + 3 ^ v * i * 2 ^ (Q - v - 1)) ≥ Q - v - 1 := by
      have hne : R x0 + 3 ^ v * i * 2 ^ (Q - v - 1) ≠ 0 := by omega
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have := (padicValNat_dvd_iff (Q - v - 1) (R x0 + 3 ^ v * i * 2 ^ (Q - v - 1))).mp hsumdvd
      unfold trailingZeros
      omega
    have hRsumeq : R (R x0 + 3 ^ v * i * 2 ^ (Q - v - 1)) =
        (R x0 + 3 ^ v * i * 2 ^ (Q - v - 1)) /
          2 ^ (trailingZeros (R x0 + 3 ^ v * i * 2 ^ (Q - v - 1))) := by
      apply R_even_closed_form _ (by omega)
      obtain ⟨r, hr⟩ := hxeven
      have hQv1 : Q - v - 1 ≥ 1 := by omega
      have hpow : (2:ℕ) ^ (Q - v - 1) = 2 ^ (Q - v - 2) * 2 := by
        rw [← pow_succ]
        congr 1
        omega
      exact ⟨r + 3 ^ v * i * 2 ^ (Q - v - 2), by
        have h2 : 3 ^ v * i * 2 ^ (Q - v - 1) = 3 ^ v * i * 2 ^ (Q - v - 2) * 2 := by
          rw [hpow]
          ring
        omega⟩
    rw [hRsumeq]
    have hmono : (R x0 + 3 ^ v * i * 2 ^ (Q - v - 1)) /
        2 ^ (trailingZeros (R x0 + 3 ^ v * i * 2 ^ (Q - v - 1))) ≤
        (R x0 + 3 ^ v * i * 2 ^ (Q - v - 1)) / 2 ^ (Q - v - 1) :=
      Nat.div_le_div_left (Nat.pow_le_pow_right (by norm_num) hv2sum) (by positivity)
    have hsuff2 := minCorrection_suff_shift_gen x0 i Q hx0 hxodd
      (by
        rw [← hv_def]
        exact_mod_cast p2_of_spec v)
      (by
        rw [← hv_def]
        exact hsuff)
    rw [hRshift] at hsuff2
    have hdiv : (R x0 + 3 ^ v * i * 2 ^ (Q - v - 1)) / 2 ^ (Q - v - 1) < x0 + i * 2 ^ Q := by
      rw [Nat.div_lt_iff_lt_mul (by positivity)]
      rw [← hv_def] at hsuff2
      exact hsuff2
    omega
  have hRxeven_shift : (R x0 + 3 ^ v * i * 2 ^ (Q - v - 1)) % 2 ≠ 1 := by
    have hxi_even : Even (R x0 + 3 ^ v * i * 2 ^ (Q - v - 1)) := by
      obtain ⟨r, hr⟩ := hxeven
      have hQv1 : Q - v - 1 ≥ 1 := by omega
      have hpow : (2:ℕ) ^ (Q - v - 1) = 2 ^ (Q - v - 2) * 2 := by
        rw [← pow_succ]
        congr 1
        omega
      exact ⟨r + 3 ^ v * i * 2 ^ (Q - v - 2), by
        have h2 : 3 ^ v * i * 2 ^ (Q - v - 1) = 3 ^ v * i * 2 ^ (Q - v - 2) * 2 := by
          rw [hpow]
          ring
        omega⟩
    obtain ⟨s, hs⟩ := hxi_even
    omega
  rw [markedVectorFinal_succ_even 0 (x0 + i * 2 ^ Q) (R x0 + 3 ^ v * i * 2 ^ (Q - v - 1))
    hRxeven_shift]
  rw [ite_eq_left hterm, ite_eq_left hterm_shift]
  congr 2
  have hmceq_shift : minCorrection (x0 + i * 2 ^ Q) (R x0 + 3 ^ v * i * 2 ^ (Q - v - 1)) =
      Q - v - 1 := by
    have hsuff2 := minCorrection_suff_shift_gen x0 i Q hx0 hxodd
      (by
        rw [← hv_def]
        exact_mod_cast p2_of_spec v)
      (by
        rw [← hv_def]
        exact hsuff)
    have hmin2 := minCorrection_min_shift x0 i hx0 hxodd hQge2
      (by
        rw [← hv_def]
        exact hmin)
    rw [hRshift] at hsuff2 hmin2
    exact minCorrection_unique (x0 + i * 2 ^ Q) (R x0 + 3 ^ v * i * 2 ^ (Q - v - 1)) (Q - v - 1)
      (by omega)
      ((Nat.div_lt_iff_lt_mul (by positivity)).mpr hsuff2)
      (Or.inr (by
        rw [ge_iff_le, Nat.le_div_iff_mul_le (by positivity)]
        omega))
  rw [hmceq, hmceq_shift]

/-- The same for `markedVector`. -/
theorem markedVector_shift_2 (x0 i : ℕ) (hx0 : x0 > 1) (hxodd : Odd x0)
    (hRx0ge : R x0 ≥ x0) (hRx0even : Even (R x0)) (hv2 : trailingOnes x0 ≥ 2)
    (hQge2 : p2_of (trailingOnes x0) ≥ trailingOnes x0 + 2)
    (hterm : R (R x0) < x0)
    (hsuff : R x0 < x0 * 2 ^ (p2_of (trailingOnes x0) - trailingOnes x0 - 1))
    (hmin : R x0 ≥ x0 * 2 ^ (p2_of (trailingOnes x0) - trailingOnes x0 - 2)) :
    markedVector 2 (x0 + i * 2 ^ (p2_of (trailingOnes x0)))
        (x0 + i * 2 ^ (p2_of (trailingOnes x0))) =
      markedVector 2 x0 x0 := by
  rw [markedVector_eq_markedVectorFinal (x0 + i * 2 ^ (p2_of (trailingOnes x0))) (by omega)
        2 (x0 + i * 2 ^ (p2_of (trailingOnes x0))) (le_refl _),
      markedVector_eq_markedVectorFinal x0 (by omega) 2 x0 (le_refl _)]
  exact markedVectorFinal_shift_2 x0 i hx0 hxodd hRx0ge hRx0even hv2 hQge2 hterm hsuff hmin

/-- 2^(v1 + v2 + 2) ≤ 3^(v1 + v2) for v1, v2 ≥ 2. -/
theorem three_pow_ge_two_pow_succ_add (v1 v2 : ℕ) (hv1 : v1 ≥ 2) (hv2 : v2 ≥ 2) :
    (3:ℕ) ^ (v1 + v2) ≥ 2 ^ (v1 + v2 + 2) := by
  have h1 := three_pow_ge_two_pow_succ v1 hv1
  have h2 := three_pow_ge_two_pow_succ v2 hv2
  have hmul : (3:ℕ) ^ v1 * 3 ^ v2 ≥ 2 ^ (v1 + 1) * 2 ^ (v2 + 1) :=
    Nat.mul_le_mul h1 h2
  rw [← pow_add, ← pow_add] at hmul
  have heq : v1 + 1 + (v2 + 1) = v1 + v2 + 2 := by omega
  rwa [heq] at hmul

/-- `minCorrection_suff_shift_gen` with the threshold x0 apart from the value
    x_init. -/
theorem minCorrection_suff_shift_gen2 (x0 x_init i Q : ℕ) (hx1 : x_init > 1) (hxodd : Odd x_init)
    (hQspec : (3 : ℕ) ^ (trailingOnes x_init) < 2 ^ Q)
    (hsuff : R x_init < x0 * 2 ^ (Q - trailingOnes x_init - 1)) :
    R (x_init + i * 2 ^ Q) < (x0 + i * 2 ^ Q) * 2 ^ (Q - trailingOnes x_init - 1) := by
  set v := trailingOnes x_init with hv_def
  have hQge : Q ≥ v + 1 := by
    have h2 : (3:ℕ) ^ v ≥ 2 ^ v := Nat.pow_le_pow_left (by norm_num) v
    have h4 : v < Q := by
      by_contra hcon
      push Not at hcon
      have hcontra : (2:ℕ) ^ Q ≤ 2 ^ v := Nat.pow_le_pow_right (by norm_num) hcon
      omega
    omega
  rw [R_shift_odd x_init i Q hx1 hxodd hQge, ← hv_def]
  have hexpand : (x0 + i * 2 ^ Q) * 2 ^ (Q - v - 1) =
      x0 * 2 ^ (Q - v - 1) + i * 2 ^ Q * 2 ^ (Q - v - 1) := by ring
  rw [hexpand]
  have hile : 3 ^ v * i * 2 ^ (Q - v - 1) ≤ i * 2 ^ Q * 2 ^ (Q - v - 1) := by
    have h1 : (3:ℕ) ^ v ≤ 2 ^ Q := le_of_lt hQspec
    have h2 : 3 ^ v * (i * 2 ^ (Q - v - 1)) ≤ 2 ^ Q * (i * 2 ^ (Q - v - 1)) :=
      Nat.mul_le_mul_right _ h1
    nlinarith [h2]
  omega

/-- `minCorrection_min_shift` with the threshold x0 apart from the value x_init,
    for any Q with 2^(Q - 1) ≤ 3^v. -/
theorem minCorrection_min_shift_gen2 (x0 x_init i Q : ℕ) (hx1 : x_init > 1) (hxodd : Odd x_init)
    (hQge2 : Q ≥ trailingOnes x_init + 2)
    (hQspec : (2 : ℕ) ^ (Q - 1) ≤ 3 ^ (trailingOnes x_init))
    (hmin : R x_init ≥ x0 * 2 ^ (Q - trailingOnes x_init - 2)) :
    R (x_init + i * 2 ^ Q) ≥ (x0 + i * 2 ^ Q) * 2 ^ (Q - trailingOnes x_init - 2) := by
  set v := trailingOnes x_init with hv_def
  have hQge : Q ≥ v + 1 := by omega
  rw [R_shift_odd x_init i Q hx1 hxodd hQge, ← hv_def]
  have hexpand : (x0 + i * 2 ^ Q) * 2 ^ (Q - v - 2) =
      x0 * 2 ^ (Q - v - 2) + i * 2 ^ Q * 2 ^ (Q - v - 2) := by ring
  rw [hexpand]
  have hile : 3 ^ v * i * 2 ^ (Q - v - 1) ≥ i * 2 ^ Q * 2 ^ (Q - v - 2) := by
    have heq1 : i * 2 ^ Q * 2 ^ (Q - v - 2) = i * (2 ^ Q * 2 ^ (Q - v - 2)) := by ring
    rw [heq1]
    have heq1b : (2:ℕ) ^ Q * 2 ^ (Q - v - 2) = 2 ^ (2 * Q - v - 2) := by
      rw [← pow_add]
      congr 1
      omega
    rw [heq1b]
    have heq2 : 3 ^ v * i * 2 ^ (Q - v - 1) = i * (3 ^ v * 2 ^ (Q - v - 1)) := by ring
    rw [heq2]
    have hpoweq : (2:ℕ) ^ (2 * Q - v - 2) = 2 ^ (Q - 1) * 2 ^ (Q - v - 1) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hpoweq]
    have h1 : (2:ℕ) ^ (Q - 1) * 2 ^ (Q - v - 1) ≤ 3 ^ v * 2 ^ (Q - v - 1) :=
      Nat.mul_le_mul_right _ hQspec
    have h2 : i * (2 ^ (Q - 1) * 2 ^ (Q - v - 1)) ≤ i * (3 ^ v * 2 ^ (Q - v - 1)) :=
      Nat.mul_le_mul_left i h1
    exact h2
  omega

/-- `rFoldFrom` from r0: `seqProduct bits * r0 + rFold bits`. -/
theorem rFoldFrom_eq_seqProduct (r0 : ℚ) (bits : List Bool) :
    rFoldFrom r0 bits = seqProduct bits * r0 + rFold bits := by
  rw [rFoldFrom_linear, seqProduct_eq_pow_ratio, rFold]

/-- drop * 2^length ≥ x * 3^order for the components of `trajStats`,
    for x ≥ x0 > 1. -/
theorem trajStats_lower_bound (x0 : ℕ) (hx0 : x0 > 1) :
    ∀ fuel x, x0 ≤ x →
      (trajStats x0 fuel x).2.2 * 2 ^ (trajStats x0 fuel x).2.1 ≥
        x * 3 ^ (trajStats x0 fuel x).1 := by
  intro fuel
  induction fuel with
  | zero =>
    intro x _
    simp [trajStats]
  | succ fuel ih =>
    intro x hxge
    have hx1' : x > 1 := by omega
    unfold trajStats
    by_cases hxodd : x % 2 = 1
    · simp only [hxodd, ite_true]
      have hxOddP : Odd x := Nat.odd_iff.mpr hxodd
      set v := trailingOnes x with hv_def
      have hdvd : 2 ^ v ∣ (x + 1) := pow_trailingOnes_dvd x
      set s := (x + 1) / 2 ^ v with hs_def
      have hsmul : s * 2 ^ v = x + 1 := Nat.div_mul_cancel hdvd
      have hsOdd : Odd s := odd_div_pow_trailingOnes x hxOddP
      have hRclosed : R x = (3 ^ v * s - 1) / 2 := R_odd_closed_form x hx1' hxOddP
      have h3vsOdd : Odd (3 ^ v * s) := ((by decide : Odd 3).pow).mul hsOdd
      have hexact : 2 * R x + 1 = 3 ^ v * s := by
        obtain ⟨k, hk⟩ := h3vsOdd
        rw [hRclosed, hk]
        omega
      have hv2 : (2:ℕ) ^ (v + 1) * R x = 3 ^ v * x + (3 ^ v - 2 ^ v) := by
        have hstep : (2 * R x + 1) * 2 ^ v = 3 ^ v * s * 2 ^ v := by rw [hexact]
        have hkey : 2 ^ (v + 1) * R x + 2 ^ v = 3 ^ v * x + 3 ^ v := by
          calc 2 ^ (v + 1) * R x + 2 ^ v = (2 * R x + 1) * 2 ^ v := by
                rw [pow_succ]
                ring
            _ = 3 ^ v * s * 2 ^ v := hstep
            _ = 3 ^ v * (s * 2 ^ v) := by ring
            _ = 3 ^ v * (x + 1) := by rw [hsmul]
            _ = 3 ^ v * x + 3 ^ v := by ring
        have hle32 : (2:ℕ) ^ v ≤ 3 ^ v := Nat.pow_le_pow_left (by norm_num) _
        omega
      rw [mul_comm (3 ^ v) x] at hv2
      rw [mul_comm ((2:ℕ) ^ (v + 1)) (R x)] at hv2
      by_cases hterm : R x < x0
      · simp only [hterm, ite_true]
        omega
      · simp only [hterm, ite_false]
        set p := trajStats x0 fuel (R x) with hp_def
        have hIH := ih (R x) (by omega)
        rw [← hp_def] at hIH
        have hRx2 : R x * 2 ^ (trailingOnes x + 1) ≥ x * 3 ^ (trailingOnes x) := by
          rw [← hv_def]
          omega
        calc p.2.2 * 2 ^ (trailingOnes x + 1 + p.2.1)
            = p.2.2 * 2 ^ p.2.1 * 2 ^ (trailingOnes x + 1) := by ring
          _ ≥ R x * 3 ^ p.1 * 2 ^ (trailingOnes x + 1) := by
              have := Nat.mul_le_mul_right (2 ^ (trailingOnes x + 1)) hIH
              linarith
          _ = (R x * 2 ^ (trailingOnes x + 1)) * 3 ^ p.1 := by ring
          _ ≥ (x * 3 ^ (trailingOnes x)) * 3 ^ p.1 := by
              exact Nat.mul_le_mul_right _ hRx2
          _ = x * 3 ^ (trailingOnes x + p.1) := by
            rw [pow_add]
            ring
    · simp only [hxodd, ite_false]
      have hxeven : Even x := Nat.even_iff.mpr (by omega)
      have hx1 : x > 1 := by
        obtain ⟨r, hr⟩ := hxeven
        omega
      have hReq : R x = x / 2 ^ (trailingZeros x) := R_even_closed_form x hx1 hxeven
      by_cases hterm : x / 2 ^ (trailingZeros x) < x0
      · simp only [hterm, ite_true]
        have hmcle : minCorrection x0 x ≤ trailingZeros x := by
          by_contra hcon
          push Not at hcon
          have hpos : minCorrection x0 x ≥ 1 := by omega
          have hmin := minCorrection_min x0 x (by omega) hpos
          have hmono : x / 2 ^ (minCorrection x0 x - 1) ≤ x / 2 ^ (trailingZeros x) :=
            Nat.div_le_div_left (Nat.pow_le_pow_right (by norm_num) (by omega)) (by positivity)
          omega
        have hdvd : 2 ^ (minCorrection x0 x) ∣ x :=
          dvd_trans (pow_dvd_pow 2 hmcle) (pow_padicValNat_dvd (p := 2) (n := x))
        have hexact : x / 2 ^ (minCorrection x0 x) * 2 ^ (minCorrection x0 x) = x :=
          Nat.div_mul_cancel hdvd
        omega
      · simp only [hterm, ite_false]
        set p := trajStats x0 fuel (x / 2 ^ (trailingZeros x)) with hp_def
        have hIH := ih (x / 2 ^ (trailingZeros x)) (by omega)
        rw [← hp_def] at hIH
        have hdvd : 2 ^ (trailingZeros x) ∣ x := pow_padicValNat_dvd (p := 2) (n := x)
        have heq : x / 2 ^ (trailingZeros x) * 2 ^ (trailingZeros x) = x := Nat.div_mul_cancel hdvd
        calc p.2.2 * 2 ^ (trailingZeros x + p.2.1)
            = p.2.2 * 2 ^ p.2.1 * 2 ^ (trailingZeros x) := by ring
          _ ≥ (x / 2 ^ (trailingZeros x)) * 3 ^ p.1 * 2 ^ (trailingZeros x) := by
              exact Nat.mul_le_mul_right _ hIH
          _ = (x / 2 ^ (trailingZeros x) * 2 ^ (trailingZeros x)) * 3 ^ p.1 := by ring
          _ = x * 3 ^ p.1 := by rw [heq]

/-- Once `trajStats` has terminated (drop < x0), extra fuel does not
    change its output. -/
theorem trajStats_stable (x0 : ℕ) (hx0 : x0 > 1) :
    ∀ fuel x, x0 ≤ x → (trajStats x0 fuel x).2.2 < x0 →
      trajStats x0 (fuel + 1) x = trajStats x0 fuel x := by
  intro fuel
  induction fuel with
  | zero =>
    intro x hxge hterm
    simp only [trajStats] at hterm
    exfalso
    omega
  | succ fuel ih =>
    intro x hxge hterm
    have hx1 : x > 1 := by omega
    unfold trajStats at hterm ⊢
    by_cases hxodd : x % 2 = 1
    · simp only [hxodd, ite_true] at hterm ⊢
      by_cases h0 : R x < x0
      · simp only [h0, ite_true]
      · simp only [h0, ite_false] at hterm ⊢
        rw [ih (R x) (by omega) hterm]
    · simp only [hxodd, ite_false] at hterm ⊢
      by_cases h0 : x / 2 ^ (trailingZeros x) < x0
      · simp only [h0, ite_true]
      · simp only [h0, ite_false] at hterm ⊢
        rw [ih (x / 2 ^ (trailingZeros x)) (by omega) hterm]

/-- Once `trajStats` has ended (drop < x0), k more fuel does not change it. -/
theorem trajStats_stable' (x0 : ℕ) (hx0 : x0 > 1) :
    ∀ fuel k x, x0 ≤ x → (trajStats x0 fuel x).2.2 < x0 →
      trajStats x0 (fuel + k) x = trajStats x0 fuel x := by
  intro fuel k
  induction k with
  | zero =>
    intro x _ _
    simp
  | succ k ih =>
    intro x hxge hterm
    have h1 := ih x hxge hterm
    have h2 : fuel + (k + 1) = (fuel + k) + 1 := by ring
    rw [h2, trajStats_stable x0 hx0 (fuel + k) x hxge (h1 ▸ hterm), h1]

-- from MarkedVectorShift

/-- If x halved k times is below x0, the shifted x halved k times is below the
    shifted x0. -/
theorem crossing_shift_sufficiency (x0 i Q x oc lc k : ℕ) (hx0 : x0 > 1)
    (_hxge : x0 ≤ x) (hlcQ : lc ≤ Q) (hQrem : Q - lc ≥ k)
    (hprefix : x * 2 ^ lc ≥ x0 * 3 ^ oc) (_hkdvd : 2 ^ k ∣ x) (hksuff : x / 2 ^ k < x0) :
    (x + i * 3 ^ oc * 2 ^ (Q - lc)) / 2 ^ k < x0 + i * 2 ^ Q := by
  have hxlt : x < x0 * 2 ^ k := by
    rw [Nat.div_lt_iff_lt_mul (by positivity)] at hksuff
    omega
  have hcross : x0 * 2 ^ (k + lc) > x0 * 3 ^ oc := by
    have h1 : x0 * 2 ^ k * 2 ^ lc > x * 2 ^ lc := by
      have h2vpos : 0 < (2:ℕ) ^ lc := by positivity
      exact (Nat.mul_lt_mul_right h2vpos).mpr hxlt
    have heq : x0 * 2 ^ k * 2 ^ lc = x0 * 2 ^ (k + lc) := by
      rw [pow_add]
      ring
    omega
  have hcross2 : (2:ℕ) ^ (k + lc) > 3 ^ oc := by
    have hx0pos : 0 < x0 := by omega
    exact lt_of_mul_lt_mul_left hcross (le_of_lt hx0pos)
  have hpoweq : (2:ℕ) ^ (Q - lc) = 2 ^ k * 2 ^ (Q - lc - k) := by
    rw [← pow_add]
    congr 1
    omega
  have hswap : i * 3 ^ oc * 2 ^ (Q - lc) = (i * 3 ^ oc * 2 ^ (Q - lc - k)) * 2 ^ k := by
    rw [hpoweq]
    ring
  rw [hswap]
  have h2kpos : (0:ℕ) < 2 ^ k := by positivity
  rw [Nat.add_mul_div_right x (i * 3 ^ oc * 2 ^ (Q - lc - k)) h2kpos]
  have hstep1 : i * 3 ^ oc * 2 ^ (Q - lc - k) < i * 2 ^ Q ∨ i = 0 := by
    rcases Nat.eq_zero_or_pos i with hi0 | hipos
    · right
      exact hi0
    · left
      have hkey : 3 ^ oc * 2 ^ (Q - lc - k) < 2 ^ Q := by
        have heq2 : (2:ℕ) ^ Q = 2 ^ (k + lc) * 2 ^ (Q - lc - k) := by
          rw [← pow_add]
          congr 1
          omega
        rw [heq2]
        have hpos2 : 0 < (2:ℕ) ^ (Q - lc - k) := by positivity
        exact (Nat.mul_lt_mul_right hpos2).mpr hcross2
      calc i * 3 ^ oc * 2 ^ (Q - lc - k) = i * (3 ^ oc * 2 ^ (Q - lc - k)) := by ring
        _ < i * 2 ^ Q := (Nat.mul_lt_mul_left hipos).mpr hkey
  rcases hstep1 with h | h
  · omega
  · simp [h]
    omega

-- from Tree

theorem childAt_strictMono (t m : ℕ) : StrictMono (childAt t m) := by
  intro i j hij
  have h2 : (2:ℕ) ^ i < 2 ^ j := Nat.pow_lt_pow_right (by omega) hij
  have hm : (0:ℕ) < 2 ^ m := by positivity
  simp only [childAt, Nat.shiftLeft_eq]
  exact (Nat.mul_lt_mul_right hm).mpr (by omega)

-- from TChain

/-- A chain block has level above 1/2. -/
theorem half_lt_seqProduct (b : List Bool) (hb : IsChainBlock b) : 1 / 2 < seqProduct b := by
  have hne : b ≠ [] := ne_nil_of_admissible b hb.adm
  have hlast := admissible_last_false b hb.adm hne
  have hsplit : b = b.dropLast ++ [false] := by
    conv_lhs => rw [← List.dropLast_append_getLast hne]
    rw [hlast]
  have hdne : b.dropLast ≠ [] := by
    intro hn
    rw [hn, List.nil_append] at hsplit
    have h1 := hb.order_pos
    rw [hsplit] at h1
    simp [order] at h1
  have hlen : b.dropLast.length < b.length := by
    rw [List.length_dropLast]
    have := List.length_pos_iff.mpr hne
    omega
  have hpre := hb.adm.prefix_gt b.dropLast.length (List.length_pos_iff.mpr hdne) hlen
  have htk : b.take b.dropLast.length = b.dropLast := by
    rw [List.length_dropLast]
    exact List.dropLast_eq_take.symm
  rw [htk] at hpre
  rw [hsplit, seqProduct_append, seqProduct_singleton_false]
  linarith

-- from OrderPreservation

/-- Order of a trajectory: the sum of `stepOrder` along the path, fuel-bounded. -/
def trajectoryOrder : (fuel : ℕ) → (x0 x : ℕ) → ℕ
  | 0, _, _ => 0
  | fuel + 1, x0, x =>
    let x' := R x
    if x' < x0 then stepOrder x
    else stepOrder x + trajectoryOrder fuel x0 x'

/-- One step's marked entry, clipped at 0, is `stepOrder` at that point, for x > 0:
    trailingOnes x at an odd step, 0 at an even step (entry -(trailingZeros x)). -/
theorem markedEntry_clip_eq_stepOrder (x : ℕ) (hxpos : x > 0) :
    max 0 (markedEntry (stepInfo x).1 (stepInfo x).2.1) = (stepOrder x : ℤ) := by
  unfold markedEntry stepInfo stepOrder
  by_cases hx : x % 2 = 1
  · have hodd : Odd x := Nat.odd_iff.mpr hx
    simp [hx, hodd]
  · have heven : ¬ Odd x := by
      rw [Nat.odd_iff]
      exact hx
    have hv1 : trailingZeros x ≥ 1 :=
      one_le_padicValNat_of_dvd (by omega) ⟨x / 2, by omega⟩
    simp [hx, heven]

theorem markedVectorRaw_succ (fuel x0 x : ℕ) :
    markedVectorRaw (fuel + 1) x0 x =
      if R x < x0 then [markedEntry (stepInfo x).1 (stepInfo x).2.1]
      else markedEntry (stepInfo x).1 (stepInfo x).2.1 :: markedVectorRaw fuel x0 (R x) := by
  simp only [markedVectorRaw, stepInfo]
  split_ifs
  · rfl
  · rfl
  · rfl
  · rfl

theorem trajectoryOrder_succ (fuel x0 x : ℕ) :
    trajectoryOrder (fuel + 1) x0 x =
      if R x < x0 then stepOrder x else stepOrder x + trajectoryOrder fuel x0 (R x) := by
  simp [trajectoryOrder]

set_option linter.flexible false in
theorem sum_pos_markedVectorRaw (fuel x0 x : ℕ) (hxpos : x > 0) :
    (((markedVectorRaw fuel x0 x).filter (· > 0)).sum : ℤ) = (trajectoryOrder fuel x0 x : ℤ) := by
  induction fuel generalizing x with
  | zero => simp [markedVectorRaw, trajectoryOrder]
  | succ fuel ih =>
    rw [markedVectorRaw_succ, trajectoryOrder_succ]
    set entry := markedEntry (stepInfo x).1 (stepInfo x).2.1 with hentry_def
    have hclip : max 0 entry = (stepOrder x : ℤ) := by
      rw [hentry_def]
      exact markedEntry_clip_eq_stepOrder x hxpos
    by_cases hdrop : R x < x0
    · simp only [hdrop, ite_true]
      by_cases hpos : entry > 0
      · simp [List.filter, hpos, List.sum_cons, List.sum_nil]
        rw [max_eq_right (le_of_lt hpos)] at hclip
        exact_mod_cast hclip
      · simp [List.filter, hpos, List.sum_nil]
        rw [max_eq_left (by omega)] at hclip
        exact_mod_cast hclip
    · simp only [hdrop, ite_false]
      have hRge := R_ge_one x
      have hih := ih (R x) (by omega)
      push Not at hdrop
      by_cases hpos : entry > 0
      · simp only [List.filter_cons, decide_eq_true_eq, hpos, ite_true, List.sum_cons]
        rw [max_eq_right (le_of_lt hpos)] at hclip
        rw [hclip]
        push_cast
        rw [← hih]
      · simp only [List.filter_cons, decide_eq_true_eq, hpos, ite_false]
        rw [max_eq_left (by omega)] at hclip
        push_cast
        rw [← hih, ← hclip]
        ring

end AcceleratedCollatz
