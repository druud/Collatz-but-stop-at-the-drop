-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TMonksDrop

/-!
  Monks' 2-adic reading xi (OEIS A401592, A401593), in integers and rationals only. xi reads
  a series over F_2 as a 2-adic number, the coefficient of q^i as the binary digit of 2^i.
  For a rational r = a/b with b odd, `IsXi y r` says a ≡ b (y mod q^k, read in binary)
  (mod 2^k) for every k; then r is unique (`isXi_unique`) and its denominator is odd
  (`den_odd_of_isXi`). A shift by q doubles xi (`isXi_X_mul`), and since the denominator is
  odd the numerator doubles too (`num_den_two_mul_of_isXi`). Digits periodic from p on with
  period e give xi = N + 2^p C/(1 - 2^e), a denominator dividing 2^e - 1
  (`isXi_of_periodic`). For Monks' T_q (A = 1 + q, B = 1) a conjugacy h, read by the drops
  (every m with 1 < m ≤ n drops), gives h(n) (1 + q)^k (1 + q + q^2) a polynomial
  (`monksQ_den`), so the digits of h(n) are periodic with period 3 2^c and xi(h(n)) has a
  denominator dividing 2^(3 2^c) - 1 (`monksQ_isXi`). With k the odd steps over the drop
  chain n → T^L(n) → ... → 1 (`DropOdd`; k = A006667(n), counted by the drops), any c with
  k ≤ 2^c will do (`monksQ_isXi_of_dropOdd`). And xi(h(2n)) = 2 xi(h(n)), numerators
  doubled (`monksQ_isXi_two_mul`).
-/

namespace AcceleratedCollatz

open PowerSeries

noncomputable section

/-! ### Digit sums -/

/-- The first k digits of f, read in binary: the sum of f(i) 2^i over i < k. -/
def digitPart (f : ℕ → ℤ) (k : ℕ) : ℤ := ∑ i ∈ Finset.range k, f i * 2 ^ i

theorem digitPart_add (f : ℕ → ℤ) (m n : ℕ) :
    digitPart f (m + n) = digitPart f m + 2 ^ m * digitPart (fun i => f (m + i)) n := by
  unfold digitPart
  rw [Finset.sum_range_add, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pow_add]
  ring

theorem dvd_digitPart_sub (f : ℕ → ℤ) {k n : ℕ} (hkn : k ≤ n) :
    (2 : ℤ) ^ k ∣ digitPart f n - digitPart f k := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hkn
  rw [digitPart_add]
  exact ⟨digitPart (fun i => f (k + i)) t, by ring⟩

/-- An integer divisible by every power of 2 is 0. -/
theorem eq_zero_of_two_pow_dvd {d : ℤ} (h : ∀ k, (2 : ℤ) ^ k ∣ d) : d = 0 := by
  by_contra hne
  have h1 := Int.natAbs_dvd_natAbs.mpr (h d.natAbs)
  rw [Int.natAbs_pow] at h1
  have h2 := Nat.le_of_dvd (Int.natAbs_pos.mpr hne) h1
  have h3 := Nat.lt_two_pow_self (n := d.natAbs)
  simp at h2
  omega

/-! ### xi -/

/-- The digit of q^i in y, as 0 or 1. -/
def xiDigit (y : QSeries) (i : ℕ) : ℤ := ((coeff i y).val : ℤ)

/-- y mod q^k read in binary: xi(y) mod 2^k. -/
def xiPart (y : QSeries) (k : ℕ) : ℤ := digitPart (xiDigit y) k

/-- xi(y) = r: r = a/b with b odd and a ≡ b xiPart y k (mod 2^k) for every k. -/
def IsXi (y : QSeries) (r : ℚ) : Prop :=
  ∃ a : ℤ, ∃ b : ℕ, b % 2 = 1 ∧ r = a / b ∧ ∀ k, (2 : ℤ) ^ k ∣ a - b * xiPart y k

/-- xi(y) is unique. -/
theorem isXi_unique {y : QSeries} {r r' : ℚ} (h : IsXi y r) (h' : IsXi y r') : r = r' := by
  obtain ⟨a, b, hb, rfl, hk⟩ := h
  obtain ⟨a', b', hb', rfl, hk'⟩ := h'
  have hd : ∀ k, (2 : ℤ) ^ k ∣ a * b' - a' * b := by
    intro k
    have e : a * b' - a' * b =
        (a - b * xiPart y k) * b' - (a' - b' * xiPart y k) * b := by ring
    rw [e]
    exact dvd_sub (dvd_mul_of_dvd_left (hk k) _) (dvd_mul_of_dvd_left (hk' k) _)
  have h0 := eq_zero_of_two_pow_dvd hd
  have hb0 : (b : ℚ) ≠ 0 := by
    have : b ≠ 0 := by omega
    exact_mod_cast this
  have hb0' : (b' : ℚ) ≠ 0 := by
    have : b' ≠ 0 := by omega
    exact_mod_cast this
  rw [div_eq_div_iff hb0 hb0']
  have h1 : a * (b' : ℤ) = a' * b := by linarith
  exact_mod_cast h1

/-- The denominator of xi(y) is odd. -/
theorem den_odd_of_isXi {y : QSeries} {r : ℚ} (h : IsXi y r) : r.den % 2 = 1 := by
  obtain ⟨a, b, hb, rfl, -⟩ := h
  have hd := Rat.den_dvd a b
  rw [Rat.divInt_eq_div] at hd
  push_cast at hd
  have hd' : (a / b : ℚ).den ∣ b := by exact_mod_cast hd
  obtain ⟨c, hc⟩ := hd'
  rw [hc, Nat.mul_mod] at hb
  rcases Nat.mod_two_eq_zero_or_one (a / b : ℚ).den with h0 | h0
  · rw [h0] at hb
    simp at hb
  · exact h0

theorem xiDigit_X_mul_zero (y : QSeries) : xiDigit (X * y) 0 = 0 := by
  simp [xiDigit, coeff_zero_X_mul]

theorem xiDigit_X_mul_succ (y : QSeries) (i : ℕ) : xiDigit (X * y) (i + 1) = xiDigit y i := by
  simp [xiDigit, coeff_succ_X_mul]

theorem xiPart_X_mul (y : QSeries) (k : ℕ) : xiPart (X * y) (k + 1) = 2 * xiPart y k := by
  unfold xiPart digitPart
  rw [Finset.sum_range_succ', xiDigit_X_mul_zero, Finset.mul_sum]
  simp only [xiDigit_X_mul_succ, zero_mul, add_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- A shift by q doubles xi. -/
theorem isXi_X_mul {y : QSeries} {r : ℚ} (h : IsXi y r) : IsXi (X * y) (2 * r) := by
  obtain ⟨a, b, hb, rfl, hk⟩ := h
  refine ⟨2 * a, b, hb, by push_cast; ring, ?_⟩
  intro k
  cases k with
  | zero => simp
  | succ k =>
    rw [xiPart_X_mul, pow_succ]
    have e : 2 * a - b * (2 * xiPart y k) = (a - b * xiPart y k) * 2 := by ring
    rw [e]
    exact mul_dvd_mul_right (hk k) 2

/-- With an odd denominator, doubling doubles the numerator. -/
theorem num_den_two_mul_of_isXi {y : QSeries} {r : ℚ} (h : IsXi y r) :
    (2 * r).num = 2 * r.num ∧ (2 * r).den = r.den := by
  have hodd := den_odd_of_isXi h
  have hr : 2 * r = ((2 * r.num : ℤ) : ℚ) / ((r.den : ℤ) : ℚ) := by
    push_cast
    rw [mul_div_assoc, Rat.num_div_den]
  have hpos : (0 : ℤ) < r.den := by exact_mod_cast r.den_pos
  have hcop : Nat.Coprime (2 * r.num).natAbs (r.den : ℤ).natAbs := by
    rw [Int.natAbs_mul, Int.natAbs_natCast]
    exact Nat.coprime_mul_iff_left.mpr
      ⟨Nat.coprime_two_left.mpr (Nat.odd_iff.mpr hodd), r.reduced⟩
  rw [hr]
  refine ⟨Rat.num_div_eq_of_coprime hpos hcop, ?_⟩
  have := Rat.den_div_eq_of_coprime hpos hcop
  exact_mod_cast this

/-! ### Periodic digits -/

/-- The digits of y repeat with period e from position p on. -/
def IsEvPeriodic (y : QSeries) (p e : ℕ) : Prop :=
  ∀ i, p ≤ i → coeff (i + e) y = coeff i y

/-- Periodic digits: xi(y) = N + 2^p C/(1 - 2^e), its denominator dividing 2^e - 1. -/
theorem isXi_of_periodic {y : QSeries} {p e : ℕ} (he : 1 ≤ e) (h : IsEvPeriodic y p e) :
    ∃ r : ℚ, IsXi y r ∧ r.den ∣ 2 ^ e - 1 := by
  set g : ℕ → ℤ := fun i => xiDigit y (p + i) with hg
  have hper : ∀ i, g (e + i) = g i := by
    intro i
    simp only [hg, xiDigit]
    rw [show p + (e + i) = (p + i) + e by omega, h (p + i) (by omega)]
  set C := digitPart g e with hC
  have hT : ∀ t, digitPart g (e + t) = C + 2 ^ e * digitPart g t := by
    intro t
    rw [digitPart_add]
    congr 3
    funext i
    exact hper i
  have hU : ∀ t, (2 : ℤ) ^ t ∣ (2 ^ e - 1) * digitPart g t + C := by
    intro t
    induction t using Nat.strong_induction_on with
    | _ t ih =>
      rcases lt_or_ge t e with hlt | hge
      · have e1 : (2 ^ e - 1) * digitPart g t + C =
            2 ^ e * digitPart g t + (digitPart g e - digitPart g t) := by
          rw [hC]
          ring
        rw [e1]
        exact dvd_add (dvd_mul_of_dvd_left (pow_dvd_pow 2 hlt.le) _)
          (dvd_digitPart_sub g hlt.le)
      · obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le hge
        have e1 : (2 ^ e - 1) * digitPart g (e + s) + C =
            2 ^ e * ((2 ^ e - 1) * digitPart g s + C) := by
          rw [hT]
          ring
        rw [e1, pow_add]
        exact mul_dvd_mul_left _ (ih s (by omega))
  have hP : 1 ≤ 2 ^ e := Nat.one_le_two_pow
  have hP2 : 2 ^ e % 2 = 0 := Nat.mod_eq_zero_of_dvd (dvd_pow_self 2 (by omega))
  have hb : (2 ^ e - 1) % 2 = 1 := by omega
  have hbz : ((2 ^ e - 1 : ℕ) : ℤ) = 2 ^ e - 1 := by
    push_cast [hP]
    ring
  set N := xiPart y p with hN
  refine ⟨((2 ^ e - 1) * N - 2 ^ p * C : ℤ) / ((2 ^ e - 1 : ℕ) : ℚ),
    ⟨(2 ^ e - 1) * N - 2 ^ p * C, 2 ^ e - 1, hb, rfl, ?_⟩, ?_⟩
  · intro k
    rw [hbz]
    rcases le_or_gt k p with hkp | hkp
    · have e1 : (2 ^ e - 1) * N - 2 ^ p * C - (2 ^ e - 1) * xiPart y k =
          (2 ^ e - 1) * (xiPart y p - xiPart y k) - 2 ^ p * C := by
        rw [hN]
        ring
      rw [e1]
      exact dvd_sub (dvd_mul_of_dvd_right (dvd_digitPart_sub _ hkp) _)
        (dvd_mul_of_dvd_left (pow_dvd_pow 2 hkp) _)
    · obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hkp.le
      have hS : xiPart y (p + t) = N + 2 ^ p * digitPart g t := by
        rw [hN, xiPart, digitPart_add]
        rfl
      have e1 : (2 ^ e - 1) * N - 2 ^ p * C - (2 ^ e - 1) * xiPart y (p + t) =
          -(2 ^ p * ((2 ^ e - 1) * digitPart g t + C)) := by
        rw [hS]
        ring
      rw [e1, pow_add]
      exact (mul_dvd_mul_left _ (hU t)).neg_right
  · have hd := Rat.den_dvd ((2 ^ e - 1) * N - 2 ^ p * C) ((2 ^ e - 1 : ℕ) : ℤ)
    rw [Rat.divInt_eq_div] at hd
    push_cast at hd ⊢
    exact_mod_cast hd

/-! ### Polynomials -/

/-- y is a polynomial in q. -/
def IsQPoly (y : QSeries) : Prop := ∃ f : Polynomial (ZMod 2), (f : QSeries) = y

theorem isQPoly_add {y z : QSeries} (hy : IsQPoly y) (hz : IsQPoly z) : IsQPoly (y + z) := by
  obtain ⟨f, rfl⟩ := hy
  obtain ⟨g, rfl⟩ := hz
  exact ⟨f + g, Polynomial.coe_add f g⟩

theorem isQPoly_mul {y z : QSeries} (hy : IsQPoly y) (hz : IsQPoly z) : IsQPoly (y * z) := by
  obtain ⟨f, rfl⟩ := hy
  obtain ⟨g, rfl⟩ := hz
  exact ⟨f * g, Polynomial.coe_mul f g⟩

theorem isQPoly_zero : IsQPoly 0 := ⟨0, Polynomial.coe_zero⟩

theorem isQPoly_one : IsQPoly 1 := ⟨1, Polynomial.coe_one⟩

theorem isQPoly_X : IsQPoly X := ⟨Polynomial.X, Polynomial.coe_X⟩

theorem isQPoly_pow {y : QSeries} (hy : IsQPoly y) (n : ℕ) : IsQPoly (y ^ n) := by
  obtain ⟨f, rfl⟩ := hy
  exact ⟨f ^ n, Polynomial.coe_pow n⟩

theorem isQPoly_foldl_qRhoAcc {A : QSeries} (hA : IsQPoly A) :
    ∀ (s : List Bool) (acc : QSeries × ℕ), IsQPoly acc.1 →
      IsQPoly (s.foldl (qRhoAcc A) acc).1
  | [], _, h => h
  | b :: s, acc, h => by
    rw [List.foldl_cons]
    refine isQPoly_foldl_qRhoAcc hA s _ ?_
    unfold qRhoAcc
    cases b
    · exact h
    · exact isQPoly_add (isQPoly_mul hA h) (isQPoly_pow isQPoly_X _)

theorem isQPoly_qRho {A : QSeries} (hA : IsQPoly A) (s : List Bool) : IsQPoly (qRho A s) :=
  isQPoly_foldl_qRhoAcc hA s (0, 0) isQPoly_zero

/-- y (1 + q^E) a polynomial: the digits of y repeat with period E past its degree. -/
theorem isEvPeriodic_of_mul {y : QSeries} {E : ℕ} {f : Polynomial (ZMod 2)}
    (h : y * (1 + X ^ E) = (f : QSeries)) : IsEvPeriodic y (f.natDegree + 1) E := by
  intro i hi
  have hc := congrArg (coeff (i + E)) h
  rw [mul_add, mul_one, map_add, coeff_mul_X_pow, Polynomial.coeff_coe,
    Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)] at hc
  exact (by decide : ∀ a b : ZMod 2, a + b = 0 → a = b) _ _ hc

/-! ### Monks' T_q: A = 1 + q, B = 1 -/

/-- In characteristic 2: (1 + y)^(2^c) = 1 + y^(2^c). -/
theorem one_add_pow_two_pow (y : QSeries) (c : ℕ) : (1 + y) ^ 2 ^ c = 1 + y ^ 2 ^ c := by
  induction c with
  | zero => simp
  | succ c ih =>
    rw [pow_succ, pow_mul, ih]
    linear_combination (y ^ 2 ^ c) * two_eq_zero_qSeries

/-- (1 + q)^k (1 + q + q^2) divides 1 + q^(3 2^c) once k ≤ 2^c. -/
theorem one_add_X_pow_eq_mul {k c : ℕ} (hk : k ≤ 2 ^ c) :
    (1 : QSeries) + X ^ (3 * 2 ^ c) = (1 + X) ^ k * (1 + X + X ^ 2) *
      ((1 + X) ^ (2 ^ c - k) * (1 + X + X ^ 2) ^ (2 ^ c - 1)) := by
  have h3 : (1 + X ^ 3 : QSeries) = (1 + X) * (1 + X + X ^ 2) := by
    linear_combination (-(X + X ^ 2 : QSeries)) * two_eq_zero_qSeries
  have h1 : 1 ≤ 2 ^ c := Nat.one_le_two_pow
  have e1 : (1 + X : QSeries) ^ k * (1 + X + X ^ 2) *
      ((1 + X) ^ (2 ^ c - k) * (1 + X + X ^ 2) ^ (2 ^ c - 1)) =
      (1 + X : QSeries) ^ (k + (2 ^ c - k)) * (1 + X + X ^ 2) ^ (1 + (2 ^ c - 1)) := by
    rw [pow_add, pow_add, pow_one]
    ring
  rw [e1, Nat.add_sub_cancel' hk, Nat.add_sub_cancel' h1, ← mul_pow, ← h3,
    one_add_pow_two_pow, ← pow_mul, mul_comm 3]

variable {h : ℕ → QSeries}

theorem constantCoeff_one_add_X : constantCoeff (1 + X : QSeries) = 1 := by
  simp

/-- h(1) (1 + q + q^2) = 1, from 1 → 2 → 1. -/
theorem monksQ_one (hc : MonksConj (1 + X) 1 h) : h 1 * (1 + X + X ^ 2) = 1 := by
  have h1 : constantCoeff (h 1) ≠ 0 := by
    rw [hc.parity]
    decide
  have hs := X_mul_monksT constantCoeff_one_add_X (map_one _) (h 1)
  simp only [h1, ↓reduceIte] at hs
  rw [← hc.step, show tStep 1 = 2 * 1 by decide, monksConj_two_mul hc] at hs
  linear_combination hs + (h 1 * X + h 1) * two_eq_zero_qSeries

/-- The drop chain n → T^L(n) → ... → 1, read by the drops, has k odd steps in all. -/
inductive DropOdd : ℕ → ℕ → Prop
  | one : DropOdd 1 0
  | drop {n L k : ℕ} : 1 < n → IsTDrop n L → DropOdd (tStep^[L] n) k →
      DropOdd n (k + order (tBits n L))

/-- When every m with 1 < m ≤ n drops, the drop chain of n has a count. -/
theorem exists_dropOdd :
    ∀ n, 1 ≤ n → (∀ m, 1 < m → m ≤ n → ∃ L, IsTDrop m L) → ∃ k, DropOdd n k := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn H
    rcases Nat.eq_or_lt_of_le hn with h1 | h1
    · subst h1
      exact ⟨0, DropOdd.one⟩
    · obtain ⟨L, hL⟩ := H n h1 le_rfl
      have hn1 : n ≠ 1 := by omega
      have hlt : tStep^[L] n < n := by
        have := hL
        simp only [IsTDrop, hn1, ↓reduceIte] at this
        exact this.2.1
      obtain ⟨k, hk⟩ := ih _ hlt (tStep_iterate_pos L n (by omega))
        fun m hm1 hm => H m hm1 (by omega)
      exact ⟨_, DropOdd.drop h1 hL hk⟩

/-- k odd steps over the drop chain: h(n) (1 + q)^k (1 + q + q^2) is a polynomial. -/
theorem monksQ_den_of_dropOdd (hc : MonksConj (1 + X) 1 h) {n k : ℕ} (hk : DropOdd n k) :
    IsQPoly (h n * ((1 + X) ^ k * (1 + X + X ^ 2))) := by
  have hA : IsQPoly (1 + X) := isQPoly_add isQPoly_one isQPoly_X
  induction hk with
  | one =>
    rw [pow_zero, one_mul, monksQ_one hc]
    exact isQPoly_one
  | @drop n L k h1 hL _ ih =>
    obtain ⟨_, hD⟩ := monksConj_drop hc constantCoeff_one_add_X (map_one _) h1 hL
    have e1 : h n * ((1 + X) ^ (k + order (tBits n L)) * (1 + X + X ^ 2)) =
        X ^ L * (h (tStep^[L] n) * ((1 + X) ^ k * (1 + X + X ^ 2))) +
          qRho (1 + X) (tBits n L) * ((1 + X) ^ k * (1 + X + X ^ 2)) := by
      rw [pow_add]
      linear_combination ((1 + X) ^ k * (1 + X + X ^ 2)) * hD
    rw [e1]
    have hDen : IsQPoly ((1 + X) ^ k * (1 + X + X ^ 2)) :=
      isQPoly_mul (isQPoly_pow hA k) (isQPoly_add hA (isQPoly_pow isQPoly_X 2))
    exact isQPoly_add (isQPoly_mul (isQPoly_pow isQPoly_X L) ih)
      (isQPoly_mul (isQPoly_qRho hA _) hDen)

/-- Read by the drops: h(n) (1 + q)^k (1 + q + q^2) is a polynomial for some k. -/
theorem monksQ_den (hc : MonksConj (1 + X) 1 h) :
    ∀ n, 1 ≤ n → (∀ m, 1 < m → m ≤ n → ∃ L, IsTDrop m L) →
      ∃ k, IsQPoly (h n * ((1 + X) ^ k * (1 + X + X ^ 2))) := by
  intro n hn H
  obtain ⟨k, hk⟩ := exists_dropOdd n hn H
  exact ⟨k, monksQ_den_of_dropOdd hc hk⟩

/-- A401593 with c named: k odd steps over the drop chain and k ≤ 2^c give a denominator
  of xi(h(n)) dividing 2^(3 2^c) - 1. -/
theorem monksQ_isXi_of_dropOdd (hc : MonksConj (1 + X) 1 h) {n k c : ℕ} (hk : DropOdd n k)
    (hkc : k ≤ 2 ^ c) : ∃ r : ℚ, IsXi (h n) r ∧ r.den ∣ 2 ^ (3 * 2 ^ c) - 1 := by
  obtain ⟨f, hf⟩ := monksQ_den_of_dropOdd hc hk
  have hA : IsQPoly (1 + X) := isQPoly_add isQPoly_one isQPoly_X
  obtain ⟨g, hg⟩ := isQPoly_mul (isQPoly_pow hA (2 ^ c - k))
    (isQPoly_pow (isQPoly_add hA (isQPoly_pow isQPoly_X 2)) (2 ^ c - 1))
  have hm : h n * (1 + X ^ (3 * 2 ^ c)) = ((f * g : Polynomial (ZMod 2)) : QSeries) := by
    rw [one_add_X_pow_eq_mul hkc, Polynomial.coe_mul, hf, hg]
    ring
  have hE : 1 ≤ 3 * 2 ^ c := by
    have := Nat.one_le_two_pow (n := c)
    omega
  exact isXi_of_periodic hE (isEvPeriodic_of_mul hm)

/-- A401593: read by the drops, xi(h(n)) has a denominator dividing 2^(3 2^c) - 1. -/
theorem monksQ_isXi (hc : MonksConj (1 + X) 1 h) {n : ℕ} (hn : 1 ≤ n)
    (H : ∀ m, 1 < m → m ≤ n → ∃ L, IsTDrop m L) :
    ∃ c, ∃ r : ℚ, IsXi (h n) r ∧ r.den ∣ 2 ^ (3 * 2 ^ c) - 1 := by
  obtain ⟨k, hk⟩ := exists_dropOdd n hn H
  exact ⟨k, monksQ_isXi_of_dropOdd hc hk Nat.lt_two_pow_self.le⟩

/-- A401592: xi(h(2n)) = 2 xi(h(n)), with the numerator doubled and the denominator kept. -/
theorem monksQ_isXi_two_mul {A B : QSeries} (hc : MonksConj A B h) {n : ℕ} {r : ℚ}
    (hr : IsXi (h n) r) :
    IsXi (h (2 * n)) (2 * r) ∧ (2 * r).num = 2 * r.num ∧ (2 * r).den = r.den := by
  rw [monksConj_two_mul hc]
  exact ⟨isXi_X_mul hr, num_den_two_mul_of_isXi hr⟩

end

end AcceleratedCollatz
