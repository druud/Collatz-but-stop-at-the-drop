-- SPDX-License-Identifier: MIT
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.PowerSeries.Basic

/-!
  K. G. Monks' q-analogs of T (JIS 28, 25.6.8; paper 3 sec:staircases). On F_2[[q]], for A
  and B with constant term 1, `monksT A B x` is x/q for even x (constant term 0) and
  (A x + B)/q for odd x; Monks' T_q is `monksT (1 + X) 1`. After L steps,
  q^L T^L(x) = A^n x + B rho_A, with n the odd steps among them and rho_A the sum of
  A^(n-o) q^(k_o) over the o-th odd step at k_o: paper 2's rho with 2 -> q, 3 -> A, and no
  signs in characteristic 2 (`X_pow_mul_monksT_iterate`). For A = 1 the map is the shift
  conjugated by B: T_{1,B}(B y) = B sigma(y) (`monksT_one_mul`).
-/

namespace AcceleratedCollatz

open PowerSeries

noncomputable section

/-- The power series over F_2, in q = `X`. -/
abbrev QSeries := PowerSeries (ZMod 2)

/-- In F_2 a nonzero element is 1. -/
theorem zmod2_eq_one_of_ne {a : ZMod 2} (h : a ≠ 0) : a = 1 :=
  (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) a h

/-- x without its constant term, divided by q. -/
def monksShift (x : QSeries) : QSeries := PowerSeries.mk fun n => coeff (n + 1) x

theorem monksShift_X_mul (z : QSeries) : monksShift (X * z) = z := by
  refine PowerSeries.ext fun n => ?_
  rw [monksShift, coeff_mk, coeff_succ_X_mul]

theorem X_mul_monksShift {x : QSeries} (h : constantCoeff x = 0) : X * monksShift x = x := by
  refine PowerSeries.ext fun n => ?_
  cases n with
  | zero => rw [coeff_zero_X_mul, coeff_zero_eq_constantCoeff_apply, h]
  | succ n => rw [coeff_succ_X_mul, monksShift, coeff_mk]

theorem monksShift_mul_of (B : QSeries) {y : QSeries} (h : constantCoeff y = 0) :
    monksShift (B * y) = B * monksShift y := by
  conv_lhs => rw [← X_mul_monksShift h]
  rw [mul_left_comm, monksShift_X_mul]

/-- Monks' map T_{A,B}: x/q for even x, (A x + B)/q for odd x. -/
def monksT (A B x : QSeries) : QSeries :=
  if constantCoeff x = 0 then monksShift x else monksShift (A * x + B)

/-- One step, times q: x for even x, A x + B for odd x. -/
theorem X_mul_monksT {A B : QSeries} (hA : constantCoeff A = 1) (hB : constantCoeff B = 1)
    (x : QSeries) :
    X * monksT A B x = if constantCoeff x = 0 then x else A * x + B := by
  unfold monksT
  split_ifs with h
  · exact X_mul_monksShift h
  · apply X_mul_monksShift
    rw [map_add, map_mul, hA, hB, one_mul, zmod2_eq_one_of_ne h]
    decide

/-- The odd steps among the first L steps of x. -/
def monksOdd (A B x : QSeries) : ℕ → ℕ
  | 0 => 0
  | L + 1 => monksOdd A B x L + if constantCoeff ((monksT A B)^[L] x) = 0 then 0 else 1

/-- rho_A of the first L steps of x: the sum of A^(n-o) q^(k_o) over the o-th odd step at
  k_o, n the odd steps. -/
def monksRho (A B x : QSeries) : ℕ → QSeries
  | 0 => 0
  | L + 1 =>
    if constantCoeff ((monksT A B)^[L] x) = 0 then monksRho A B x L
    else A * monksRho A B x L + X ^ L

/-- After L steps: q^L T^L(x) = A^n x + B rho_A. -/
theorem X_pow_mul_monksT_iterate {A B : QSeries} (hA : constantCoeff A = 1)
    (hB : constantCoeff B = 1) (x : QSeries) (L : ℕ) :
    X ^ L * (monksT A B)^[L] x = A ^ monksOdd A B x L * x + B * monksRho A B x L := by
  induction L with
  | zero => simp [monksOdd, monksRho]
  | succ L ih =>
    rw [Function.iterate_succ_apply', pow_succ, mul_assoc, X_mul_monksT hA hB]
    simp only [monksOdd, monksRho]
    split_ifs with h
    · rw [ih, add_zero]
    · calc X ^ L * (A * (monksT A B)^[L] x + B)
          = A * (X ^ L * (monksT A B)^[L] x) + B * X ^ L := by ring
        _ = A ^ (monksOdd A B x L + 1) * x + B * (A * monksRho A B x L + X ^ L) := by
          rw [ih]; ring

/-- The shift sigma: y/q for even y, (y + 1)/q for odd y. -/
def monksSigma (y : QSeries) : QSeries :=
  if constantCoeff y = 0 then monksShift y else monksShift (y + 1)

/-- For A = 1 Monks' map is the shift conjugated by B: T_{1,B}(B y) = B sigma(y). -/
theorem monksT_one_mul {B : QSeries} (hB : constantCoeff B = 1) (y : QSeries) :
    monksT 1 B (B * y) = B * monksSigma y := by
  have h0 : constantCoeff (B * y) = constantCoeff y := by rw [map_mul, hB, one_mul]
  unfold monksT monksSigma
  rw [h0]
  split_ifs with h
  · exact monksShift_mul_of B h
  · rw [one_mul, show B * y + B = B * (y + 1) by ring]
    apply monksShift_mul_of
    rw [map_add, map_one, zmod2_eq_one_of_ne h]
    decide

end

end AcceleratedCollatz
