-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TMonksQ
import AcceleratedCollatz.TNest
import AcceleratedCollatz.TTerras
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors

/-!
  A parity-preserving conjugacy h from T to Monks' map T_{A,B} (`MonksConj`; Monks proves
  one exists, here it is a hypothesis), read up to the drop (OEIS A401592, A401593 for
  Monks' T_q). The steps of h(n) are those of n (`monksT_iterate_conj`), so after L steps
  q^L h(T^L(n)) = A^o h(n) + B rho_A(w), w the first L parity bits of n, o its odd steps and
  rho_A paper 2's rho with 2 -> q, 3 -> A (`X_pow_mul_conj_iterate`). At the drop of n this
  fixes h(n) from h of the smaller number T^L(n) (`monksConj_eq_of_prefix`,
  `monksConj_drop`). An even step is a shift: h(2n) = q h(n) (`monksConj_two_mul`), which
  read as 2-adic numbers is a(2n) = 2 a(n) of A401592.
-/

namespace AcceleratedCollatz

open PowerSeries

noncomputable section

/-- h maps T to T_{A,B} and keeps the parity. -/
structure MonksConj (A B : QSeries) (h : ℕ → QSeries) : Prop where
  parity : ∀ n, constantCoeff (h n) = if n % 2 = 1 then 1 else 0
  step : ∀ n, h (tStep n) = monksT A B (h n)

/-- rho_A of a word, from the front: A rho + q^k for an odd step at k, rho for an even one. -/
def qRhoAcc (A : QSeries) (acc : QSeries × ℕ) (b : Bool) : QSeries × ℕ :=
  (if b then A * acc.1 + X ^ acc.2 else acc.1, acc.2 + 1)

/-- rho_A of a word: paper 2's rho with 2 -> q, 3 -> A. -/
def qRho (A : QSeries) (s : List Bool) : QSeries :=
  (s.foldl (qRhoAcc A) (0, 0)).1

theorem qRho_snd (A : QSeries) (s : List Bool) : (s.foldl (qRhoAcc A) (0, 0)).2 = s.length := by
  induction s using List.reverseRecOn with
  | nil => rfl
  | append_singleton s b ih =>
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil, qRhoAcc, ih, List.length_append,
      List.length_singleton]

theorem qRho_append_single (A : QSeries) (s : List Bool) (b : Bool) :
    qRho A (s ++ [b]) = if b then A * qRho A s + X ^ s.length else qRho A s := by
  rw [qRho, List.foldl_append, List.foldl_cons, List.foldl_nil, qRhoAcc, qRho_snd]
  rfl

variable {A B : QSeries} {h : ℕ → QSeries}

/-- The steps of h(n) are those of n. -/
theorem monksT_iterate_conj (hc : MonksConj A B h) (n L : ℕ) :
    (monksT A B)^[L] (h n) = h (tStep^[L] n) := by
  induction L with
  | zero => rfl
  | succ L ih =>
    rw [Function.iterate_succ_apply', ih, ← hc.step, Function.iterate_succ_apply']

theorem constantCoeff_conj_iterate (hc : MonksConj A B h) (n L : ℕ) :
    constantCoeff ((monksT A B)^[L] (h n)) = 0 ↔ ¬ tStep^[L] n % 2 = 1 := by
  rw [monksT_iterate_conj hc, hc.parity]
  split_ifs with h1
  · simp [h1]
  · simp [h1]

/-- The odd steps of h(n) are those of n. -/
theorem monksOdd_conj (hc : MonksConj A B h) (n L : ℕ) :
    monksOdd A B (h n) L = order (tBits n L) := by
  induction L with
  | zero => simp [monksOdd, tBits, order]
  | succ L ih =>
    rw [monksOdd, ih, order_tBits_succ]
    by_cases h1 : tStep^[L] n % 2 = 1
    · have h0 : ¬ constantCoeff ((monksT A B)^[L] (h n)) = 0 := by
        rw [constantCoeff_conj_iterate hc]
        exact not_not.mpr h1
      simp [h0, h1]
    · have h0 : constantCoeff ((monksT A B)^[L] (h n)) = 0 :=
        (constantCoeff_conj_iterate hc n L).mpr h1
      simp [h0, h1]

/-- rho_A of h(n) is rho_A of the parity bits of n. -/
theorem monksRho_conj (hc : MonksConj A B h) (n L : ℕ) :
    monksRho A B (h n) L = qRho A (tBits n L) := by
  induction L with
  | zero => simp [monksRho, tBits, qRho]
  | succ L ih =>
    have hb : tBits n (L + 1) = tBits n L ++ [decide (tStep^[L] n % 2 = 1)] := by
      rw [tBits_add]
      simp [tBits]
    rw [monksRho, ih, hb, qRho_append_single, length_tBits]
    by_cases h1 : tStep^[L] n % 2 = 1
    · have h0 : ¬ constantCoeff ((monksT A B)^[L] (h n)) = 0 := by
        rw [constantCoeff_conj_iterate hc]
        exact not_not.mpr h1
      simp [h0, h1]
    · have h0 : constantCoeff ((monksT A B)^[L] (h n)) = 0 :=
        (constantCoeff_conj_iterate hc n L).mpr h1
      simp [h0, h1]

/-- After L steps: q^L h(T^L(n)) = A^o h(n) + B rho_A(w), w the first L bits of n. -/
theorem X_pow_mul_conj_iterate (hc : MonksConj A B h) (hA : constantCoeff A = 1)
    (hB : constantCoeff B = 1) (n L : ℕ) :
    X ^ L * h (tStep^[L] n) =
      A ^ order (tBits n L) * h n + B * qRho A (tBits n L) := by
  rw [← monksT_iterate_conj hc, X_pow_mul_monksT_iterate hA hB, monksOdd_conj hc,
    monksRho_conj hc]

theorem two_eq_zero_qSeries : (2 : QSeries) = 0 := by
  rw [← map_ofNat (C (R := ZMod 2)) 2]
  rw [show (OfNat.ofNat 2 : ZMod 2) = 0 by decide, map_zero]

/-- h(n) is the one y with A^o y = q^L h(T^L(n)) + B rho_A(w). -/
theorem monksConj_eq_of_prefix (hc : MonksConj A B h) (hA : constantCoeff A = 1)
    (hB : constantCoeff B = 1) (n L : ℕ) (y : QSeries)
    (hy : A ^ order (tBits n L) * y = X ^ L * h (tStep^[L] n) + B * qRho A (tBits n L)) :
    y = h n := by
  have e := X_pow_mul_conj_iterate hc hA hB n L
  have hA0 : A ^ order (tBits n L) ≠ 0 := by
    apply pow_ne_zero
    intro h0
    rw [h0, map_zero] at hA
    exact zero_ne_one hA
  apply mul_left_cancel₀ hA0
  linear_combination hy + e + (B * qRho A (tBits n L)) * two_eq_zero_qSeries

/-- At the drop: T^L(n) < n and A^o h(n) = q^L h(T^L(n)) + B rho_A(w). -/
theorem monksConj_drop (hc : MonksConj A B h) (hA : constantCoeff A = 1)
    (hB : constantCoeff B = 1) {n L : ℕ} (hn : 1 < n) (hD : IsTDrop n L) :
    tStep^[L] n < n ∧
      A ^ order (tBits n L) * h n = X ^ L * h (tStep^[L] n) + B * qRho A (tBits n L) := by
  have hn1 : n ≠ 1 := by omega
  simp only [IsTDrop, hn1, ↓reduceIte] at hD
  refine ⟨hD.2.1, ?_⟩
  linear_combination (X_pow_mul_conj_iterate hc hA hB n L).symm -
    (B * qRho A (tBits n L)) * two_eq_zero_qSeries

/-- An even step is a shift: h(2n) = q h(n). -/
theorem monksConj_two_mul (hc : MonksConj A B h) (n : ℕ) : h (2 * n) = X * h n := by
  have h0 : constantCoeff (h (2 * n)) = 0 := by
    rw [hc.parity]
    simp
  have hs := hc.step (2 * n)
  rw [tStep_even _ (by omega), Nat.mul_div_cancel_left n (by norm_num)] at hs
  simp only [monksT, h0, ↓reduceIte] at hs
  rw [hs, X_mul_monksShift h0]

end

end AcceleratedCollatz
