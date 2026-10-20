-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TSternBrocotQ
import Mathlib.Algebra.ContinuedFractions.Computation.Translations
import Mathlib.Algebra.ContinuedFractions.ContinuantsRecurrence
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.NumberTheory.Real.Irrational

/-!
  The Stern–Brocot walk towards log2 q (odd q ≥ 3) and the continued fraction of log2 q.
  log2 q is irrational (`irrational_log2Q`); its complete quotients (`cqQ`) and partial
  quotients a(j) (`cfQuotQ`, all ≥ 1) are those of Mathlib's `GenContFract.of`
  (`stream_log2Q`, `of_log2Q_h`, `of_log2Q_s`), and the continuants, two places ahead
  (`cfNumQ`, `cfDenQ`: 0/1, 1/0, then Q(j + 2) = a(j) Q(j + 1) + Q(j)), are its
  numerators and denominators (`of_log2Q_nums`, `of_log2Q_dens`): Q(j + 2) is the j-th
  convergent. The walk runs through the quotients: after a(0) + ... + a(j - 1) + t steps,
  t ≤ a(j), it holds Q(j + 1) and Q(j) + t Q(j + 1) (`sbWalkQ_cfStartQ_add`), the second
  one below log2 q for even j and above it for odd j (`cfNodeQ`). The fractions
  Q(j) + t Q(j + 1) with 1 ≤ t ≤ a(j) are the semiconvergents (`IsSemiconvQ`; t = a(j) gives
  the convergent Q(j + 2)). So the fractions above log2 q on the walk are exactly the
  semiconvergents with odd j, those below it after the first step exactly the ones with
  even j (`sbWalkQ_hi_iff`, `sbWalkQ_lo_iff`), and the upper and lower record Orders
  n ≥ 1 are exactly their denominators (`upperRecordQ_iff_semiconvQ`,
  `lowerRecordQ_iff_semiconvQ`).
-/

namespace AcceleratedCollatz

variable {q : ℕ}

/-- log2 q. -/
noncomputable def log2Q (q : ℕ) : ℝ := Real.logb 2 q

theorem mul_log2Q (q n : ℕ) : (n : ℝ) * log2Q q = Real.logb 2 ((q ^ n : ℕ) : ℝ) := by
  rw [log2Q, Nat.cast_pow, Real.logb_pow]

/-- q^n < 2^p exactly when n log2 q < p. -/
theorem pow_lt_iff_mul_log2Q_lt (hq : 1 ≤ q) (n p : ℕ) :
    q ^ n < 2 ^ p ↔ (n : ℝ) * log2Q q < p := by
  have hx : (0 : ℝ) < ((q ^ n : ℕ) : ℝ) := by
    exact_mod_cast Nat.pow_pos (by omega)
  rw [mul_log2Q, Real.logb_lt_iff_lt_rpow (by norm_num) hx, Real.rpow_natCast]
  norm_cast

/-- 2^p < q^n exactly when p < n log2 q. -/
theorem pow_lt_iff_lt_mul_log2Q (hq : 1 ≤ q) (n p : ℕ) :
    2 ^ p < q ^ n ↔ (p : ℝ) < n * log2Q q := by
  have hx : (0 : ℝ) < ((q ^ n : ℕ) : ℝ) := by
    exact_mod_cast Nat.pow_pos (by omega)
  rw [mul_log2Q, Real.lt_logb_iff_rpow_lt (by norm_num) hx, Real.rpow_natCast]
  norm_cast

theorem one_lt_log2Q (hq : 3 ≤ q) : 1 < log2Q q := by
  have h0 : 2 ^ 1 < q ^ 1 := by
    rw [pow_one, pow_one]
    omega
  have h := (pow_lt_iff_lt_mul_log2Q (q := q) (by omega) 1 1).mp h0
  simpa using h

/-- n log2 q is no natural number for n ≥ 1. -/
theorem mul_log2Q_ne (hodd : Odd q) (hq : 3 ≤ q) {n : ℕ} (hn : 1 ≤ n) (p : ℕ) :
    (n : ℝ) * log2Q q ≠ p := by
  intro h
  have h1 : ¬q ^ n < 2 ^ p := by
    intro hc
    have := (pow_lt_iff_mul_log2Q_lt (by omega) n p).mp hc
    linarith
  have h2 : ¬2 ^ p < q ^ n := by
    intro hc
    have := (pow_lt_iff_lt_mul_log2Q (by omega) n p).mp hc
    linarith
  have he : q ^ n = 2 ^ p := by
    omega
  have hqn : q ≤ q ^ n := Nat.le_self_pow (by omega) q
  cases p with
  | zero =>
    rw [pow_zero] at he
    omega
  | succ p =>
    have hev : Even (q ^ n) := by
      rw [he]
      exact (Nat.even_pow.mpr ⟨even_two, by omega⟩)
    exact (Nat.not_even_iff_odd.mpr (hodd.pow)) hev

/-- log2 q is irrational. -/
theorem irrational_log2Q (hodd : Odd q) (hq : 3 ≤ q) : Irrational (log2Q q) := by
  rintro ⟨r, hr⟩
  have hpos : (0 : ℝ) < r := by
    rw [hr]
    linarith [one_lt_log2Q hq]
  have hnum : 0 < r.num := Rat.num_pos.mpr (by exact_mod_cast hpos)
  have hden : (r.den : ℝ) ≠ 0 := by
    exact_mod_cast r.den_nz
  have hcast : (r : ℝ) = (r.num : ℝ) / r.den := by
    exact_mod_cast (Rat.num_div_den r).symm
  have hnat : ((r.num.toNat : ℕ) : ℝ) = (r.num : ℝ) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hnum.le]
  have h1 : (r.den : ℝ) * log2Q q = ((r.num.toNat : ℕ) : ℝ) := by
    rw [hnat, ← hr, hcast, mul_div_cancel₀ _ hden]
  exact mul_log2Q_ne hodd hq (Nat.one_le_iff_ne_zero.mpr r.den_nz) _ h1

/-- The complete quotients of log2 q: log2 q, then the inverse of the fractional part. -/
noncomputable def cqQ (q : ℕ) : ℕ → ℝ
  | 0 => log2Q q
  | j + 1 => (Int.fract (cqQ q j))⁻¹

theorem cqQ_zero (q : ℕ) : cqQ q 0 = log2Q q := rfl

theorem cqQ_succ (q j : ℕ) : cqQ q (j + 1) = (Int.fract (cqQ q j))⁻¹ := rfl

theorem irrational_cqQ (hodd : Odd q) (hq : 3 ≤ q) (j : ℕ) : Irrational (cqQ q j) := by
  induction j with
  | zero =>
    exact irrational_log2Q hodd hq
  | succ j ih =>
    rw [cqQ_succ, irrational_inv_iff, ← Int.self_sub_floor]
    exact ih.sub_intCast _

theorem fract_cqQ_pos (hodd : Odd q) (hq : 3 ≤ q) (j : ℕ) : 0 < Int.fract (cqQ q j) := by
  have h := (irrational_cqQ hodd hq j).sub_intCast ⌊cqQ q j⌋
  rw [Int.self_sub_floor] at h
  exact lt_of_le_of_ne (Int.fract_nonneg _) (Ne.symm h.ne_zero)

theorem one_lt_cqQ (hodd : Odd q) (hq : 3 ≤ q) (j : ℕ) : 1 < cqQ q j := by
  cases j with
  | zero =>
    exact one_lt_log2Q hq
  | succ j =>
    rw [cqQ_succ]
    exact (one_lt_inv₀ (fract_cqQ_pos hodd hq j)).mpr (Int.fract_lt_one _)

theorem floor_cqQ_lt (hodd : Odd q) (hq : 3 ≤ q) (j : ℕ) : (⌊cqQ q j⌋ : ℝ) < cqQ q j :=
  lt_of_le_of_ne (Int.floor_le _) (Ne.symm ((irrational_cqQ hodd hq j).ne_int _))

/-- The partial quotients of log2 q. -/
noncomputable def cfQuotQ (q j : ℕ) : ℕ := ⌊cqQ q j⌋.toNat

theorem cfQuotQ_cast (hodd : Odd q) (hq : 3 ≤ q) (j : ℕ) :
    (cfQuotQ q j : ℝ) = (⌊cqQ q j⌋ : ℝ) := by
  have h0 : 0 ≤ ⌊cqQ q j⌋ := Int.floor_nonneg.mpr (by linarith [one_lt_cqQ hodd hq j])
  rw [cfQuotQ, ← Int.cast_natCast, Int.toNat_of_nonneg h0]

/-- Every partial quotient of log2 q is at least 1. -/
theorem one_le_cfQuotQ (hodd : Odd q) (hq : 3 ≤ q) (j : ℕ) : 1 ≤ cfQuotQ q j := by
  have h1 : (1 : ℤ) ≤ ⌊cqQ q j⌋ := Int.le_floor.mpr (by
    push_cast
    linarith [one_lt_cqQ hodd hq j])
  have h2 : (1 : ℝ) ≤ (cfQuotQ q j : ℝ) := by
    rw [cfQuotQ_cast hodd hq]
    exact_mod_cast h1
  exact_mod_cast h2

/-- A partial quotient lies below its complete quotient. -/
theorem cfQuotQ_lt_cqQ (hodd : Odd q) (hq : 3 ≤ q) (j : ℕ) : (cfQuotQ q j : ℝ) < cqQ q j := by
  rw [cfQuotQ_cast hodd hq]
  exact floor_cqQ_lt hodd hq j

/-- y(j) y(j + 1) = a(j) y(j + 1) + 1. -/
theorem cqQ_mul_succ (hodd : Odd q) (hq : 3 ≤ q) (j : ℕ) :
    cqQ q j * cqQ q (j + 1) = cfQuotQ q j * cqQ q (j + 1) + 1 := by
  have hf : Int.fract (cqQ q j) ≠ 0 := (fract_cqQ_pos hodd hq j).ne'
  have hy : cqQ q j = (⌊cqQ q j⌋ : ℝ) + Int.fract (cqQ q j) := (Int.floor_add_fract _).symm
  rw [cqQ_succ, cfQuotQ_cast hodd hq]
  nth_rewrite 1 [hy]
  rw [add_mul, mul_inv_cancel₀ hf]

/-- Numerators of the continuants, two places ahead: 0, 1, then
    a(j) times the last plus the one before. -/
noncomputable def cfNumQ (q : ℕ) : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | j + 2 => cfQuotQ q j * cfNumQ q (j + 1) + cfNumQ q j

/-- Denominators of the continuants, two places ahead: 1, 0, then
    a(j) times the last plus the one before. -/
noncomputable def cfDenQ (q : ℕ) : ℕ → ℕ
  | 0 => 1
  | 1 => 0
  | j + 2 => cfQuotQ q j * cfDenQ q (j + 1) + cfDenQ q j

theorem cfNumQ_add_two (q j : ℕ) :
    cfNumQ q (j + 2) = cfQuotQ q j * cfNumQ q (j + 1) + cfNumQ q j := rfl

theorem cfDenQ_add_two (q j : ℕ) :
    cfDenQ q (j + 2) = cfQuotQ q j * cfDenQ q (j + 1) + cfDenQ q j := rfl

/-- Neighbouring continuants: N(j + 1) D(j) - N(j) D(j + 1) = (-1)^j. -/
theorem cfQ_det (q j : ℕ) :
    (cfNumQ q (j + 1) : ℤ) * cfDenQ q j - cfNumQ q j * cfDenQ q (j + 1) = (-1) ^ j := by
  induction j with
  | zero =>
    simp [cfNumQ, cfDenQ]
  | succ j ih =>
    rw [cfNumQ_add_two, cfDenQ_add_two, pow_succ]
    push_cast
    linear_combination (-1 : ℤ) * ih

/-- The denominators of two neighbouring continuants sum to at least 1. -/
theorem one_le_cfDenQ_add (q j : ℕ) : 1 ≤ cfDenQ q j + cfDenQ q (j + 1) := by
  induction j with
  | zero =>
    simp [cfDenQ]
  | succ j ih =>
    rw [cfDenQ_add_two]
    have h := Nat.zero_le (cfQuotQ q j * cfDenQ q (j + 1))
    omega

/-- log2 q from the continuants and the complete quotient y(j):
    log2 q (D(j + 1) y + D(j)) = N(j + 1) y + N(j). -/
theorem cfQ_exact (hodd : Odd q) (hq : 3 ≤ q) (j : ℕ) :
    log2Q q * ((cfDenQ q (j + 1) : ℝ) * cqQ q j + cfDenQ q j) =
      (cfNumQ q (j + 1) : ℝ) * cqQ q j + cfNumQ q j := by
  induction j with
  | zero =>
    simp [cfNumQ, cfDenQ, cqQ_zero]
  | succ j ih =>
    have hrel := cqQ_mul_succ hodd hq j
    rw [cfNumQ_add_two, cfDenQ_add_two]
    push_cast
    linear_combination (cqQ q (j + 1)) * ih +
      ((cfNumQ q (j + 1) : ℝ) - log2Q q * cfDenQ q (j + 1)) * hrel

theorem cfQ_den_pos (hodd : Odd q) (hq : 3 ≤ q) (j : ℕ) :
    0 < (cfDenQ q (j + 1) : ℝ) * cqQ q j + cfDenQ q j := by
  have hy := one_lt_cqQ hodd hq j
  have h := one_le_cfDenQ_add q j
  rcases Nat.eq_zero_or_pos (cfDenQ q (j + 1)) with h0 | h0
  · rw [h0] at h ⊢
    have : (1 : ℝ) ≤ cfDenQ q j := by exact_mod_cast (by omega : 1 ≤ cfDenQ q j)
    simp only [Nat.cast_zero, zero_mul, zero_add]
    linarith
  · have : (1 : ℝ) ≤ cfDenQ q (j + 1) := by exact_mod_cast h0
    have : (0 : ℝ) ≤ cfDenQ q j := Nat.cast_nonneg _
    nlinarith

/-- The side of Q(j) + s Q(j + 1) for s ≤ a(j): above log2 q exactly for odd j. -/
theorem cfQ_pow_lt_iff (hodd : Odd q) (hq : 3 ≤ q) {j s : ℕ} (hs : s ≤ cfQuotQ q j) :
    q ^ (cfDenQ q j + s * cfDenQ q (j + 1)) < 2 ^ (cfNumQ q j + s * cfNumQ q (j + 1)) ↔
      j % 2 = 1 := by
  have hE := cfQ_exact hodd hq j
  have hdet : ((cfNumQ q (j + 1) : ℝ) * cfDenQ q j - cfNumQ q j * cfDenQ q (j + 1)) =
      (-1) ^ j := by
    exact_mod_cast cfQ_det q j
  have hpos := cfQ_den_pos hodd hq j
  have hsy : (s : ℝ) < cqQ q j := by
    have : (s : ℝ) ≤ cfQuotQ q j := by exact_mod_cast hs
    linarith [cfQuotQ_lt_cqQ hodd hq j]
  have key : (log2Q q * ((cfDenQ q j : ℝ) + s * cfDenQ q (j + 1)) -
      ((cfNumQ q j : ℝ) + s * cfNumQ q (j + 1))) *
      ((cfDenQ q (j + 1) : ℝ) * cqQ q j + cfDenQ q j) = (-1) ^ j * (cqQ q j - s) := by
    linear_combination ((cfDenQ q j : ℝ) + s * cfDenQ q (j + 1)) * hE +
      (cqQ q j - s) * hdet
  rw [pow_lt_iff_mul_log2Q_lt (by omega)]
  push_cast
  rcases Nat.even_or_odd j with hj | hj
  · rw [hj.neg_one_pow, one_mul] at key
    have hj2 : j % 2 = 0 := Nat.even_iff.mp hj
    constructor
    · intro hlt
      have : 0 < (log2Q q * ((cfDenQ q j : ℝ) + s * cfDenQ q (j + 1)) -
          ((cfNumQ q j : ℝ) + s * cfNumQ q (j + 1))) := by
        by_contra hc
        push Not at hc
        nlinarith
      linarith
    · intro h
      omega
  · rw [hj.neg_one_pow] at key
    have hj2 : j % 2 = 1 := Nat.odd_iff.mp hj
    constructor
    · intro _
      exact hj2
    · intro _
      by_contra hc
      push Not at hc
      nlinarith

/-- The node of the walk in run j after t of its steps: Q(j + 1), and Q(j) + t Q(j + 1),
    below log2 q for even j and above it for odd j. -/
noncomputable def cfNodeQ (q j t : ℕ) : SBNode :=
  if j % 2 = 0 then
    ⟨cfNumQ q j + t * cfNumQ q (j + 1), cfDenQ q j + t * cfDenQ q (j + 1),
      cfNumQ q (j + 1), cfDenQ q (j + 1)⟩
  else
    ⟨cfNumQ q (j + 1), cfDenQ q (j + 1),
      cfNumQ q j + t * cfNumQ q (j + 1), cfDenQ q j + t * cfDenQ q (j + 1)⟩

/-- The number of steps before run j: a(0) + ... + a(j - 1). -/
noncomputable def cfStartQ (q : ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => cfStartQ q j + cfQuotQ q j

/-- A step inside run j. -/
theorem sbStepQ_cfNodeQ (hodd : Odd q) (hq : 3 ≤ q) {j t : ℕ} (ht : t < cfQuotQ q j) :
    sbStepQ q (cfNodeQ q j t) = cfNodeQ q j (t + 1) := by
  have h := cfQ_pow_lt_iff hodd hq (s := t + 1) (j := j) (by omega)
  have eD : cfDenQ q j + t * cfDenQ q (j + 1) + cfDenQ q (j + 1) =
      cfDenQ q j + (t + 1) * cfDenQ q (j + 1) := by
    ring
  have eN : cfNumQ q j + t * cfNumQ q (j + 1) + cfNumQ q (j + 1) =
      cfNumQ q j + (t + 1) * cfNumQ q (j + 1) := by
    ring
  by_cases hj : j % 2 = 0
  · simp only [cfNodeQ, hj, ↓reduceIte]
    have hlt : ¬q ^ (cfDenQ q j + t * cfDenQ q (j + 1) + cfDenQ q (j + 1)) <
        2 ^ (cfNumQ q j + t * cfNumQ q (j + 1) + cfNumQ q (j + 1)) := by
      rw [eD, eN, h]
      omega
    rw [sbStepQ_of_not_lt hlt, eD, eN]
  · simp only [cfNodeQ, hj, ↓reduceIte]
    have hlt : q ^ (cfDenQ q (j + 1) + (cfDenQ q j + t * cfDenQ q (j + 1))) <
        2 ^ (cfNumQ q (j + 1) + (cfNumQ q j + t * cfNumQ q (j + 1))) := by
      rw [Nat.add_comm (cfDenQ q (j + 1)), Nat.add_comm (cfNumQ q (j + 1)), eD, eN, h]
      omega
    rw [sbStepQ_of_lt hlt, Nat.add_comm (cfDenQ q (j + 1)), Nat.add_comm (cfNumQ q (j + 1)),
      eD, eN]

/-- The end of run j is the start of run j + 1. -/
theorem cfNodeQ_end (q j : ℕ) : cfNodeQ q j (cfQuotQ q j) = cfNodeQ q (j + 1) 0 := by
  have eN : cfNumQ q j + cfQuotQ q j * cfNumQ q (j + 1) = cfNumQ q (j + 2) := by
    rw [cfNumQ_add_two]
    ring
  have eD : cfDenQ q j + cfQuotQ q j * cfDenQ q (j + 1) = cfDenQ q (j + 2) := by
    rw [cfDenQ_add_two]
    ring
  by_cases hj : j % 2 = 0
  · have hj' : ¬(j + 1) % 2 = 0 := by
      omega
    simp only [cfNodeQ, hj, hj', ↓reduceIte, eN, eD, Nat.zero_mul, Nat.add_zero]
  · have hj' : (j + 1) % 2 = 0 := by
      omega
    simp only [cfNodeQ, hj, hj', ↓reduceIte, eN, eD, Nat.zero_mul, Nat.add_zero]

/-- Inside run j, from its start. -/
theorem sbWalkQ_cfStartQ_add_of (hodd : Odd q) (hq : 3 ≤ q) {j : ℕ}
    (h0 : sbWalkQ q (cfStartQ q j) = cfNodeQ q j 0) :
    ∀ t, t ≤ cfQuotQ q j → sbWalkQ q (cfStartQ q j + t) = cfNodeQ q j t := by
  intro t
  induction t with
  | zero =>
    intro _
    rw [Nat.add_zero]
    exact h0
  | succ t ih =>
    intro ht
    rw [← Nat.add_assoc, sbWalkQ_succ, ih (by omega)]
    exact sbStepQ_cfNodeQ hodd hq (by omega)

/-- The walk at the start of run j. -/
theorem sbWalkQ_cfStartQ (hodd : Odd q) (hq : 3 ≤ q) (j : ℕ) :
    sbWalkQ q (cfStartQ q j) = cfNodeQ q j 0 := by
  induction j with
  | zero =>
    change sbRoot = cfNodeQ q 0 0
    simp [cfNodeQ, cfNumQ, cfDenQ, sbRoot]
  | succ j ih =>
    change sbWalkQ q (cfStartQ q j + cfQuotQ q j) = cfNodeQ q (j + 1) 0
    rw [sbWalkQ_cfStartQ_add_of hodd hq ih _ le_rfl, cfNodeQ_end]

/-- The walk after a(0) + ... + a(j - 1) + t steps, t ≤ a(j). -/
theorem sbWalkQ_cfStartQ_add (hodd : Odd q) (hq : 3 ≤ q) {j t : ℕ} (ht : t ≤ cfQuotQ q j) :
    sbWalkQ q (cfStartQ q j + t) = cfNodeQ q j t :=
  sbWalkQ_cfStartQ_add_of hodd hq (sbWalkQ_cfStartQ hodd hq j) t ht

/-- Every step lies in a run. -/
theorem exists_cfStartQ (hodd : Odd q) (hq : 3 ≤ q) (k : ℕ) :
    ∃ j t, t ≤ cfQuotQ q j ∧ k = cfStartQ q j + t := by
  induction k with
  | zero =>
    exact ⟨0, 0, Nat.zero_le _, rfl⟩
  | succ k ih =>
    obtain ⟨j, t, ht, rfl⟩ := ih
    rcases Nat.lt_or_ge t (cfQuotQ q j) with h | h
    · exact ⟨j, t + 1, h, rfl⟩
    · have h1 := one_le_cfQuotQ hodd hq (j + 1)
      refine ⟨j + 1, 1, h1, ?_⟩
      change cfStartQ q j + t + 1 = cfStartQ q j + cfQuotQ q j + 1
      omega

/-- A semiconvergent of log2 q: Q(j) + t Q(j + 1) with 1 ≤ t ≤ a(j), as p/n; t = a(j)
    gives the convergent Q(j + 2). -/
def IsSemiconvQ (q j t p n : ℕ) : Prop :=
  1 ≤ t ∧ t ≤ cfQuotQ q j ∧ p = cfNumQ q j + t * cfNumQ q (j + 1) ∧
    n = cfDenQ q j + t * cfDenQ q (j + 1)

/-- The convergent Q(i + 2) is the semiconvergent with t = a(i). -/
theorem isSemiconvQ_conv (hodd : Odd q) (hq : 3 ≤ q) (i : ℕ) :
    IsSemiconvQ q i (cfQuotQ q i) (cfNumQ q (i + 2)) (cfDenQ q (i + 2)) := by
  refine ⟨one_le_cfQuotQ hodd hq i, le_rfl, ?_, ?_⟩
  · rw [cfNumQ_add_two]
    ring
  · rw [cfDenQ_add_two]
    ring

/-- The fraction above log2 q in a node of a run, when its denominator is not 0, is a
    semiconvergent with odd j. -/
theorem cfNodeQ_hi_semiconv (hodd : Odd q) (hq : 3 ≤ q) {j t : ℕ} (ht : t ≤ cfQuotQ q j)
    (hn : 1 ≤ (cfNodeQ q j t).hiDen) :
    ∃ j' t', j' % 2 = 1 ∧ IsSemiconvQ q j' t' (cfNodeQ q j t).hiNum (cfNodeQ q j t).hiDen := by
  by_cases hj : j % 2 = 0
  · simp only [cfNodeQ, hj, ↓reduceIte] at hn ⊢
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := by
      rcases j with _ | i
      · simp [cfDenQ] at hn
      · exact ⟨i, rfl⟩
    exact ⟨i, cfQuotQ q i, by omega, isSemiconvQ_conv hodd hq i⟩
  · simp only [cfNodeQ, hj, ↓reduceIte] at hn ⊢
    rcases Nat.eq_zero_or_pos t with ht' | ht'
    · subst ht'
      simp only [Nat.zero_mul, Nat.add_zero] at hn ⊢
      obtain ⟨i, rfl⟩ : ∃ i, j = i + 2 := by
        rcases j with _ | _ | i
        · omega
        · simp [cfDenQ] at hn
        · exact ⟨i, rfl⟩
      exact ⟨i, cfQuotQ q i, by omega, isSemiconvQ_conv hodd hq i⟩
    · exact ⟨j, t, by omega, ht', ht, rfl, rfl⟩

/-- The fraction below log2 q in a node of a run, after the first step, is a semiconvergent
    with even j. -/
theorem cfNodeQ_lo_semiconv (hodd : Odd q) (hq : 3 ≤ q) {j t : ℕ} (ht : t ≤ cfQuotQ q j)
    (hjt : 1 ≤ j + t) :
    ∃ j' t', j' % 2 = 0 ∧ IsSemiconvQ q j' t' (cfNodeQ q j t).loNum (cfNodeQ q j t).loDen := by
  by_cases hj : j % 2 = 0
  · simp only [cfNodeQ, hj, ↓reduceIte]
    rcases Nat.eq_zero_or_pos t with ht' | ht'
    · subst ht'
      simp only [Nat.zero_mul, Nat.add_zero]
      obtain ⟨i, rfl⟩ : ∃ i, j = i + 2 := by
        rcases j with _ | _ | i
        · omega
        · omega
        · exact ⟨i, rfl⟩
      exact ⟨i, cfQuotQ q i, by omega, isSemiconvQ_conv hodd hq i⟩
    · exact ⟨j, t, hj, ht', ht, rfl, rfl⟩
  · simp only [cfNodeQ, hj, ↓reduceIte]
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    exact ⟨i, cfQuotQ q i, by omega, isSemiconvQ_conv hodd hq i⟩

/-- The fractions above log2 q on the walk, with denominator n ≥ 1, are exactly the
    semiconvergents with odd j. -/
theorem sbWalkQ_hi_iff (hodd : Odd q) (hq : 3 ≤ q) {p n : ℕ} (hn : 1 ≤ n) :
    (∃ k, (sbWalkQ q k).hiNum = p ∧ (sbWalkQ q k).hiDen = n) ↔
      ∃ j t, j % 2 = 1 ∧ IsSemiconvQ q j t p n := by
  constructor
  · rintro ⟨k, hp, hk⟩
    obtain ⟨j, t, ht, rfl⟩ := exists_cfStartQ hodd hq k
    rw [sbWalkQ_cfStartQ_add hodd hq ht] at hp hk
    subst hp hk
    exact cfNodeQ_hi_semiconv hodd hq ht hn
  · rintro ⟨j, t, hj, ht1, ht, rfl, rfl⟩
    have hj0 : ¬j % 2 = 0 := by
      omega
    refine ⟨cfStartQ q j + t, ?_⟩
    rw [sbWalkQ_cfStartQ_add hodd hq ht]
    simp only [cfNodeQ, hj0, ↓reduceIte]
    exact ⟨trivial, trivial⟩

/-- The fractions below log2 q on the walk after its first step are exactly the
    semiconvergents with even j. -/
theorem sbWalkQ_lo_iff (hodd : Odd q) (hq : 3 ≤ q) {p n : ℕ} :
    (∃ k, 1 ≤ k ∧ (sbWalkQ q k).loNum = p ∧ (sbWalkQ q k).loDen = n) ↔
      ∃ j t, j % 2 = 0 ∧ IsSemiconvQ q j t p n := by
  constructor
  · rintro ⟨k, hk1, hp, hk⟩
    obtain ⟨j, t, ht, rfl⟩ := exists_cfStartQ hodd hq k
    have hjt : 1 ≤ j + t := by
      rcases Nat.eq_zero_or_pos j with h | h
      · subst h
        change 1 ≤ 0 + t at hk1
        omega
      · omega
    rw [sbWalkQ_cfStartQ_add hodd hq ht] at hp hk
    subst hp hk
    exact cfNodeQ_lo_semiconv hodd hq ht hjt
  · rintro ⟨j, t, hj, ht1, ht, rfl, rfl⟩
    refine ⟨cfStartQ q j + t, by omega, ?_⟩
    rw [sbWalkQ_cfStartQ_add hodd hq ht]
    simp only [cfNodeQ, hj, ↓reduceIte]
    exact ⟨trivial, trivial⟩

/-- The upper record Orders n ≥ 1 are exactly the denominators of the semiconvergents of
    log2 q above it. -/
theorem upperRecordQ_iff_semiconvQ (hodd : Odd q) (hq : 3 ≤ q) {n : ℕ} (hn : 1 ≤ n) :
    UpperRecordQ q n ↔ ∃ j t p, j % 2 = 1 ∧ IsSemiconvQ q j t p n := by
  rw [upperRecordQ_iff_sbWalkQ hodd hq hn]
  constructor
  · rintro ⟨k, hk⟩
    obtain ⟨j, t, hj, h⟩ := (sbWalkQ_hi_iff hodd hq hn).mp ⟨k, rfl, hk⟩
    exact ⟨j, t, _, hj, h⟩
  · rintro ⟨j, t, p, hj, h⟩
    obtain ⟨k, _, hk⟩ := (sbWalkQ_hi_iff hodd hq hn).mpr ⟨j, t, hj, h⟩
    exact ⟨k, hk⟩

/-- The lower record Orders n ≥ 1 are exactly the denominators of the semiconvergents of
    log2 q below it. -/
theorem lowerRecordQ_iff_semiconvQ (hodd : Odd q) (hq : 3 ≤ q) {n : ℕ} (hn : 1 ≤ n) :
    LowerRecordQ q n ↔ ∃ j t p, j % 2 = 0 ∧ IsSemiconvQ q j t p n := by
  rw [lowerRecordQ_iff_sbWalkQ hodd hq hn]
  constructor
  · rintro ⟨k, hk⟩
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · subst h0
      change 1 = n at hk
      subst hk
      refine ⟨0, 1, 1, rfl, le_rfl, one_le_cfQuotQ hodd hq 0, ?_, ?_⟩
      · simp [cfNumQ]
      · simp [cfDenQ]
    · obtain ⟨j, t, hj, h⟩ := (sbWalkQ_lo_iff hodd hq).mp ⟨k, h0, rfl, hk⟩
      exact ⟨j, t, _, hj, h⟩
  · rintro ⟨j, t, p, hj, h⟩
    obtain ⟨k, _, _, hk⟩ := (sbWalkQ_lo_iff hodd hq).mpr ⟨j, t, hj, h⟩
    exact ⟨k, hk⟩

/-- Mathlib's stream of integer and fractional parts of log2 q holds the complete
    quotients. -/
theorem stream_log2Q (hodd : Odd q) (hq : 3 ≤ q) (j : ℕ) :
    GenContFract.IntFractPair.stream (log2Q q) j = some ⟨⌊cqQ q j⌋, Int.fract (cqQ q j)⟩ := by
  induction j with
  | zero =>
    rfl
  | succ j ih =>
    rw [GenContFract.IntFractPair.stream_succ_of_some ih (fract_cqQ_pos hodd hq j).ne']
    rfl

/-- The head of Mathlib's continued fraction of log2 q is a(0). -/
theorem of_log2Q_h (hodd : Odd q) (hq : 3 ≤ q) :
    (GenContFract.of (log2Q q)).h = cfQuotQ q 0 := by
  rw [GenContFract.of_h_eq_floor, cfQuotQ_cast hodd hq 0, cqQ_zero]

/-- The j-th partial quotient of Mathlib's continued fraction of log2 q is a(j + 1). -/
theorem of_log2Q_s (hodd : Odd q) (hq : 3 ≤ q) (j : ℕ) :
    (GenContFract.of (log2Q q)).s.get? j = some ⟨1, (cfQuotQ q (j + 1) : ℝ)⟩ := by
  rw [GenContFract.get?_of_eq_some_of_succ_get?_intFractPair_stream
    (stream_log2Q hodd hq (j + 1)), cfQuotQ_cast hodd hq]

/-- The numerators and denominators of Mathlib's continued fraction of log2 q are the
    continuants Q(j + 2): Q(j + 2) is the j-th convergent. -/
theorem of_log2Q_nums_dens (hodd : Odd q) (hq : 3 ≤ q) (j : ℕ) :
    (GenContFract.of (log2Q q)).nums j = cfNumQ q (j + 2) ∧
      (GenContFract.of (log2Q q)).dens j = cfDenQ q (j + 2) ∧
      (GenContFract.of (log2Q q)).nums (j + 1) = cfNumQ q (j + 3) ∧
      (GenContFract.of (log2Q q)).dens (j + 1) = cfDenQ q (j + 3) := by
  induction j with
  | zero =>
    have hs := of_log2Q_s hodd hq 0
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [GenContFract.zeroth_num_eq_h, of_log2Q_h hodd hq, cfNumQ_add_two]
      simp [cfNumQ]
    · rw [GenContFract.zeroth_den_eq_one, cfDenQ_add_two]
      simp [cfDenQ]
    · rw [GenContFract.first_num_eq hs, of_log2Q_h hodd hq, cfNumQ_add_two, cfNumQ_add_two]
      simp [cfNumQ]
    · rw [GenContFract.first_den_eq hs, cfDenQ_add_two, cfDenQ_add_two]
      simp [cfDenQ]
  | succ j ih =>
    obtain ⟨h1, h2, h3, h4⟩ := ih
    have hs := of_log2Q_s hodd hq (j + 1)
    refine ⟨h3, h4, ?_, ?_⟩
    · rw [GenContFract.nums_recurrence hs h1 h3, cfNumQ_add_two q (j + 2)]
      push_cast
      ring
    · rw [GenContFract.dens_recurrence hs h2 h4, cfDenQ_add_two q (j + 2)]
      push_cast
      ring

/-- Q(j + 2) is Mathlib's j-th convergent of log2 q. -/
theorem of_log2Q_convs (hodd : Odd q) (hq : 3 ≤ q) (j : ℕ) :
    (GenContFract.of (log2Q q)).convs j = (cfNumQ q (j + 2) : ℝ) / cfDenQ q (j + 2) := by
  obtain ⟨h1, h2, _, _⟩ := of_log2Q_nums_dens hodd hq j
  rw [GenContFract.conv_eq_num_div_den, h1, h2]

end AcceleratedCollatz
