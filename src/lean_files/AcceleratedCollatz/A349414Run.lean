-- SPDX-License-Identifier: MIT
import Mathlib.Tactic

/-!
# The A349414 map on odd k, stopped at the first value below the start

Self-contained extract of the AcceleratedCollatz Lean 4 project; depends on
Mathlib only. The proofs, for every odd k, of the checks of `OEIS/a349414_variant_01.py`
that hold for every k (A53 of the project, 5 Nov 2026).

The map on odd values (n ↦ n + A349414(n) for k = 2n + 1), with T(x) = x/2 for even x and
(3x + 1)/2 for odd x:

* U: y ≡ 3 (mod 4) ↦ (3y + 1)/2 = T y;
* D: y ≡ 1 (mod 8) ↦ (3y + 1)/4 = T (T y);
* S: y ≡ 5 (mod 8) ↦ (y - 1)/4, a value off the path with T ((y - 1)/4) = T (T (T y)).

`run k j` is the value after j steps, with the numbers of U and D steps (m) and the power of
2 (e: 1 for U, 2 for D and S). The run stops at the first j with a value below k.

* `stops_of_drops`: if the T-path of k ever goes below k, the run stops.
* `stop_ne_U`: a step U never goes down, so a stop is by D or by S.
* `stop_D`: a stop by D is the drop: its value is the first value of the T-path below k.
* `stop_S`: a stop by S comes before the drop, at a merge: the T-path of k stays at least k
  up to some s, its value at s is above the stop value, and T of the stop value is the value
  at s + 1 (the same next odd value).
* `pow_lt_of_stop`: the stop has 3^m < 2^e, that is, its product of the factors
  U: 3/2, D: 3/4, S: 1/4 is below 1.

That the stop is at the *first* prefix with product below 1 is checked by the script only
(odd k < 2^18): for words without S it is Terras' coefficient stopping time conjecture.

Added (A55 to A57 of the project, 5 Nov 2026):

* `stops_iff`: the run stops for every odd k ≥ 3 iff every T-path from k ≥ 1 reaches 1.
* `run_U`, `run_D`, `run_S`: the letter powers in closed form, with h r s n = ∑_{i ≤ n}
  r^i s^(n-i) (OEIS A401763): n + 1 steps U from y ≡ -1 (mod 2^(n+2)) give
  2^(n+1) y' = 3^(n+1) y + h 3 2 n; D from y ≡ 1 (mod 2^(2n+3)) gives
  4^(n+1) y' = 3^(n+1) y + h 4 3 n; S from 3y + 1 ≡ 0 (mod 2^(2n+3)) gives
  4^(n+1) y' + h 4 1 n = y. `h_mul`: (r - s) h r s n = r^(n+1) - s^(n+1).
* `run_class`: the starts of a word of e ≤ E form one class modulo 2^(E+1) (check 4).
* `path`: the run reads the parities of T k, T^2 k, ..: m is the number of odd ones among the
  first e. `oc_eq`: over the odd k < 2^(n+1) these parities are binomial (Terras).
* `density`: for every M, from some E on, at most 2^E / M of the 2^E odd k (mod 2^(E+1)) have
  3^m ≥ 2^e for every word of e ≤ E. `stop_of_coeff`: a word with 3^m < 2^e stops every
  k > 2^e 3^m that starts with it. All in integers (3^5 < 2^8, a weighted binomial sum, Bernoulli).
-/

namespace A349414Run

/-- The Collatz map T: x/2 for even x, (3x + 1)/2 for odd x. -/
def T (x : ℕ) : ℕ := if x % 2 = 0 then x / 2 else (3 * x + 1) / 2

/-- One step on (value, number of U and D steps, power of 2). -/
def st (p : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ :=
  if p.1 % 4 = 3 then ((3 * p.1 + 1) / 2, p.2.1 + 1, p.2.2 + 1)
  else if p.1 % 8 = 1 then ((3 * p.1 + 1) / 4, p.2.1 + 1, p.2.2 + 2)
  else ((p.1 - 1) / 4, p.2.1, p.2.2 + 2)

/-- The state after j steps from k. -/
def run (k j : ℕ) : ℕ × ℕ × ℕ := st^[j] (k, 0, 0)

/-- The value after j steps. -/
def val (k j : ℕ) : ℕ := (run k j).1

theorem run_succ (k j : ℕ) : run k (j + 1) = st (run k j) :=
  Function.iterate_succ_apply' st j (k, 0, 0)

theorem val_succ (k j : ℕ) : val k (j + 1) =
    if val k j % 4 = 3 then (3 * val k j + 1) / 2
    else if val k j % 8 = 1 then (3 * val k j + 1) / 4 else (val k j - 1) / 4 := by
  unfold val; rw [run_succ, st]; split_ifs <;> rfl

theorem val_odd {k : ℕ} (hk : k % 2 = 1) (j : ℕ) : val k j % 2 = 1 := by
  induction j with
  | zero => exact hk
  | succ j ih => rw [val_succ]; split_ifs <;> omega

theorem iterate_T (s k : ℕ) : T^[s + 1] k = T (T^[s] k) := Function.iterate_succ_apply' T s k

theorem T_odd {y : ℕ} (hy : y % 2 = 1) : T y = (3 * y + 1) / 2 := by
  unfold T; rw [ite_eq_right (by omega)]

theorem T_even {y : ℕ} (hy : y % 2 = 0) : T y = y / 2 := by
  unfold T; rw [ite_eq_left hy]

/-- The invariant at step j: T of the run value is the path value at s + 1, the path stays at
least k before s, and the run value is at most the path value at s. -/
def Inv (k j : ℕ) : Prop :=
  ∃ s, j ≤ s ∧ T^[s + 1] k = T (val k j) ∧ (∀ i < s, k ≤ T^[i] k) ∧ val k j ≤ T^[s] k

theorem inv_zero (k : ℕ) : Inv k 0 := ⟨0, le_rfl, rfl, fun _ h => absurd h (by omega), le_rfl⟩

/-- The three steps against T. -/
theorem step_U {y : ℕ} (h : y % 4 = 3) : T y = (3 * y + 1) / 2 := T_odd (by omega)

theorem step_D {y : ℕ} (h : y % 8 = 1) :
    T y = (3 * y + 1) / 2 ∧ T (T y) = (3 * y + 1) / 4 := by
  have h1 := T_odd (y := y) (by omega)
  refine ⟨h1, ?_⟩
  rw [h1, T_even (by omega)]; omega

theorem step_S {y : ℕ} (h : y % 8 = 5) :
    T y = (3 * y + 1) / 2 ∧ T (T y) = (3 * y + 1) / 4 ∧ T (T (T y)) = T ((y - 1) / 4) := by
  have h1 := T_odd (y := y) (by omega)
  have h2 : T (T y) = (3 * y + 1) / 4 := by rw [h1, T_even (by omega)]; omega
  refine ⟨h1, h2, ?_⟩
  rw [h2, T_even (by omega), T_odd (by omega)]; omega

theorem inv_succ {k j : ℕ} (hk : k % 2 = 1) (h : Inv k j) (hj : k ≤ val k j) :
    Inv k (j + 1) := by
  obtain ⟨s, hs, h1, h2, h3⟩ := h
  have hy := val_odd hk j
  have hv := val_succ k j
  have e1 : T^[s + 1 + 1] k = T (T (val k j)) := by rw [iterate_T, h1]
  have e2 : T^[s + 1 + 1 + 1] k = T (T (T (val k j))) := by rw [iterate_T, e1]
  by_cases hU : val k j % 4 = 3
  · rw [ite_eq_left hU] at hv
    have hT := step_U hU
    refine ⟨s + 1, by omega, ?_, ?_, ?_⟩
    · rw [e1, hT, hv]
    · intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact h2 i hi
      · omega
    · rw [h1, hT, hv]
  by_cases hD : val k j % 8 = 1
  · rw [ite_eq_right hU, ite_eq_left hD] at hv
    obtain ⟨hT1, hT2⟩ := step_D hD
    refine ⟨s + 2, by omega, ?_, ?_, ?_⟩
    · rw [e2, hT2, hv]
    · intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
        · exact h2 i hi
        · omega
      · rw [h1, hT1]; omega
    · rw [e1, hT2, hv]
  · have hS : val k j % 8 = 5 := by omega
    rw [ite_eq_right hU, ite_eq_right hD] at hv
    obtain ⟨hT1, hT2, hT3⟩ := step_S hS
    refine ⟨s + 2, by omega, ?_, ?_, ?_⟩
    · rw [e2, hT3, hv]
    · intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
        · exact h2 i hi
        · omega
      · rw [h1, hT1]; omega
    · rw [e1, hT2, hv]; omega

/-- While the run stays at least k, the invariant holds. -/
theorem inv_of_le {k : ℕ} (hk : k % 2 = 1) :
    ∀ j, (∀ j' < j, k ≤ val k j') → Inv k j
  | 0, _ => inv_zero k
  | j + 1, h => inv_succ hk (inv_of_le hk j fun j' hj' => h j' (by omega)) (h j (by omega))

/-- If the T-path of k goes below k, the run stops. -/
theorem stops_of_drops {k i : ℕ} (hk : k % 2 = 1) (hd : T^[i] k < k) : ∃ j, val k j < k := by
  by_contra hc
  push Not at hc
  obtain ⟨s, hs, -, h2, -⟩ := inv_of_le hk (i + 1) fun j' _ => hc j'
  exact absurd (h2 i (by omega)) (by omega)

/-- A step U goes up, so a stop is never by U. -/
theorem stop_ne_U {k j : ℕ} (hU : val k j % 4 = 3) : val k j < val k (j + 1) := by
  rw [val_succ, ite_eq_left hU]; omega

/-- A stop by D is the drop: the stop value is the first value of the T-path below k. -/
theorem stop_D {k J : ℕ} (hk : k % 2 = 1) (hJ : ∀ j ≤ J, k ≤ val k j) (hD : val k J % 8 = 1) :
    ∃ s, T^[s] k = val k (J + 1) ∧ ∀ i < s, k ≤ T^[i] k := by
  obtain ⟨s, -, h1, h2, h3⟩ := inv_of_le hk J fun j' hj' => hJ j' (by omega)
  have hv := val_succ k J
  rw [ite_eq_right (by omega), ite_eq_left hD] at hv
  obtain ⟨hT1, hT2⟩ := step_D hD
  refine ⟨s + 2, ?_, ?_⟩
  · rw [show s + 2 = s + 1 + 1 by ring, iterate_T, h1, hT2, hv]
  · intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact h2 i hi
      · have := hJ J le_rfl; omega
    · rw [h1, hT1]; have := hJ J le_rfl; omega

/-- A stop by S comes before the drop, at a merge: the path stays at least k before s, its
value at s is above the stop value, and T of the stop value is the path value at s + 1. -/
theorem stop_S {k J : ℕ} (hk : k % 2 = 1) (hJ : ∀ j ≤ J, k ≤ val k j) (hS : val k J % 8 = 5) :
    ∃ s, T (val k (J + 1)) = T^[s + 1] k ∧ (∀ i < s, k ≤ T^[i] k) ∧
      val k (J + 1) < T^[s] k := by
  obtain ⟨s, -, h1, h2, h3⟩ := inv_of_le hk J fun j' hj' => hJ j' (by omega)
  have hv := val_succ k J
  rw [ite_eq_right (by omega), ite_eq_right (by omega)] at hv
  obtain ⟨hT1, hT2, hT3⟩ := step_S hS
  refine ⟨s + 2, ?_, ?_, ?_⟩
  · rw [show s + 2 + 1 = s + 1 + 1 + 1 by ring, iterate_T, iterate_T, h1, hT3, hv]
  · intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact h2 i hi
      · have := hJ J le_rfl; omega
    · rw [h1, hT1]; have := hJ J le_rfl; omega
  · rw [show s + 2 = s + 1 + 1 by ring, iterate_T, h1, hT2, hv]; omega

/-- The numbers of U and D steps, and the power of 2. -/
def ud (k j : ℕ) : ℕ := (run k j).2.1

def ex (k j : ℕ) : ℕ := (run k j).2.2

/-- 3 3^m k ≤ (3 y + 1) 2^e at every step: the offset of the value from 3^m k / 2^e is at
least -1/3. -/
theorem bound {k : ℕ} (hk : k % 2 = 1) (j : ℕ) :
    3 * 3 ^ ud k j * k ≤ (3 * val k j + 1) * 2 ^ ex k j := by
  induction j with
  | zero => simp [ud, ex, val, run]
  | succ j ih =>
    have hy := val_odd hk j
    simp only [ud, ex, val] at ih hy ⊢
    rw [run_succ]
    generalize run k j = p at ih hy ⊢
    obtain ⟨y, m, e⟩ := p
    simp only at ih hy ⊢
    unfold st
    split_ifs with hU hD
    · obtain ⟨a, ha⟩ : ∃ a, 3 * y + 1 = 2 * a := ⟨(3 * y + 1) / 2, by omega⟩
      simp only [ha, show 2 * a / 2 = a by omega, pow_succ]
      generalize 2 ^ e = P at ih ⊢
      generalize 3 ^ m = Q at ih ⊢
      nlinarith
    · obtain ⟨a, ha⟩ : ∃ a, 3 * y + 1 = 4 * a := ⟨(3 * y + 1) / 4, by omega⟩
      simp only [ha, show 4 * a / 4 = a by omega, pow_succ]
      generalize 2 ^ e = P at ih ⊢
      generalize 3 ^ m = Q at ih ⊢
      nlinarith
    · obtain ⟨a, ha⟩ : ∃ a, y = 4 * a + 1 := ⟨(y - 1) / 4, by omega⟩
      subst ha
      simp only [show (4 * a + 1 - 1) / 4 = a by omega, pow_add]
      generalize 2 ^ e = P at ih ⊢
      generalize 3 ^ m = Q at ih ⊢
      nlinarith

/-- At a stop, 3^m < 2^e: the product of the factors (U: 3/2, D: 3/4, S: 1/4) is below 1. -/
theorem pow_lt_of_stop {k J : ℕ} (hk : k % 2 = 1) (h : val k J < k) :
    3 ^ ud k J < 2 ^ ex k J := by
  have hb := bound hk J
  have hP : 0 < 2 ^ ex k J := by positivity
  by_contra hc
  push Not at hc
  have : 3 * 2 ^ ex k J * k ≤ 3 * 3 ^ ud k J * k := by gcongr
  nlinarith

/-! ## The run stops for every odd k ≥ 3 iff every T-path reaches 1 (A55) -/

/-- x reaches 1 under T. -/
def Reaches (x : ℕ) : Prop := ∃ i, T^[i] x = 1

theorem reaches_T {x : ℕ} (h : Reaches x) : Reaches (T x) := by
  obtain ⟨i, hi⟩ := h
  cases i with
  | zero => rw [Function.iterate_zero_apply] at hi; subst hi; exact ⟨1, by decide⟩
  | succ i => exact ⟨i, by rw [← Function.iterate_succ_apply]; exact hi⟩

theorem reaches_of_iterate {x n : ℕ} (h : Reaches (T^[n] x)) : Reaches x := by
  obtain ⟨i, hi⟩ := h
  exact ⟨i + n, by rw [Function.iterate_add_apply]; exact hi⟩

/-- The run of every odd k ≥ 3 stops iff every T-path from k ≥ 1 reaches 1: one way by
`stops_of_drops`, the other by strong induction, a stop by D at a smaller path value and a stop
by S at a smaller value with the same next value. -/
theorem stops_iff :
    (∀ k, k % 2 = 1 → 3 ≤ k → ∃ j, val k j < k) ↔ ∀ k, 1 ≤ k → Reaches k := by
  constructor
  · intro H k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk1
      by_cases h1 : k = 1
      · exact ⟨0, by simp [h1]⟩
      by_cases he : k % 2 = 0
      · refine reaches_of_iterate (n := 1) ?_
        rw [Function.iterate_one, T_even he]
        exact ih (k / 2) (by omega) (by omega)
      have hk : k % 2 = 1 := by omega
      have hstop := H k hk (by omega)
      classical
      obtain ⟨J, hJ, hmin⟩ : ∃ J, val k J < k ∧ ∀ j < J, ¬ val k j < k :=
        ⟨Nat.find hstop, Nat.find_spec hstop, fun j hj => Nat.find_min hstop hj⟩
      have hJ0 : J ≠ 0 := by
        rintro rfl
        have : val k 0 = k := rfl
        omega
      obtain ⟨J', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hJ0
      have hle : ∀ j ≤ J', k ≤ val k j := fun j hj => not_lt.mp (hmin j (by omega))
      have hpos : 1 ≤ val k (J' + 1) := by have := val_odd hk (J' + 1); omega
      have hJ1 : val k (J' + 1) < k := hJ
      have hv := val_odd hk J'
      by_cases hU : val k J' % 4 = 3
      · have := stop_ne_U hU
        have := hle J' le_rfl
        omega
      by_cases hD : val k J' % 8 = 1
      · obtain ⟨s, hs, -⟩ := stop_D hk hle hD
        exact reaches_of_iterate (n := s) (by rw [hs]; exact ih _ hJ1 hpos)
      · obtain ⟨s, hs, -, -⟩ := stop_S hk hle (by omega)
        exact reaches_of_iterate (n := s + 1) (by rw [← hs]; exact reaches_T (ih _ hJ1 hpos))
  · intro H k hk h3
    obtain ⟨i, hi⟩ := H k (by omega)
    exact stops_of_drops hk (i := i) (by omega)

/-! ## The letter powers U^n, D^n, S^n (A57)

h r s n = (r^(n+1) - s^(n+1))/(r - s), the entry of A401763 for the pair (r, s). -/

/-- h r s n = ∑_{i ≤ n} r^i s^(n-i). -/
def h (r s : ℕ) : ℕ → ℕ
  | 0 => 1
  | n + 1 => r ^ (n + 1) + s * h r s n

theorem h_succ' (r s n : ℕ) : h r s (n + 1) = s ^ (n + 1) + r * h r s n := by
  induction n with
  | zero => simp [h]; ring
  | succ n ih =>
    change r ^ (n + 2) + s * h r s (n + 1) = s ^ (n + 2) + r * h r s (n + 1)
    calc r ^ (n + 2) + s * h r s (n + 1)
        = r ^ (n + 2) + s * (s ^ (n + 1) + r * h r s n) := by rw [ih]
      _ = s ^ (n + 2) + r * (r ^ (n + 1) + s * h r s n) := by ring
      _ = s ^ (n + 2) + r * h r s (n + 1) := rfl

/-- (r - s) h r s n = r^(n+1) - s^(n+1), with r = s + d. -/
theorem h_mul (s d n : ℕ) : d * h (s + d) s n + s ^ (n + 1) = (s + d) ^ (n + 1) := by
  induction n with
  | zero => simp [h]; ring
  | succ n ih =>
    calc d * h (s + d) s (n + 1) + s ^ (n + 2)
        = d * (s + d) ^ (n + 1) + s * (d * h (s + d) s n + s ^ (n + 1)) := by
          change d * ((s + d) ^ (n + 1) + s * h (s + d) s n) + s ^ (n + 2) = _; ring
      _ = (s + d) ^ (n + 2) := by rw [ih]; ring

theorem h32 (n : ℕ) : h 3 2 n + 2 ^ (n + 1) = 3 ^ (n + 1) := by simpa using h_mul 2 1 n

theorem h43 (n : ℕ) : h 4 3 n + 3 ^ (n + 1) = 4 ^ (n + 1) := by simpa using h_mul 3 1 n

theorem h41 (n : ℕ) : 3 * h 4 1 n + 1 = 4 ^ (n + 1) := by simpa using h_mul 1 3 n

/-- U^(n+1) on y ≡ -1 (mod 2^(n+2)): 2^(n+1) y' = 3^(n+1) y + h_n(3,2). -/
theorem pow_U (n : ℕ) : ∀ y m e, 2 ^ (n + 2) ∣ y + 1 →
    ∃ y', st^[n + 1] (y, m, e) = (y', m + (n + 1), e + (n + 1)) ∧
      2 ^ (n + 1) * y' = 3 ^ (n + 1) * y + h 3 2 n := by
  induction n with
  | zero =>
    intro y m e hd
    obtain ⟨a, ha⟩ := hd
    norm_num at ha
    have h4 : y % 4 = 3 := by omega
    refine ⟨(3 * y + 1) / 2, by simp [st, h4], ?_⟩
    simp [h]; omega
  | succ n ih =>
    intro y m e hd
    obtain ⟨a, ha⟩ := hd
    have hy : y + 1 = 2 * (2 ^ (n + 2) * a) := by rw [ha]; ring
    have h4' : y + 1 = 4 * (2 ^ n * (2 * a)) := by rw [ha]; ring
    have h4 : y % 4 = 3 := by generalize 2 ^ n * (2 * a) = Q at h4'; omega
    have hst : st (y, m, e) = ((3 * y + 1) / 2, m + 1, e + 1) := by simp [st, h4]
    have hdiv : 2 ^ (n + 2) ∣ (3 * y + 1) / 2 + 1 := by
      refine ⟨3 * a, ?_⟩
      rw [show 2 ^ (n + 2) * (3 * a) = 3 * (2 ^ (n + 2) * a) by ring]
      generalize 2 ^ (n + 2) * a = Q at hy ⊢
      omega
    obtain ⟨y', h1, h2⟩ := ih _ (m + 1) (e + 1) hdiv
    refine ⟨y', ?_, ?_⟩
    · rw [Function.iterate_succ_apply, hst, h1,
        show m + 1 + (n + 1) = m + (n + 1 + 1) by omega,
        show e + 1 + (n + 1) = e + (n + 1 + 1) by omega]
    · have hy1 : 2 * ((3 * y + 1) / 2) = 3 * y + 1 := by omega
      change 2 ^ (n + 1 + 1) * y' = 3 ^ (n + 1 + 1) * y + (3 ^ (n + 1) + 2 * h 3 2 n)
      calc 2 ^ (n + 1 + 1) * y' = 2 * (2 ^ (n + 1) * y') := by ring
        _ = 2 * (3 ^ (n + 1) * ((3 * y + 1) / 2) + h 3 2 n) := by rw [h2]
        _ = 3 ^ (n + 1) * (2 * ((3 * y + 1) / 2)) + 2 * h 3 2 n := by ring
        _ = _ := by rw [hy1]; ring

/-- D^(n+1) on y ≡ 1 (mod 2^(2n+3)): 4^(n+1) y' = 3^(n+1) y + h_n(4,3). -/
theorem pow_D (n : ℕ) : ∀ y m e, (∃ a, y = 2 ^ (2 * n + 3) * a + 1) →
    ∃ y', st^[n + 1] (y, m, e) = (y', m + (n + 1), e + 2 * (n + 1)) ∧
      4 ^ (n + 1) * y' = 3 ^ (n + 1) * y + h 4 3 n := by
  induction n with
  | zero =>
    intro y m e hd
    obtain ⟨a, ha⟩ := hd
    norm_num at ha
    have h8 : y % 8 = 1 := by omega
    refine ⟨(3 * y + 1) / 4, by simp [st, h8, show y % 4 ≠ 3 by omega], ?_⟩
    simp [h]; omega
  | succ n ih =>
    intro y m e hd
    obtain ⟨a, ha⟩ := hd
    rw [show 2 ^ (2 * (n + 1) + 3) * a = 8 * (2 ^ (2 * n + 2) * a) by ring] at ha
    have h8 : y % 8 = 1 := by generalize 2 ^ (2 * n + 2) * a = Q at ha; omega
    have hst : st (y, m, e) = ((3 * y + 1) / 4, m + 1, e + 2) := by
      simp [st, h8, show y % 4 ≠ 3 by omega]
    have hdiv : ∃ a', (3 * y + 1) / 4 = 2 ^ (2 * n + 3) * a' + 1 := by
      refine ⟨3 * a, ?_⟩
      rw [show 2 ^ (2 * n + 3) * (3 * a) = 6 * (2 ^ (2 * n + 2) * a) by ring]
      generalize 2 ^ (2 * n + 2) * a = Q at ha ⊢
      omega
    obtain ⟨y', h1, h2⟩ := ih _ (m + 1) (e + 2) hdiv
    refine ⟨y', ?_, ?_⟩
    · rw [Function.iterate_succ_apply, hst, h1,
        show m + 1 + (n + 1) = m + (n + 1 + 1) by omega,
        show e + 2 + 2 * (n + 1) = e + 2 * (n + 1 + 1) by omega]
    · have hy1 : 4 * ((3 * y + 1) / 4) = 3 * y + 1 := by omega
      rw [h_succ']
      calc 4 ^ (n + 1 + 1) * y' = 4 * (4 ^ (n + 1) * y') := by ring
        _ = 4 * (3 ^ (n + 1) * ((3 * y + 1) / 4) + h 4 3 n) := by rw [h2]
        _ = 3 ^ (n + 1) * (4 * ((3 * y + 1) / 4)) + 4 * h 4 3 n := by ring
        _ = _ := by rw [hy1]; ring

/-- S^(n+1) on y ≡ -1/3 (mod 2^(2n+3)): 4^(n+1) y' + h_n(4,1) = y. -/
theorem pow_S (n : ℕ) : ∀ y m e, (∃ a, 3 * y + 1 = 2 ^ (2 * n + 3) * a) →
    ∃ y', st^[n + 1] (y, m, e) = (y', m, e + 2 * (n + 1)) ∧
      4 ^ (n + 1) * y' + h 4 1 n = y := by
  induction n with
  | zero =>
    intro y m e hd
    obtain ⟨a, ha⟩ := hd
    norm_num at ha
    have h8 : y % 8 = 5 := by omega
    refine ⟨(y - 1) / 4, by simp [st, show y % 4 ≠ 3 by omega, show y % 8 ≠ 1 by omega], ?_⟩
    simp [h]; omega
  | succ n ih =>
    intro y m e hd
    obtain ⟨a, ha⟩ := hd
    rw [show 2 ^ (2 * (n + 1) + 3) * a = 8 * (2 ^ (2 * n + 2) * a) by ring] at ha
    have h8 : y % 8 = 5 := by generalize 2 ^ (2 * n + 2) * a = Q at ha; omega
    have hst : st (y, m, e) = ((y - 1) / 4, m, e + 2) := by
      simp [st, show y % 4 ≠ 3 by omega, show y % 8 ≠ 1 by omega]
    have hdiv : ∃ a', 3 * ((y - 1) / 4) + 1 = 2 ^ (2 * n + 3) * a' := by
      refine ⟨a, ?_⟩
      rw [show 2 ^ (2 * n + 3) * a = 2 * (2 ^ (2 * n + 2) * a) by ring]
      generalize 2 ^ (2 * n + 2) * a = Q at ha ⊢
      omega
    obtain ⟨y', h1, h2⟩ := ih _ m (e + 2) hdiv
    refine ⟨y', ?_, ?_⟩
    · rw [Function.iterate_succ_apply, hst, h1,
        show e + 2 + 2 * (n + 1) = e + 2 * (n + 1 + 1) by omega]
    · have hy1 : 4 * ((y - 1) / 4) + 1 = y := by omega
      rw [h_succ', one_pow]
      calc 4 ^ (n + 1 + 1) * y' + (1 + 4 * h 4 1 n)
          = 4 * (4 ^ (n + 1) * y' + h 4 1 n) + 1 := by ring
        _ = y := by rw [h2, hy1]

theorem run_add (k j n : ℕ) : run k (j + n) = st^[n] (run k j) := by
  rw [run, add_comm, Function.iterate_add_apply]; rfl

theorem run_eq (k j : ℕ) : run k j = (val k j, ud k j, ex k j) := rfl

/-- n + 1 steps U from a value ≡ -1 (mod 2^(n+2)). -/
theorem run_U {k j : ℕ} (n : ℕ) (hd : 2 ^ (n + 2) ∣ val k j + 1) :
    ∃ y', run k (j + (n + 1)) = (y', ud k j + (n + 1), ex k j + (n + 1)) ∧
      2 ^ (n + 1) * y' = 3 ^ (n + 1) * val k j + h 3 2 n := by
  rw [run_add, run_eq]; exact pow_U n _ _ _ hd

/-- n + 1 steps D from a value ≡ 1 (mod 2^(2n+3)). -/
theorem run_D {k j : ℕ} (n : ℕ) (hd : ∃ a, val k j = 2 ^ (2 * n + 3) * a + 1) :
    ∃ y', run k (j + (n + 1)) = (y', ud k j + (n + 1), ex k j + 2 * (n + 1)) ∧
      4 ^ (n + 1) * y' = 3 ^ (n + 1) * val k j + h 4 3 n := by
  rw [run_add, run_eq]; exact pow_D n _ _ _ hd

/-- n + 1 steps S from a value ≡ -1/3 (mod 2^(2n+3)). -/
theorem run_S {k j : ℕ} (n : ℕ) (hd : ∃ a, 3 * val k j + 1 = 2 ^ (2 * n + 3) * a) :
    ∃ y', run k (j + (n + 1)) = (y', ud k j, ex k j + 2 * (n + 1)) ∧
      4 ^ (n + 1) * y' + h 4 1 n = val k j := by
  rw [run_add, run_eq]; exact pow_S n _ _ _ hd

/-! ## A Terras-type density for the run (A56)

The starts of a word form one class: `run_class` (the script's check 4). For odd k the run reads
the parities of T k, T^2 k, ..: `path`, with m the number of odd ones among the first e. Those
parities are spread binomially over the odd k < 2^(e+1): `oc_eq`. So the share of the odd
k (mod 2^(E+1)) whose words of e ≤ E all keep 3^m ≥ 2^e goes to 0: `density`. A class whose
word has 3^m < 2^e stops for every k > 2^e 3^m in it: `stop_of_coeff`. -/

theorem ex_succ (k j : ℕ) :
    ex k (j + 1) = if val k j % 4 = 3 then ex k j + 1 else ex k j + 2 := by
  unfold ex val; rw [run_succ, st]; split_ifs <;> rfl

theorem ud_succ (k j : ℕ) : ud k (j + 1) =
    if val k j % 4 = 3 then ud k j + 1 else if val k j % 8 = 1 then ud k j + 1 else ud k j := by
  unfold ud val; rw [run_succ, st]; split_ifs <;> rfl

/-- 2^e y ≤ 3^m k + 2^e 3^m at every step. -/
theorem upper {k : ℕ} (hk : k % 2 = 1) (j : ℕ) :
    2 ^ ex k j * val k j ≤ 3 ^ ud k j * k + 2 ^ ex k j * 3 ^ ud k j := by
  induction j with
  | zero => simp [ud, ex, val, run]
  | succ j ih =>
    have hy := val_odd hk j
    simp only [ud, ex, val] at ih hy ⊢
    rw [run_succ]
    generalize run k j = p at ih hy ⊢
    obtain ⟨y, m, e⟩ := p
    simp only at ih hy ⊢
    have hQ : 1 ≤ 3 ^ m := Nat.one_le_pow _ _ (by norm_num)
    unfold st
    split_ifs with hU hD
    · obtain ⟨a, ha⟩ : ∃ a, 3 * y + 1 = 2 * a := ⟨(3 * y + 1) / 2, by omega⟩
      simp only [ha, show 2 * a / 2 = a by omega, pow_succ]
      generalize 2 ^ e = P at ih ⊢
      generalize 3 ^ m = Q at ih hQ ⊢
      nlinarith
    · obtain ⟨a, ha⟩ : ∃ a, 3 * y + 1 = 4 * a := ⟨(3 * y + 1) / 4, by omega⟩
      simp only [ha, show 4 * a / 4 = a by omega, pow_succ]
      generalize 2 ^ e = P at ih ⊢
      generalize 3 ^ m = Q at ih hQ ⊢
      nlinarith
    · obtain ⟨a, ha⟩ : ∃ a, y = 4 * a + 1 := ⟨(y - 1) / 4, by omega⟩
      subst ha
      simp only [show (4 * a + 1 - 1) / 4 = a by omega, pow_add]
      generalize 2 ^ e = P at ih ⊢
      generalize 3 ^ m = Q at ih hQ ⊢
      nlinarith

/-- A word with 3^m < 2^e stops every k > 2^e 3^m that starts with it. -/
theorem stop_of_coeff {k j : ℕ} (hk : k % 2 = 1) (hc : 3 ^ ud k j < 2 ^ ex k j)
    (hbig : 2 ^ ex k j * 3 ^ ud k j < k) : val k j < k := by
  have hu := upper hk j
  generalize 2 ^ ex k j = P at hu hc hbig
  generalize 3 ^ ud k j = Q at hu hc hbig
  by_contra hn
  push Not at hn
  have h1 : P * k ≤ P * val k j := Nat.mul_le_mul_left P hn
  have h2 : (Q + 1) * k ≤ P * k := Nat.mul_le_mul_right k hc
  nlinarith

/-- The starts of a word form one class (check 4): k + 2^(E+1) t runs as k while e ≤ E. -/
theorem run_class {k : ℕ} (hk : k % 2 = 1) (E t : ℕ) : ∀ j, ex k j ≤ E →
    run (k + 2 ^ (E + 1) * t) j =
      (val k j + 3 ^ ud k j * 2 ^ (E + 1 - ex k j) * t, ud k j, ex k j) := by
  intro j
  induction j with
  | zero => intro _; simp [run, val, ud, ex]
  | succ j ih =>
    intro hE
    unfold val ud ex at ih ⊢
    unfold ex at hE
    rw [run_succ] at hE
    have hle : (run k j).2.2 ≤ E := by
      revert hE; unfold st; split_ifs <;> (intro h; dsimp only at h; omega)
    have hy : (run k j).1 % 2 = 1 := val_odd hk j
    rw [run_succ, run_succ, ih hle]
    generalize run k j = p at hE hle hy ⊢
    obtain ⟨y, m, e⟩ := p
    dsimp only at hE hle hy ⊢
    by_cases hU : y % 4 = 3
    · simp only [st, ite_eq_left hU] at hE ⊢
      obtain ⟨d, hd⟩ : ∃ d, E + 1 - e = d + 2 := ⟨E - e - 1, by omega⟩
      rw [hd, show E + 1 - (e + 1) = d + 1 by omega,
        show 3 ^ m * 2 ^ (d + 2) * t = 4 * (3 ^ m * 2 ^ d * t) by ring,
        show 3 ^ (m + 1) * 2 ^ (d + 1) * t = 6 * (3 ^ m * 2 ^ d * t) by ring]
      generalize 3 ^ m * 2 ^ d * t = D
      rw [ite_eq_left (show (y + 4 * D) % 4 = 3 by omega)]
      congr 1; omega
    by_cases hD : y % 8 = 1
    · simp only [st, ite_eq_right hU, ite_eq_left hD] at hE ⊢
      obtain ⟨d, hd⟩ : ∃ d, E + 1 - e = d + 3 := ⟨E - e - 2, by omega⟩
      rw [hd, show E + 1 - (e + 2) = d + 1 by omega,
        show 3 ^ m * 2 ^ (d + 3) * t = 8 * (3 ^ m * 2 ^ d * t) by ring,
        show 3 ^ (m + 1) * 2 ^ (d + 1) * t = 6 * (3 ^ m * 2 ^ d * t) by ring]
      generalize 3 ^ m * 2 ^ d * t = D
      rw [ite_eq_right (show ¬ (y + 8 * D) % 4 = 3 by omega),
        ite_eq_left (show (y + 8 * D) % 8 = 1 by omega)]
      congr 1; omega
    · simp only [st, ite_eq_right hU, ite_eq_right hD] at hE ⊢
      obtain ⟨d, hd⟩ : ∃ d, E + 1 - e = d + 3 := ⟨E - e - 2, by omega⟩
      rw [hd, show E + 1 - (e + 2) = d + 1 by omega,
        show 3 ^ m * 2 ^ (d + 3) * t = 8 * (3 ^ m * 2 ^ d * t) by ring,
        show 3 ^ m * 2 ^ (d + 1) * t = 2 * (3 ^ m * 2 ^ d * t) by ring]
      generalize 3 ^ m * 2 ^ d * t = D
      rw [ite_eq_right (show ¬ (y + 8 * D) % 4 = 3 by omega),
        ite_eq_right (show ¬ (y + 8 * D) % 8 = 1 by omega)]
      congr 1; omega

/-- The number of odd values among T k, .., T^n k. -/
def cnt (k n : ℕ) : ℕ := ∑ i ∈ Finset.range n, if T^[i + 1] k % 2 = 1 then 1 else 0

theorem cnt_succ (k n : ℕ) :
    cnt k (n + 1) = cnt k n + if T^[n + 1] k % 2 = 1 then 1 else 0 :=
  Finset.sum_range_succ _ _

theorem cnt_mono (k : ℕ) {a b : ℕ} (h : a ≤ b) : cnt k a ≤ cnt k b :=
  Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr h)

theorem cnt_le (k n : ℕ) : cnt k n ≤ n := by
  induction n with
  | zero => simp [cnt]
  | succ n ih => rw [cnt_succ]; split_ifs <;> omega

/-- The run reads the T-path of k: T of the value is T^(e+1) k, and m counts the odd values
among T k, .., T^e k. -/
theorem path {k : ℕ} (hk : k % 2 = 1) (j : ℕ) :
    T^[ex k j + 1] k = T (val k j) ∧ ud k j = cnt k (ex k j) := by
  induction j with
  | zero => simp [ex, ud, val, run, cnt]
  | succ j ih =>
    obtain ⟨h1, h2⟩ := ih
    have hy := val_odd hk j
    have hv := val_succ k j
    have hx := ex_succ k j
    have hu := ud_succ k j
    have c1 := cnt_succ k (ex k j)
    by_cases hU : val k j % 4 = 3
    · rw [ite_eq_left hU] at hv hx hu
      have hT := step_U hU
      have hodd : T (val k j) % 2 = 1 := by rw [hT]; omega
      refine ⟨?_, ?_⟩
      · rw [hx, iterate_T, h1, hv, hT]
      · rw [hu, hx, c1, h1, ite_eq_left hodd, h2]
    have c2 : cnt k (ex k j + 2) = cnt k (ex k j + 1) +
        if T^[ex k j + 2] k % 2 = 1 then 1 else 0 := cnt_succ k (ex k j + 1)
    have t2 : T^[ex k j + 2] k = T (T (val k j)) := by
      rw [show ex k j + 2 = (ex k j + 1) + 1 from rfl, iterate_T, h1]
    rw [h1] at c1
    rw [t2] at c2
    by_cases hD : val k j % 8 = 1
    · rw [ite_eq_right hU, ite_eq_left hD] at hv hu
      rw [ite_eq_right hU] at hx
      obtain ⟨hT1, hT2⟩ := step_D hD
      rw [hT1, ite_eq_right (by omega)] at c1
      rw [hT2, ite_eq_left (by omega)] at c2
      refine ⟨?_, ?_⟩
      · rw [hx, show ex k j + 2 + 1 = ex k j + 1 + 1 + 1 from rfl, iterate_T, iterate_T, h1,
          hv, ← hT2]
      · rw [hu, hx]; omega
    · have hS : val k j % 8 = 5 := by omega
      rw [ite_eq_right hU, ite_eq_right hD] at hv hu
      rw [ite_eq_right hU] at hx
      obtain ⟨hT1, hT2, hT3⟩ := step_S hS
      rw [hT1, ite_eq_right (by omega)] at c1
      rw [hT2, ite_eq_right (by omega)] at c2
      refine ⟨?_, ?_⟩
      · rw [hx, show ex k j + 2 + 1 = ex k j + 1 + 1 + 1 from rfl, iterate_T, iterate_T, h1,
          hT3, hv]
      · rw [hu, hx]; omega

/-- The number of odd values among x, .., T^(i-1) x. -/
def c0 (x i : ℕ) : ℕ := ∑ l ∈ Finset.range i, if T^[l] x % 2 = 1 then 1 else 0

/-- Terras: T^i (x + 2^N) = T^i x + 3^(c0 x i) 2^(N-i) for i ≤ N. -/
theorem shift (x N : ℕ) : ∀ i ≤ N, T^[i] (x + 2 ^ N) = T^[i] x + 3 ^ c0 x i * 2 ^ (N - i) := by
  intro i
  induction i with
  | zero => intro _; simp [c0]
  | succ i ih =>
    intro hi
    rw [iterate_T, iterate_T, ih (by omega)]
    obtain ⟨d, hd⟩ : ∃ d, N - i = d + 1 := ⟨N - i - 1, by omega⟩
    rw [hd, show N - (i + 1) = d by omega]
    have hc : c0 x (i + 1) = c0 x i + if T^[i] x % 2 = 1 then 1 else 0 :=
      Finset.sum_range_succ _ _
    rw [hc, show 3 ^ c0 x i * 2 ^ (d + 1) = 2 * (3 ^ c0 x i * 2 ^ d) by ring]
    generalize T^[i] x = y
    generalize c0 x i = c
    by_cases hy : y % 2 = 1
    · rw [ite_eq_left hy, show 3 ^ (c + 1) * 2 ^ d = 3 * (3 ^ c * 2 ^ d) by ring]
      generalize 3 ^ c * 2 ^ d = D
      rw [T_odd hy, T_odd (by omega)]; omega
    · rw [ite_eq_right hy, add_zero]
      generalize 3 ^ c * 2 ^ d = D
      rw [T_even (by omega), T_even (by omega)]; omega

theorem cnt_pair (x n : ℕ) : cnt (x + 2 ^ (n + 1)) n = cnt x n := by
  unfold cnt
  apply Finset.sum_congr rfl
  intro l hl
  rw [Finset.mem_range] at hl
  rw [shift x (n + 1) (l + 1) (by omega)]
  obtain ⟨d, hd⟩ : ∃ d, n + 1 - (l + 1) = d + 1 := ⟨n - l - 1, by omega⟩
  rw [hd, show 3 ^ c0 x (l + 1) * 2 ^ (d + 1) = 2 * (3 ^ c0 x (l + 1) * 2 ^ d) by ring]
  generalize T^[l + 1] x = y
  generalize 3 ^ c0 x (l + 1) * 2 ^ d = D
  simp only [show (y + 2 * D) % 2 = y % 2 by omega]

theorem last_flip (x n : ℕ) :
    T^[n + 1] (x + 2 ^ (n + 1)) % 2 = 1 ↔ ¬ T^[n + 1] x % 2 = 1 := by
  rw [shift x (n + 1) (n + 1) le_rfl, Nat.sub_self, pow_zero, mul_one]
  have h3 : 3 ^ c0 x (n + 1) % 2 = 1 := by rw [Nat.pow_mod]; norm_num
  generalize 3 ^ c0 x (n + 1) = Q at h3
  omega

/-- The number of odd x < 2^(n+1) with m odd values among T x, .., T^n x. -/
def oc (n m : ℕ) : ℕ :=
  ∑ x ∈ Finset.range (2 ^ (n + 1)), if x % 2 = 1 ∧ cnt x n = m then 1 else 0

/-- It is binomial. -/
theorem oc_eq (n : ℕ) : ∀ m, oc n m = n.choose m := by
  induction n with
  | zero =>
    intro m
    cases m
    · decide
    · simp [oc, cnt]
  | succ n ih =>
    intro m
    unfold oc
    rw [show 2 ^ (n + 1 + 1) = 2 ^ (n + 1) + 2 ^ (n + 1) by ring, Finset.sum_range_add,
      ← Finset.sum_add_distrib]
    have key : ∀ x ∈ Finset.range (2 ^ (n + 1)),
        ((if x % 2 = 1 ∧ cnt x (n + 1) = m then 1 else 0) +
          if (2 ^ (n + 1) + x) % 2 = 1 ∧ cnt (2 ^ (n + 1) + x) (n + 1) = m then 1 else 0) =
        (if x % 2 = 1 ∧ cnt x n = m then 1 else 0) +
          if x % 2 = 1 ∧ cnt x n + 1 = m then 1 else 0 := by
      intro x _
      rw [add_comm (2 ^ (n + 1)) x, cnt_succ, cnt_succ, cnt_pair]
      have hf := last_flip x n
      have hp : (x + 2 ^ (n + 1)) % 2 = x % 2 := by
        rw [pow_succ]; generalize 2 ^ n = P; omega
      rw [hp]
      by_cases h1 : T^[n + 1] x % 2 = 1
      · have h2 : ¬ T^[n + 1] (x + 2 ^ (n + 1)) % 2 = 1 := fun h => (hf.mp h) h1
        rw [ite_eq_left h1, ite_eq_right h2]
        split_ifs <;> omega
      · have h2 : T^[n + 1] (x + 2 ^ (n + 1)) % 2 = 1 := hf.mpr h1
        rw [ite_eq_right h1, ite_eq_left h2]
        split_ifs <;> omega
    rw [Finset.sum_congr rfl key, Finset.sum_add_distrib]
    cases m with
    | zero =>
      have h0 : (∑ x ∈ Finset.range (2 ^ (n + 1)),
          if x % 2 = 1 ∧ cnt x n + 1 = 0 then 1 else 0) = 0 :=
        Finset.sum_eq_zero (fun x _ => ite_eq_right (by omega))
      rw [h0, add_zero]
      change oc n 0 = _
      rw [ih]; simp
    | succ m =>
      have hm : ∀ x, (x % 2 = 1 ∧ cnt x n + 1 = m + 1) ↔ (x % 2 = 1 ∧ cnt x n = m) :=
        fun x => by omega
      simp only [hm]
      change oc n (m + 1) + oc n m = _
      rw [ih, ih, Nat.choose_succ_succ']; omega

/-- Counting the odd k < 2^(E+1) by their m among T k, .., T^E k. -/
theorem count_eq (E : ℕ) :
    (∑ k ∈ Finset.range (2 ^ (E + 1)), if k % 2 = 1 ∧ 2 ^ E ≤ 2 * 3 ^ cnt k E then 1 else 0) =
      ∑ m ∈ Finset.range (E + 1), if 2 ^ E ≤ 2 * 3 ^ m then E.choose m else 0 := by
  have hs : ∀ m ∈ Finset.range (E + 1), (if 2 ^ E ≤ 2 * 3 ^ m then E.choose m else 0) =
      ∑ k ∈ Finset.range (2 ^ (E + 1)),
        if k % 2 = 1 ∧ cnt k E = m ∧ 2 ^ E ≤ 2 * 3 ^ m then 1 else 0 := by
    intro m _
    rw [← oc_eq E m, oc]
    split_ifs with hP
    · apply Finset.sum_congr rfl; intro k _; simp [hP]
    · symm; apply Finset.sum_eq_zero; intro k _; simp [hP]
  rw [Finset.sum_congr rfl hs, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_eq_single (cnt k E)]
  · simp only [true_and]
  · intro m _ hm
    rw [ite_eq_right]
    rintro ⟨-, h, -⟩
    exact hm h.symm
  · intro h
    exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le (cnt_le k E))) h

theorem ex_le_succ (k j : ℕ) : ex k j + 1 ≤ ex k (j + 1) ∧ ex k (j + 1) ≤ ex k j + 2 := by
  rw [ex_succ]; split_ifs <;> omega

theorem le_ex (k j : ℕ) : j ≤ ex k j := by
  induction j with
  | zero => simp
  | succ j ih => have := ex_le_succ k j; omega

/-- If no word of e ≤ E has 3^m < 2^e, then 2^E ≤ 2 3^m for m among T k, .., T^E k. -/
theorem unstopped_tail {k E : ℕ} (hk : k % 2 = 1)
    (hU : ∀ j, ex k j ≤ E → 2 ^ ex k j ≤ 3 ^ ud k j) : 2 ^ E ≤ 2 * 3 ^ cnt k E := by
  classical
  have hex : ∃ J, E < ex k J := ⟨E + 1, by have := le_ex k (E + 1); omega⟩
  obtain ⟨J, hJ, hmin⟩ : ∃ J, E < ex k J ∧ ∀ j < J, ¬ E < ex k j :=
    ⟨Nat.find hex, Nat.find_spec hex, fun j hj => Nat.find_min hex hj⟩
  have hJ0 : J ≠ 0 := by rintro rfl; simp [ex, run] at hJ
  obtain ⟨j, rfl⟩ : ∃ j, J = j + 1 := ⟨J - 1, by omega⟩
  have hj : ex k j ≤ E := not_lt.mp (hmin j (by omega))
  have h2 := ex_le_succ k j
  have hu := hU j hj
  rw [(path hk j).2] at hu
  have hm := cnt_mono k hj
  calc 2 ^ E ≤ 2 ^ (ex k j + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ = 2 * 2 ^ ex k j := by ring
    _ ≤ 2 * 3 ^ cnt k (ex k j) := Nat.mul_le_mul_left 2 hu
    _ ≤ 2 * 3 ^ cnt k E := Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right (by norm_num) hm)

theorem five_q_le {E m : ℕ} (h : 2 ^ E ≤ 2 * 3 ^ m) : 5 * ((E - 1) / 8) ≤ m := by
  by_contra hc
  push Not at hc
  set q := (E - 1) / 8 with hq
  have h1 : 2 * 3 ^ m < 3 ^ (m + 1) := by
    rw [pow_succ]; have := Nat.one_le_pow m 3 (by norm_num); omega
  have h2 : 3 ^ (m + 1) ≤ 3 ^ (5 * q) := Nat.pow_le_pow_right (by norm_num) hc
  have h3 : 3 ^ (5 * q) ≤ 2 ^ (8 * q) := by
    rw [pow_mul, pow_mul]; exact Nat.pow_le_pow_left (by norm_num) q
  have h4 : 2 ^ (8 * q) ≤ 2 ^ E := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem weight_le {q m E : ℕ} (h1 : q ≤ m) (h2 : m ≤ E) :
    3 ^ q * 2 ^ (E - q) ≤ 3 ^ m * 2 ^ (E - m) := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le h1
  rw [show E - q = a + (E - (q + a)) by omega, pow_add, pow_add]
  have : 2 ^ a ≤ 3 ^ a := Nat.pow_le_pow_left (by norm_num) a
  calc 3 ^ q * (2 ^ a * 2 ^ (E - (q + a))) = 3 ^ q * 2 ^ (E - (q + a)) * 2 ^ a := by ring
    _ ≤ 3 ^ q * 2 ^ (E - (q + a)) * 3 ^ a := Nat.mul_le_mul_left _ this
    _ = 3 ^ q * 3 ^ a * 2 ^ (E - (q + a)) := by ring

/-- The tail, weighted: each m in it has 3^m 2^(E-m) ≥ 3^(5q) 2^(E-5q), and these weights sum
to 5^E. -/
theorem tail_mul (E : ℕ) :
    (∑ m ∈ Finset.range (E + 1), if 2 ^ E ≤ 2 * 3 ^ m then E.choose m else 0) *
      (3 ^ (5 * ((E - 1) / 8)) * 2 ^ (E - 5 * ((E - 1) / 8))) ≤ 5 ^ E := by
  have h5 : 5 ^ E = ∑ m ∈ Finset.range (E + 1), 3 ^ m * 2 ^ (E - m) * E.choose m := by
    have := add_pow (3 : ℕ) 2 E
    simp only [Nat.cast_id] at this
    rw [← this]
  rw [h5, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro m hm
  rw [Finset.mem_range] at hm
  split_ifs with h
  · have := weight_le (five_q_le h) (by omega : m ≤ E)
    calc E.choose m * (3 ^ (5 * ((E - 1) / 8)) * 2 ^ (E - 5 * ((E - 1) / 8)))
        ≤ E.choose m * (3 ^ m * 2 ^ (E - m)) := Nat.mul_le_mul_left _ this
      _ = _ := by ring
  · simp

/-- Bernoulli: B^q (B + q d) ≤ B (B + d)^q. -/
theorem bern (B d q : ℕ) : B ^ q * (B + q * d) ≤ B * (B + d) ^ q := by
  induction q with
  | zero => simp
  | succ q ih =>
    have h1 : B ^ q ≤ (B + d) ^ q := Nat.pow_le_pow_left (by omega) q
    calc B ^ (q + 1) * (B + (q + 1) * d) = B * (B ^ q * (B + q * d)) + B * B ^ q * d := by ring
      _ ≤ B * (B * (B + d) ^ q) + B * (B + d) ^ q * d := by gcongr
      _ = B * (B + d) ^ (q + 1) := by ring

open Classical in
/-- The density: for every M, from some E on, at most a share 1/M of the 2^E odd k
(mod 2^(E+1)) has no word of e ≤ E with 3^m < 2^e. -/
theorem density (M : ℕ) : ∃ E0, ∀ E ≥ E0,
    M * ((Finset.range (2 ^ (E + 1))).filter
      (fun k => k % 2 = 1 ∧ ∀ j, ex k j ≤ E → 2 ^ ex k j ≤ 3 ^ ud k j)).card ≤ 2 ^ E := by
  obtain ⟨q0, hq0⟩ : ∃ q0, ∀ q ≥ q0, M * 5 ^ 8 * 390625 ^ q ≤ 497664 ^ q := by
    refine ⟨M * 5 ^ 8 * 390625, fun q hq => ?_⟩
    have h1 : M * 5 ^ 8 * 390625 ^ q * 390625 ≤ 497664 ^ q * 390625 := by
      calc M * 5 ^ 8 * 390625 ^ q * 390625 = (M * 5 ^ 8 * 390625) * 390625 ^ q := by ring
        _ ≤ q * 390625 ^ q := Nat.mul_le_mul_right _ hq
        _ ≤ 390625 ^ q * (390625 + q * 107039) := by
          generalize 390625 ^ q = X; nlinarith [Nat.zero_le (q * X)]
        _ ≤ 390625 * (390625 + 107039) ^ q := bern 390625 107039 q
        _ = 497664 ^ q * 390625 := by rw [mul_comm]
    exact Nat.le_of_mul_le_mul_right h1 (by norm_num)
  refine ⟨8 * q0 + 1, fun E hE => ?_⟩
  have htail := tail_mul E
  set q := (E - 1) / 8 with hq
  have hqq : q0 ≤ q := by omega
  have hw : 0 < 3 ^ (5 * q) * 2 ^ (E - 5 * q) := by positivity
  have hcard : ((Finset.range (2 ^ (E + 1))).filter
      (fun k => k % 2 = 1 ∧ ∀ j, ex k j ≤ E → 2 ^ ex k j ≤ 3 ^ ud k j)).card ≤
      ∑ m ∈ Finset.range (E + 1), if 2 ^ E ≤ 2 * 3 ^ m then E.choose m else 0 := by
    rw [Finset.card_filter, ← count_eq]
    apply Finset.sum_le_sum
    intro k _
    by_cases h1 : k % 2 = 1 ∧ ∀ j, ex k j ≤ E → 2 ^ ex k j ≤ 3 ^ ud k j
    · rw [ite_eq_left h1, ite_eq_left ⟨h1.1, unstopped_tail h1.1 h1.2⟩]
    · rw [ite_eq_right h1]; exact Nat.zero_le _
  have hpow : M * 5 ^ E ≤ 2 ^ E * (3 ^ (5 * q) * 2 ^ (E - 5 * q)) := by
    have e1 : 5 ^ E ≤ 5 ^ 8 * 390625 ^ q := by
      calc 5 ^ E ≤ 5 ^ (8 + 8 * q) := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 5 ^ 8 * 390625 ^ q := by rw [pow_add, pow_mul]; norm_num
    have e2 : 497664 ^ q ≤ 2 ^ E * (3 ^ (5 * q) * 2 ^ (E - 5 * q)) := by
      calc 497664 ^ q = 2 ^ (11 * q) * 3 ^ (5 * q) := by
            rw [pow_mul, pow_mul, ← mul_pow]; norm_num
        _ ≤ 2 ^ (E + (E - 5 * q)) * 3 ^ (5 * q) :=
            Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (by omega))
        _ = _ := by rw [pow_add]; ring
    calc M * 5 ^ E ≤ M * (5 ^ 8 * 390625 ^ q) := Nat.mul_le_mul_left _ e1
      _ = M * 5 ^ 8 * 390625 ^ q := by ring
      _ ≤ 497664 ^ q := hq0 q hqq
      _ ≤ _ := e2
  generalize ((Finset.range (2 ^ (E + 1))).filter
      (fun k => k % 2 = 1 ∧ ∀ j, ex k j ≤ E → 2 ^ ex k j ≤ 3 ^ ud k j)).card = C at hcard ⊢
  generalize (∑ m ∈ Finset.range (E + 1), if 2 ^ E ≤ 2 * 3 ^ m then E.choose m else 0) = S
    at hcard htail
  generalize 3 ^ (5 * q) * 2 ^ (E - 5 * q) = W at hw htail hpow
  have : M * C * W ≤ 2 ^ E * W :=
    calc M * C * W ≤ M * (S * W) := by
          rw [mul_assoc]; exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hcard)
      _ ≤ M * 5 ^ E := Nat.mul_le_mul_left _ htail
      _ ≤ 2 ^ E * W := hpow
  exact Nat.le_of_mul_le_mul_right this hw

end A349414Run
