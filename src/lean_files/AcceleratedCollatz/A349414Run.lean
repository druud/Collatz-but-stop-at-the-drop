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

end A349414Run
