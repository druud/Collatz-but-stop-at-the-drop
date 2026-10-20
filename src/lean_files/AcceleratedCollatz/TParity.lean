-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.AdmissibleLength

/-!
  Division-free form of the standard map T (x ↦ (3x+1)/2 for odd x, x/2 for
  even x) and its parity bits. For a parity sequence s, `affineNum s j N` applies
  s to the scaled value N = 2^j T^j(x): an odd step N ↦ 3N + 2^j, an even
  step leaves N unchanged. Main result `tBits_eq_iff`: the first |s| parity
  bits of x are s iff 2^|s| divides 3^(order s) x + rho s.
-/

namespace AcceleratedCollatz

/-- Standard map T. -/
def tStep (x : ℕ) : ℕ := if x % 2 = 1 then (3 * x + 1) / 2 else x / 2

/-- First n T-parity bits of x (true = odd). -/
def tBits : ℕ → ℕ → List Bool
  | _, 0 => []
  | x, n + 1 => decide (x % 2 = 1) :: tBits (tStep x) n

/-- Scaled value after applying t from position j to N. -/
def affineNum : List Bool → ℕ → ℕ → ℕ
  | [], _, N => N
  | b :: t, j, N => affineNum t (j + 1) (if b then 3 * N + 2 ^ j else N)

/-- Remainder term: 2^|s| T^|s|(x) = 3^(order s) x + rho s. -/
def rho (s : List Bool) : ℕ := affineNum s 0 0

/-- Gap numerator: 2^|s| - 3^(order s). -/
abbrev d_23 (s : List Bool) : ℕ := 2 ^ s.length - 3 ^ order s

/-- Order of b :: t. -/
theorem order_cons (b : Bool) (t : List Bool) :
    order (b :: t) = order t + (if b then 1 else 0) := by
  grind [order]

theorem affineNum_linear (t : List Bool) (j N : ℕ) :
    affineNum t j N = 3 ^ order t * N + affineNum t j 0 := by
  induction t generalizing j N with
  | nil =>
    simp [affineNum, order]
  | cons b t ih =>
    rw [order_cons]
    cases b with
    | true =>
      simp only [affineNum, ↓reduceIte]
      rw [ih (j + 1) (3 * N + 2 ^ j), ih (j + 1) (3 * 0 + 2 ^ j)]
      ring
    | false =>
      simp only [affineNum, Bool.false_eq_true, ↓reduceIte]
      rw [ih (j + 1) N]
      simp

theorem pow_dvd_affineNum_zero (t : List Bool) (j : ℕ) : 2 ^ j ∣ affineNum t j 0 := by
  induction t generalizing j with
  | nil =>
    simp [affineNum]
  | cons b t ih =>
    have hj : 2 ^ j ∣ 2 ^ (j + 1) := pow_dvd_pow 2 (by omega)
    cases b with
    | true =>
      simp only [affineNum]
      rw [affineNum_linear]
      apply dvd_add
      · simp
      · exact hj.trans (ih (j + 1))
    | false =>
      simp only [affineNum]
      exact hj.trans (ih (j + 1))

/-- A power of 2 dividing the final scaled value divides the start value. -/
theorem pow_dvd_of_pow_dvd_affineNum (t : List Bool) (j N : ℕ) (h : 2 ^ j ∣ affineNum t j N) :
    2 ^ j ∣ N := by
  rw [affineNum_linear] at h
  have h3 : 2 ^ j ∣ 3 ^ order t * N := (Nat.dvd_add_left (pow_dvd_affineNum_zero t j)).mp h
  have hcop : Nat.Coprime (2 ^ j) (3 ^ order t) := Nat.Coprime.pow j (order t) (by decide)
  exact hcop.dvd_of_dvd_mul_left h3

/-- One scaled step: N = 2^j y goes to 2^(j+1) T(y). -/
theorem scaled_tStep (j y : ℕ) :
    (if decide (y % 2 = 1) = true then 3 * (2 ^ j * y) + 2 ^ j else 2 ^ j * y)
      = 2 ^ (j + 1) * tStep y := by
  unfold tStep
  by_cases h : y % 2 = 1
  · have h2 : 2 * ((3 * y + 1) / 2) = 3 * y + 1 := by omega
    simp only [h, decide_true, ↓reduceIte]
    rw [pow_succ, mul_assoc, h2]
    ring
  · have h2 : 2 * (y / 2) = y := by omega
    simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte]
    rw [pow_succ, mul_assoc, h2]

/-- The parity bit at position j is forced by 2^(j+1) dividing the next value. -/
theorem bit_of_dvd (b : Bool) (y j : ℕ)
    (h : 2 ^ (j + 1) ∣ (if b then 3 * (2 ^ j * y) + 2 ^ j else 2 ^ j * y)) :
    decide (y % 2 = 1) = b := by
  have hpos : 0 < 2 ^ j := by positivity
  cases b with
  | true =>
    simp only [↓reduceIte] at h
    rw [show 3 * (2 ^ j * y) + 2 ^ j = 2 ^ j * (3 * y + 1) by ring, pow_succ] at h
    have h2 : 2 ∣ 3 * y + 1 := Nat.dvd_of_mul_dvd_mul_left hpos h
    simp only [decide_eq_true_eq]
    omega
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    rw [pow_succ] at h
    have h2 : 2 ∣ y := Nat.dvd_of_mul_dvd_mul_left hpos h
    simp only [decide_eq_false_iff_not]
    omega

/-- N-form of the trajectory: applying x's own parity bits to 2^j x. -/
theorem affineNum_tBits (n j y : ℕ) :
    affineNum (tBits y n) j (2 ^ j * y) = 2 ^ (j + n) * tStep^[n] y := by
  induction n generalizing j y with
  | zero =>
    simp [tBits, affineNum]
  | succ n ih =>
    simp only [tBits, affineNum]
    rw [scaled_tStep, ih (j + 1) (tStep y), Function.iterate_succ_apply]
    ring_nf

/-- Terras direction: 2^(j+|t|) dividing the final scaled value forces the bits. -/
theorem tBits_of_dvd : ∀ (t : List Bool) (j y : ℕ),
    2 ^ (j + t.length) ∣ affineNum t j (2 ^ j * y) → tBits y t.length = t
  | [], _, _, _ => rfl
  | b :: t, j, y, h => by
    have hlen : j + (b :: t).length = j + 1 + t.length := by
      simp only [List.length_cons]
      omega
    rw [hlen] at h
    simp only [affineNum] at h
    have h1 : 2 ^ (j + 1) ∣
        affineNum t (j + 1) (if b then 3 * (2 ^ j * y) + 2 ^ j else 2 ^ j * y) :=
      (pow_dvd_pow 2 (by omega)).trans h
    have hb := bit_of_dvd b y j (pow_dvd_of_pow_dvd_affineNum t (j + 1) _ h1)
    have hsc := scaled_tStep j y
    rw [hb] at hsc
    rw [hsc] at h
    have ih := tBits_of_dvd t (j + 1) (tStep y) h
    simp only [List.length_cons, tBits]
    rw [hb, ih]

/-- 2^n T^n(x) = 3^o x + rho, with o and rho taken from x's own parity bits. -/
theorem tStep_iterate_nForm (n x : ℕ) :
    2 ^ n * tStep^[n] x = 3 ^ order (tBits x n) * x + rho (tBits x n) := by
  have h := affineNum_tBits n 0 x
  rw [affineNum_linear] at h
  simp only [pow_zero, one_mul, zero_add] at h
  exact h.symm

/-- Parity sequence s ⟺ 2^|s| ∣ 3^(order s) x + rho s. -/
theorem tBits_eq_iff (s : List Bool) (x : ℕ) :
    tBits x s.length = s ↔ 2 ^ s.length ∣ 3 ^ order s * x + rho s := by
  constructor
  · intro h
    have hN := tStep_iterate_nForm s.length x
    rw [h] at hN
    rw [← hN]
    exact dvd_mul_right _ _
  · intro h
    apply tBits_of_dvd s 0 x
    rw [affineNum_linear]
    simpa [rho] using h

@[simp]
theorem tStep_odd (y : ℕ) (h : y % 2 = 1) : tStep y = (3 * y + 1) / 2 := by
  simp [tStep, h]

@[simp]
theorem tStep_even (y : ℕ) (h : y % 2 ≠ 1) : tStep y = y / 2 := by
  simp [tStep, h]

theorem tBits_add (x a b : ℕ) :
    tBits x (a + b) = tBits x a ++ tBits (tStep^[a] x) b := by
  induction a generalizing x with
  | zero =>
    simp [tBits]
  | succ a ih =>
    rw [Nat.add_right_comm]
    simp only [tBits, List.cons_append]
    rw [ih (tStep x), Function.iterate_succ_apply]

theorem tBits_replicate (b : Bool) :
    ∀ (n x : ℕ), (∀ k < n, decide (tStep^[k] x % 2 = 1) = b) →
      tBits x n = List.replicate n b
  | 0, _, _ => rfl
  | n + 1, x, h => by
    have h0 : decide (x % 2 = 1) = b := h 0 (by omega)
    have ht : ∀ k < n, decide (tStep^[k] (tStep x) % 2 = 1) = b := by
      intro k hk
      have hk' := h (k + 1) (by omega)
      rwa [Function.iterate_succ_apply] at hk'
    simp only [tBits, List.replicate_succ]
    rw [h0, tBits_replicate b n (tStep x) ht]

@[simp]
theorem length_tBits (x n : ℕ) : (tBits x n).length = n := by
  induction n generalizing x with
  | zero =>
    simp [tBits]
  | succ n ih =>
    simp [tBits, ih]

theorem tBits_take (x n m : ℕ) (hm : m ≤ n) : (tBits x n).take m = tBits x m := by
  induction n generalizing x m with
  | zero =>
    have hm0 : m = 0 := by omega
    subst hm0
    simp [tBits]
  | succ n ih =>
    cases m with
    | zero =>
      simp [tBits]
    | succ m =>
      simp only [tBits, List.take_succ_cons]
      rw [ih (tStep x) m (by omega)]

/-- Odd run: with x + 1 = 2^v s, T^k(x) + 1 = 3^k 2^(v-k) s for k ≤ v. -/
theorem tStep_iterate_odd_run (x v s : ℕ) (h : x + 1 = 2 ^ v * s) :
    ∀ k ≤ v, tStep^[k] x + 1 = 3 ^ k * 2 ^ (v - k) * s := by
  intro k
  induction k with
  | zero =>
    intro _
    simpa using h
  | succ k ih =>
    intro hk
    have ih' := ih (by omega)
    have hv : 2 ^ (v - k) = 2 * 2 ^ (v - (k + 1)) := by
      rw [← pow_succ']
      grind
    have ih'' : tStep^[k] x + 1 = 2 * (3 ^ k * 2 ^ (v - (k + 1)) * s) := by
      grind
    have hc : 3 ^ (k + 1) * 2 ^ (v - (k + 1)) * s = 3 * (3 ^ k * 2 ^ (v - (k + 1)) * s) := by
      ring
    rw [Function.iterate_succ_apply', hc]
    generalize 3 ^ k * 2 ^ (v - (k + 1)) * s = c at ih'' ⊢
    have hodd : tStep^[k] x % 2 = 1 := by omega
    rw [tStep_odd _ hodd]
    omega

theorem tStep_iterate_of_pow_dvd (x k : ℕ) (h : 2 ^ k ∣ x) :
    ∀ j ≤ k, tStep^[j] x = x / 2 ^ j := by
  intro j
  induction j with
  | zero =>
    intro _
    simp
  | succ j ih =>
    intro hj
    rw [Function.iterate_succ_apply', ih (by omega)]
    obtain ⟨c, hc⟩ := (pow_dvd_pow 2 hj).trans h
    have e1 : x / 2 ^ j = 2 * c := by
      rw [hc, show 2 ^ (j + 1) * c = 2 ^ j * (2 * c) by ring]
      exact Nat.mul_div_cancel_left _ (by positivity)
    have e2 : x / 2 ^ (j + 1) = c := by
      rw [hc]
      exact Nat.mul_div_cancel_left _ (by positivity)
    have hev : 2 * c % 2 ≠ 1 := by omega
    rw [e1, e2, tStep_even _ hev]
    omega

theorem div_pow_even (x j k : ℕ) (hj : j < k) (h : 2 ^ k ∣ x) : x / 2 ^ j % 2 = 0 := by
  obtain ⟨c, hc⟩ := (pow_dvd_pow 2 hj).trans h
  rw [hc, show 2 ^ (j + 1) * c = 2 ^ j * (2 * c) by ring,
    Nat.mul_div_cancel_left _ (by positivity)]
  omega

end AcceleratedCollatz
