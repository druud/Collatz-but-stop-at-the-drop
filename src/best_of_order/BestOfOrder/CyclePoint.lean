-- SPDX-License-Identifier: MIT
import BestOfOrder.Bridge
import Mathlib.Algebra.Order.Field.Basic

/-!
  The cycle point (paper, Chapter 4 and Theorem A). For a word s of length L with n ones and
  constant rho, the cycle point is x* = rho / (2^L - 3^n), the rational fixed point of
  x ↦ (3^n x + rho) / 2^L. For every member x > 0 of the word's class:
  1 - T^L(x)/x = (1 - 3^n/2^L)(1 - x*/x) (`one_sub_ratio`), so between two words of one length
  and Order the ratio is higher exactly when x*/x is (`ratio_lt_ratio_iff`), and x drops at the
  end of the word exactly when x* < x (`drops_iff`). Within a class the ratio falls as x grows
  (`ratio_lt_of_lt`). The points x*_l = (3^(w_l) x* + rho_l)/2^l of the rational cycle close at
  l = L (`cyclePt_length`) and stay above x* on every proper prefix of an admissible word
  (`cyclePoint_lt_cyclePt`); T^l(x) = x*_l + (x - x*) 3^(w_l)/2^l (`iterate_eq_split`); the
  cycle point of a nonempty proper prefix as a word of its own is negative
  (`prefix_cyclePoint_neg`).
-/

namespace BestOfOrder

open AcceleratedCollatz

/-- The cycle point rho / (2^L - 3^n) of a word. -/
def cyclePoint (s : List Bool) : ℚ := rho s / (2 ^ s.length - 3 ^ order s)

/-- The point x*_l of the rational cycle, after the first l letters. -/
def cyclePt (s : List Bool) (l : ℕ) : ℚ :=
  (3 ^ order (s.take l) * cyclePoint s + rho (s.take l)) / 2 ^ l

/-- For a member x of the class of s: 2^L T^L(x) = 3^n x + rho, in ℚ. -/
theorem affine_q {s : List Bool} {x : ℕ} (hx : tBits x s.length = s) :
    (2 : ℚ) ^ s.length * (tStep^[s.length] x : ℚ) = 3 ^ order s * x + rho s := by
  have h := affine s.length x
  rw [hx] at h
  exact_mod_cast h

/-- Theorem A: 1 - T^L(x)/x = (1 - 3^n/2^L)(1 - x*/x). -/
theorem one_sub_ratio {s : List Bool} {x : ℕ} (hx : tBits x s.length = s) (hx0 : 0 < x)
    (hd : 3 ^ order s < 2 ^ s.length) :
    1 - (tStep^[s.length] x : ℚ) / x =
      (1 - (3 : ℚ) ^ order s / 2 ^ s.length) * (1 - cyclePoint s / x) := by
  have h := affine_q hx
  have hx' : (x : ℚ) ≠ 0 := by positivity
  have hd' : ((2 : ℚ) ^ s.length - 3 ^ order s) ≠ 0 := by
    have : ((3 : ℚ) ^ order s) < 2 ^ s.length := by exact_mod_cast hd
    linarith
  have h2 : (2 : ℚ) ^ s.length ≠ 0 := by positivity
  have hT : (tStep^[s.length] x : ℚ) = (3 ^ order s * x + rho s) / 2 ^ s.length := by
    rw [eq_div_iff h2, mul_comm, h]
  rw [hT, cyclePoint]
  field_simp
  ring

/-- x drops at the end of its word exactly when it lies above the cycle point. -/
theorem drops_iff {s : List Bool} {x : ℕ} (hx : tBits x s.length = s)
    (hd : 3 ^ order s < 2 ^ s.length) :
    tStep^[s.length] x < x ↔ cyclePoint s < x := by
  have h := affine_q hx
  have hd' : (0 : ℚ) < 2 ^ s.length - 3 ^ order s := by
    have : ((3 : ℚ) ^ order s) < 2 ^ s.length := by exact_mod_cast hd
    linarith
  have h2 : (0 : ℚ) < 2 ^ s.length := by positivity
  rw [cyclePoint, div_lt_iff₀ hd']
  constructor
  · intro hlt
    have hq : (tStep^[s.length] x : ℚ) < x := by exact_mod_cast hlt
    nlinarith
  · intro hlt
    have hq : (tStep^[s.length] x : ℚ) < x := by nlinarith
    exact_mod_cast hq

/-- Theorem A, the best: for two words of one length and one Order, the ratio is higher exactly
    when x*/x is. -/
theorem ratio_lt_ratio_iff {s s' : List Bool} {x x' : ℕ} (hx : tBits x s.length = s)
    (hx' : tBits x' s'.length = s') (hx0 : 0 < x) (hx0' : 0 < x')
    (hL : s'.length = s.length) (hn : order s' = order s)
    (hd : 3 ^ order s < 2 ^ s.length) :
    (tStep^[s.length] x : ℚ) / x < (tStep^[s.length] x' : ℚ) / x' ↔
      cyclePoint s / x < cyclePoint s' / x' := by
  have h1 := one_sub_ratio hx hx0 hd
  have h2 := one_sub_ratio hx' hx0' (by rw [hn, hL]; exact hd)
  rw [hL, hn] at h2
  have hk : (0 : ℚ) < 1 - 3 ^ order s / 2 ^ s.length := by
    have hlt : ((3 : ℚ) ^ order s) < 2 ^ s.length := by exact_mod_cast hd
    have h2p : (0 : ℚ) < 2 ^ s.length := by positivity
    rw [sub_pos, div_lt_iff₀ h2p, one_mul]
    exact hlt
  constructor
  · intro h
    by_contra hc
    have hc' := not_lt.mp hc
    have := mul_le_mul_of_nonneg_left (sub_le_sub_left hc' 1) hk.le
    linarith
  · intro h
    have := mul_lt_mul_of_pos_left (sub_lt_sub_left h 1) hk
    linarith

/-- Lemma 2.5: within a class of positive Order, the ratio falls as x grows. -/
theorem ratio_lt_of_lt {s : List Bool} {x y : ℕ} (hx : tBits x s.length = s)
    (hy : tBits y s.length = s) (hx0 : 0 < x) (hxy : x < y) (hn : 0 < order s) :
    (tStep^[s.length] y : ℚ) / y < (tStep^[s.length] x : ℚ) / x := by
  have h1 := affine_q hx
  have h2 := affine_q hy
  have hr : (0 : ℚ) < rho s := by exact_mod_cast (rho_pos_iff s).mpr hn
  have hx' : (0 : ℚ) < x := by exact_mod_cast hx0
  have hy' : (0 : ℚ) < y := by exact_mod_cast hx0.trans hxy
  have hxy' : (x : ℚ) < y := by exact_mod_cast hxy
  have hp : (0 : ℚ) < 2 ^ s.length := by positivity
  rw [div_lt_div_iff₀ hy' hx']
  have key : (2 : ℚ) ^ s.length * ((tStep^[s.length] y : ℚ) * x) <
      2 ^ s.length * ((tStep^[s.length] x : ℚ) * y) := by
    have e1 : (2 : ℚ) ^ s.length * ((tStep^[s.length] y : ℚ) * x) =
        (3 ^ order s * y + rho s) * x := by rw [← h2]; ring
    have e2 : (2 : ℚ) ^ s.length * ((tStep^[s.length] x : ℚ) * y) =
        (3 ^ order s * x + rho s) * y := by rw [← h1]; ring
    rw [e1, e2]
    nlinarith
  exact lt_of_mul_lt_mul_left key hp.le

/-- A prefix with 2^l < 3^w, l ≥ 1, has a one. -/
theorem order_pos_of_pow_lt {t : List Bool} {l : ℕ} (hl1 : 1 ≤ l) (hp : 2 ^ l < 3 ^ order t) :
    0 < order t := by
  rcases Nat.eq_zero_or_pos (order t) with hz | hz
  · rw [hz, pow_zero] at hp
    have : 2 ≤ 2 ^ l := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ l := Nat.pow_le_pow_right (by norm_num) hl1
    omega
  · exact hz

/-- The rational cycle closes: x*_L = x*. -/
theorem cyclePt_length {s : List Bool} (hd : 3 ^ order s < 2 ^ s.length) :
    cyclePt s s.length = cyclePoint s := by
  have hd' : ((2 : ℚ) ^ s.length - 3 ^ order s) ≠ 0 := by
    have : ((3 : ℚ) ^ order s) < 2 ^ s.length := by exact_mod_cast hd
    linarith
  have h2 : (2 : ℚ) ^ s.length ≠ 0 := by positivity
  rw [cyclePt, List.take_length, cyclePoint]
  field_simp
  ring

/-- Proposition 4.4: on every nonempty proper prefix of an admissible word, the cycle point lies
    strictly below the point of its cycle: x* is the strict minimum of its cycle. -/
theorem cyclePoint_lt_cyclePt {s : List Bool} (hA : Admissible s) {l : ℕ} (hl1 : 1 ≤ l)
    (hlL : l < s.length) : cyclePoint s < cyclePt s l := by
  obtain ⟨hpre, hfin⟩ := (admissible_iff_pow s).mp hA
  have hp := hpre l hlL hl1
  have hw : 0 < order (s.take l) := order_pos_of_pow_lt hl1 hp
  have hr : (0 : ℚ) < rho (s.take l) := by exact_mod_cast (rho_pos_iff _).mpr hw
  have hx : (0 : ℚ) ≤ cyclePoint s := by
    unfold cyclePoint
    apply div_nonneg (by positivity)
    have : ((3 : ℚ) ^ order s) < 2 ^ s.length := by exact_mod_cast hfin
    linarith
  have hp' : ((2 : ℚ) ^ l) < 3 ^ order (s.take l) := by exact_mod_cast hp
  have h2 : (0 : ℚ) < 2 ^ l := by positivity
  rw [cyclePt, lt_div_iff₀ h2]
  nlinarith

/-- Lemma 4.5, the split of the trajectory: T^l(x) = x*_l + (x - x*) 3^(w_l)/2^l. -/
theorem iterate_eq_split {s : List Bool} {x : ℕ} (hx : tBits x s.length = s) {l : ℕ}
    (hl : l ≤ s.length) :
    (tStep^[l] x : ℚ) =
      cyclePt s l + ((x : ℚ) - cyclePoint s) * 3 ^ order (s.take l) / 2 ^ l := by
  have hb : tBits x l = s.take l := by rw [← tBits_take' x s.length l hl, hx]
  have h := affine l x
  rw [hb] at h
  have h' : (2 : ℚ) ^ l * (tStep^[l] x : ℚ) = 3 ^ order (s.take l) * x + rho (s.take l) := by
    exact_mod_cast h
  have h2 : (2 : ℚ) ^ l ≠ 0 := by positivity
  rw [cyclePt, eq_comm]
  field_simp
  linarith

/-- Proposition 4.6: the cycle point of a nonempty proper prefix of an admissible word, as a word
    of its own, is negative. -/
theorem prefix_cyclePoint_neg {s : List Bool} (hA : Admissible s) {l : ℕ} (hl1 : 1 ≤ l)
    (hlL : l < s.length) : cyclePoint (s.take l) < 0 := by
  obtain ⟨hpre, -⟩ := (admissible_iff_pow s).mp hA
  have hp := hpre l hlL hl1
  have hlen : (s.take l).length = l := by rw [List.length_take]; omega
  have hw : 0 < order (s.take l) := order_pos_of_pow_lt hl1 hp
  have hr : (0 : ℚ) < rho (s.take l) := by exact_mod_cast (rho_pos_iff _).mpr hw
  have hp' : ((2 : ℚ) ^ l) < 3 ^ order (s.take l) := by exact_mod_cast hp
  unfold cyclePoint
  rw [hlen]
  have hden : ((2 : ℚ) ^ l - 3 ^ order (s.take l)) < 0 := by linarith
  rw [div_lt_iff_of_neg hden, zero_mul]
  exact hr

end BestOfOrder
