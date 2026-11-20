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
  (`prefix_cyclePoint_neg`). Each odd step of the rational cycle multiplies by at most 3 + 1/x*
  (`cyclePt_le_pow`), so 2^L ≤ (3 + 1/x*)^n, and x* lies below the ceiling t_n
  (`cyclePoint_lt_ceiling`).
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

/-- 2^l x*_l = 3^(w_l) x* + rho_l. -/
theorem two_pow_mul_cyclePt (s : List Bool) (l : ℕ) :
    (2 : ℚ) ^ l * cyclePt s l = 3 ^ order (s.take l) * cyclePoint s + rho (s.take l) := by
  rw [cyclePt]
  field_simp

/-- x*_0 = x*. -/
theorem cyclePt_zero (s : List Bool) : cyclePt s 0 = cyclePoint s := by
  simp [cyclePt, order, rho, affineNum]

/-- x* ≤ x*_l for l < L (an admissible word). -/
theorem cyclePoint_le_cyclePt {s : List Bool} (hA : Admissible s) {l : ℕ} (hl : l < s.length) :
    cyclePoint s ≤ cyclePt s l := by
  rcases Nat.eq_zero_or_pos l with rfl | h1
  · rw [cyclePt_zero]
  · exact (cyclePoint_lt_cyclePt hA h1 hl).le

/-- The cycle point of a word of positive Order with 3^n < 2^L is positive. -/
theorem cyclePoint_pos {s : List Bool} (hn : 0 < order s) (hd : 3 ^ order s < 2 ^ s.length) :
    0 < cyclePoint s := by
  have hr : (0 : ℚ) < rho s := by exact_mod_cast (rho_pos_iff s).mpr hn
  have hd' : ((3 : ℚ) ^ order s) < 2 ^ s.length := by exact_mod_cast hd
  unfold cyclePoint
  apply div_pos hr
  linarith

/-- Along the rational cycle every odd step multiplies by at most 3 + 1/x*:
    2^l x*_l ≤ (3 + 1/x*)^(w_l) x* for l ≤ L. -/
theorem cyclePt_le_pow {s : List Bool} (hA : Admissible s) (hn : 0 < order s) :
    ∀ l ≤ s.length, (2 : ℚ) ^ l * cyclePt s l ≤
      (3 + 1 / cyclePoint s) ^ order (s.take l) * cyclePoint s := by
  have hd := ((admissible_iff_pow s).mp hA).2
  have hx := cyclePoint_pos hn hd
  intro l
  induction l with
  | zero => intro _; simp [cyclePt_zero, order]
  | succ l ih =>
    intro hl
    have hlt : l < s.length := by omega
    have ih' := ih hlt.le
    have hge := cyclePoint_le_cyclePt hA hlt
    have htake : s.take (l + 1) = s.take l ++ [s[l]] := List.take_succ_eq_append_getElem hlt
    have e0 := two_pow_mul_cyclePt s l
    have e1 := two_pow_mul_cyclePt s (l + 1)
    rw [htake, AcceleratedCollatz.rho_append, AcceleratedCollatz.order_append] at e1
    rw [htake, AcceleratedCollatz.order_append]
    rw [List.length_take, min_eq_left hlt.le] at e1
    set x := cyclePoint s
    set A := (2 : ℚ) ^ l * cyclePt s l
    have hc : (0 : ℚ) < 3 + 1 / x := by positivity
    cases hb : s[l] with
    | false =>
      have ho : order [false] = 0 := rfl
      have hr : rho [false] = 0 := rfl
      rw [hb, ho, hr] at e1
      rw [ho, add_zero, e1]
      push_cast
      simp only [one_mul, mul_zero, add_zero]
      rw [← e0]
      exact ih'
    | true =>
      have ho : order [true] = 1 := rfl
      have hr : rho [true] = 1 := rfl
      rw [hb, ho, hr] at e1
      rw [ho, e1, pow_succ]
      push_cast
      -- 2^(l+1) x*_{l+1} = 3 A + 2^l, with A = 2^l x*_l ≥ 2^l x*
      have hA2 : (2 : ℚ) ^ l * x ≤ A := by
        have h2 : (0 : ℚ) ≤ 2 ^ l := by positivity
        exact mul_le_mul_of_nonneg_left hge h2
      have key : 3 * (3 ^ order (s.take l) * x + rho (s.take l)) + (2 : ℚ) ^ l ≤ (3 + 1 / x) * A := by
        rw [← e0]
        have : (2 : ℚ) ^ l ≤ A / x := by rw [le_div_iff₀ hx]; exact hA2
        have hAx : A / x = 1 / x * A := by ring
        nlinarith
      calc 3 ^ order (s.take l) * 3 ^ 1 * x + (3 ^ 1 * (rho (s.take l) : ℚ) + 2 ^ l * 1)
          = 3 * (3 ^ order (s.take l) * x + rho (s.take l)) + 2 ^ l := by ring
        _ ≤ (3 + 1 / x) * A := key
        _ ≤ (3 + 1 / x) * ((3 + 1 / x) ^ order (s.take l) * x) := mul_le_mul_of_nonneg_left ih' hc.le
        _ = (3 + 1 / x) ^ (order (s.take l) + 1) * x := by ring

/-- Proposition 4.7 (the ceiling): for an admissible word of Order n ≥ 1 and length
    L, 2^L ≤ (3 + 1/x*)^n, so every t > 0 with (3t + 1)^n < 2^L t^n lies above the cycle point. -/
theorem cyclePoint_lt_ceiling {s : List Bool} (hA : Admissible s) (hn : 0 < order s) {t : ℕ}
    (ht0 : 0 < t) (ht : (3 * t + 1) ^ order s < 2 ^ s.length * t ^ order s) :
    cyclePoint s < t := by
  have hd := ((admissible_iff_pow s).mp hA).2
  have hx := cyclePoint_pos hn hd
  have hb := cyclePt_le_pow hA hn s.length le_rfl
  rw [cyclePt_length hd, List.take_length] at hb
  have h2 : (2 : ℚ) ^ s.length ≤ (3 + 1 / cyclePoint s) ^ order s := le_of_mul_le_mul_right hb hx
  have ht' : ((3 : ℚ) * t + 1) ^ order s < 2 ^ s.length * (t : ℚ) ^ order s := by exact_mod_cast ht
  have htq : (0 : ℚ) < t := by exact_mod_cast ht0
  have h3 : (3 + 1 / (t : ℚ)) ^ order s < 2 ^ s.length := by
    rw [show (3 + 1 / (t : ℚ)) = (3 * t + 1) / t by field_simp, div_pow, div_lt_iff₀ (by positivity)]
    exact ht'
  by_contra hc
  have hle : (t : ℚ) ≤ cyclePoint s := not_lt.mp hc
  have : 3 + 1 / cyclePoint s ≤ 3 + 1 / (t : ℚ) := by
    gcongr
  have := pow_le_pow_left₀ (by positivity) this (order s)
  linarith


end BestOfOrder
