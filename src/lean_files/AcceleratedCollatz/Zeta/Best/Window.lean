-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.Zeta.Best.Base
import Mathlib.Tactic.LinearCombination

/-!
  The window (paper, Theorem B and Theorem 6.1). If a member x of the class of an admissible word
  of Order n has T^L(x)/x > b/a, then x (2^L b - 3^n a) < R(n) a, with R(n) = `rhoMax n` the
  constant of the wall word (`window`). The paper states it for the drop ratio drop(x)/x of a
  class id; here the ratio is b/a, stated as b x < a T^L(x), so a may be any
  natural number; with b/a the ratio of a class id of the Order, this is the window of the search.
  With the lower wall rho ≥ 3^n - 2^n the window of a start y is at most R(n) y / (3^n - 2^n)
  (`window_seed`); with R(n) ≤ n 3^(n-1) that gives 2x < n y for n ≥ 3 (`window_seed_half`),
  and the share of s_0 is at least 2/n of
  the best's (`share_ratio_ge`).
-/

namespace AcceleratedCollatz.Best

/-- Theorem B: a start with a ratio above b/a lies inside the window. -/
theorem window {s : List Bool} (hA : Admissible s) {x a b : ℕ} (hx : tBits x s.length = s)
    (hab : b * x < a * tStep^[s.length] x) :
    (x : ℤ) * (2 ^ s.length * b - 3 ^ order s * a) < rhoMax (order s) * a := by
  have h := affine s.length x
  rw [hx] at h
  have h' : (2 : ℤ) ^ s.length * (tStep^[s.length] x : ℤ) = 3 ^ order s * x + rho s := by
    exact_mod_cast h
  have hab' : (b : ℤ) * x < a * (tStep^[s.length] x : ℤ) := by exact_mod_cast hab
  have hR : (rho s : ℤ) ≤ rhoMax (order s) := by exact_mod_cast rho_le_wall hA
  have h1 : (2 : ℤ) ^ s.length * (b * x) < 2 ^ s.length * (a * (tStep^[s.length] x : ℤ)) :=
    mul_lt_mul_of_pos_left hab' (by positivity)
  have h2 :
      (2 : ℤ) ^ s.length * (a * (tStep^[s.length] x : ℤ)) = a * (3 ^ order s * x + rho s) := by
    rw [← h']
    ring
  have h3 : (a : ℤ) * rho s ≤ a * rhoMax (order s) := mul_le_mul_of_nonneg_left hR (by positivity)
  nlinarith

/-- Corollary 6.2 (where the best lies): a member x of a class of Order n with a higher ratio than a
    member y of a class of Order n has x (3^n - 2^n) < R(n) y. With y the smallest start s_0 of the
    Order: the best is below s_0 R(n) / (3^n - 2^n). -/
theorem window_seed {s t : List Bool} (hs : Admissible s) (ht : Admissible t)
    (ho : order t = order s) {x y : ℕ} (hx : tBits x t.length = t) (hy : tBits y s.length = s)
    (h : tStep^[s.length] y * x < y * tStep^[t.length] x) :
    x * (3 ^ order s - 2 ^ order s) < rhoMax (order s) * y := by
  have hw := window ht hx h
  have hlen : t.length = s.length := by
    rw [admissible_length' t ht, admissible_length' s hs, ho]
  have ha := affine s.length y
  rw [hy] at ha
  have ha' : (2 : ℤ) ^ s.length * (tStep^[s.length] y : ℤ) = 3 ^ order s * y + rho s := by
    exact_mod_cast ha
  rw [hlen, ho] at hw
  have hlow : (3 : ℤ) ^ order s ≤ rho s + 2 ^ order s := by
    exact_mod_cast three_pow_le_rho_add' s
  have h23 : 2 ^ order s ≤ 3 ^ order s := Nat.pow_le_pow_left (by norm_num) _
  have hx0 : (0 : ℤ) ≤ x := by positivity
  zify [h23]
  nlinarith

/-- 2 3^(n-1) ≤ 3^n - 2^n for n ≥ 3, as 2^n ≤ 3^(n-1). -/
theorem two_pow_le_three_pow_pred {n : ℕ} (hn : 3 ≤ n) : 2 ^ n ≤ 3 ^ (n - 1) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have hk1 : k + 1 - 1 = (k - 1) + 1 := by omega
    rw [hk1, pow_succ, pow_succ]
    omega

/-- Corollary 6.2, the second bound: a member x of a class of Order n ≥ 3 with a higher ratio than a
    member y of a class of Order n has 2x < n y. With y = s_0: the best c* < n s_0 / 2. -/
theorem window_seed_half {s t : List Bool} (hs : Admissible s) (ht : Admissible t)
    (ho : order t = order s) (hn : 3 ≤ order s) {x y : ℕ} (hx : tBits x t.length = t)
    (hy : tBits y s.length = s) (h : tStep^[s.length] y * x < y * tStep^[t.length] x) :
    2 * x < order s * y := by
  have hw := window_seed hs ht ho hx hy h
  have hR := rhoMax_le_mul (order s)
  have h23 := two_pow_le_three_pow_pred hn
  set n := order s
  have h3 : 3 ^ n = 3 * 3 ^ (n - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hle : 2 * 3 ^ (n - 1) ≤ 3 ^ n - 2 ^ n := by omega
  have hpos : 0 < 3 ^ (n - 1) := by positivity
  have h1 : x * (2 * 3 ^ (n - 1)) ≤ x * (3 ^ n - 2 ^ n) := Nat.mul_le_mul_left _ hle
  have h2 : rhoMax n * y ≤ n * 3 ^ (n - 1) * y := Nat.mul_le_mul_right _ hR
  have h4 : 2 * x * 3 ^ (n - 1) < n * y * 3 ^ (n - 1) := by
    calc 2 * x * 3 ^ (n - 1) = x * (2 * 3 ^ (n - 1)) := by ring
      _ < n * 3 ^ (n - 1) * y := by omega
      _ = n * y * 3 ^ (n - 1) := by ring
  exact Nat.lt_of_mul_lt_mul_right h4

/-- Corollary 6.2, the shares: for a member y of a class of Order n ≥ 3 (word s) and a member x ≥ y
    of a class of Order n (word t), 2 rho_t y ≤ n rho_s x. With y = s_0 and x = c*:
    θ(s_0)/θ(c*) = rho_0 c*/(rho* s_0) ≥ 2/n. -/
theorem share_ratio_ge {s t : List Bool} (ht : Admissible t) (ho : order t = order s)
    (hn : 3 ≤ order s) {x y : ℕ} (hxy : y ≤ x) :
    2 * rho t * y ≤ order s * rho s * x := by
  have hR := rhoMax_le_mul (order s)
  have hw := rho_le_wall ht
  rw [ho] at hw
  have hlow := three_pow_le_rho_add' s
  have h23 := two_pow_le_three_pow_pred hn
  set n := order s
  have h3 : 3 ^ n = 3 * 3 ^ (n - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have h1 : 2 * rho t ≤ n * rho s := by
    calc 2 * rho t ≤ 2 * (n * 3 ^ (n - 1)) := by omega
      _ = n * (2 * 3 ^ (n - 1)) := by ring
      _ ≤ n * rho s := Nat.mul_le_mul_left _ (by omega)
  calc 2 * rho t * y ≤ n * rho s * y := Nat.mul_le_mul_right _ h1
    _ ≤ n * rho s * x := Nat.mul_le_mul_left _ hxy

/-- Remark 2.10 (ties): two starts with the same word length L and Order, x of word s and y of
    word t,
    with equal ratios T^L(x)/x = T^L(y)/y, have rho s * y = rho t * x. -/
theorem tie_rho {s t : List Bool} (hl : s.length = t.length) (ho : order s = order t) {x y : ℕ}
    (hx : tBits x s.length = s) (hy : tBits y t.length = t)
    (h : tStep^[s.length] x * y = tStep^[s.length] y * x) : rho s * y = rho t * x := by
  have h1 := affine s.length x
  have h2 := affine s.length y
  rw [hx] at h1
  rw [hl, hy, ← ho, ← hl] at h2
  have h1' : (2 : ℤ) ^ s.length * (tStep^[s.length] x : ℤ) = 3 ^ order s * x + rho s := by
    exact_mod_cast h1
  have h2' : (2 : ℤ) ^ s.length * (tStep^[s.length] y : ℤ) = 3 ^ order s * y + rho t := by
    exact_mod_cast h2
  have h' : (tStep^[s.length] x : ℤ) * y = (tStep^[s.length] y : ℤ) * x := by exact_mod_cast h
  zify
  linear_combination -(y : ℤ) * h1' + (x : ℤ) * h2' + (2 : ℤ) ^ s.length * h'

/-- Remark 2.10 (ties), the divisibility: a start x tying y (as in `tie_rho`, y > 0) is a
    multiple of
    u = y / gcd(y, rho t). So the ties of the best c* are among the multiples of c*/gcd(c*, rho*)
    below the window (`window`, non-strict). -/
theorem tie_dvd {s t : List Bool} (hl : s.length = t.length) (ho : order s = order t) {x y : ℕ}
    (hx : tBits x s.length = s) (hy : tBits y t.length = t) (hy0 : 0 < y)
    (h : tStep^[s.length] x * y = tStep^[s.length] y * x) :
    y / Nat.gcd y (rho t) ∣ x := by
  have hr := tie_rho hl ho hx hy h
  have hg : 0 < Nat.gcd y (rho t) := Nat.gcd_pos_of_pos_left _ hy0
  have hc := Nat.coprime_div_gcd_div_gcd hg
  apply hc.dvd_of_dvd_mul_left
  apply Nat.dvd_of_mul_dvd_mul_right hg
  rw [Nat.div_mul_cancel (Nat.gcd_dvd_left y (rho t)), mul_right_comm,
    Nat.div_mul_cancel (Nat.gcd_dvd_right y (rho t)), ← hr]
  exact Dvd.intro_left _ rfl

end AcceleratedCollatz.Best
