-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TRhinBound
import AcceleratedCollatz.TRhinCheck

/-!
  3c + 1 ≤ 2^p2(n) for the class ids that could break the width identity (B46, 13 Nov 2026;
  paper 3, Ch. 4, "The bound of a split"). Those class ids are at most widthBound n
  = ⌊n 3^(n-1)/d⌋, and under a bound 3^n ≤ K p2(n)^C d of Rhin's kind, 3 widthBound n
  ≤ 3 K n p2(n)^C, which is below 2^p2(n) once p2(n) is large. So the split after the
  leading 1 is the drop itself (`split_one_iff`) at every Order up to 10^60 without a
  hypothesis (`three_mul_widthBound_add_one_le_upTo`), and at every Order under Rhin's
  bound `RhinBound 1 14` (`three_mul_widthBound_add_one_le_of_rhin`).
-/

namespace AcceleratedCollatz

/-- n < p2(n). -/
theorem lt_p2_of_self (n : ℕ) : n < p2_of n := by
  have h1 : 2 ^ n ≤ 3 ^ n := Nat.pow_le_pow_left (by norm_num) n
  have h2 := p2_of_spec n
  exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp (lt_of_le_of_lt h1 h2)

/-- 3 L^(C+1) < 2^L once (C+1)(log2 L + 1) + 2 ≤ L. -/
theorem three_mul_pow_lt_two_pow {L C : ℕ}
    (h : (C + 1) * (Nat.log 2 L + 1) + 2 ≤ L) : 3 * L ^ (C + 1) < 2 ^ L := by
  have hl : L < 2 ^ (Nat.log 2 L + 1) := Nat.lt_pow_succ_log_self (by norm_num) L
  have hp : L ^ (C + 1) < (2 ^ (Nat.log 2 L + 1)) ^ (C + 1) :=
    Nat.pow_lt_pow_left hl (by omega)
  rw [← pow_mul, mul_comm] at hp
  calc 3 * L ^ (C + 1) < 4 * 2 ^ ((C + 1) * (Nat.log 2 L + 1)) := by omega
    _ = 2 ^ ((C + 1) * (Nat.log 2 L + 1) + 2) := by rw [pow_add]; ring
    _ ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) h

/-- The core step: from 3^n ≤ K p2(n)^C d and 3 K n p2(n)^C < 2^p2(n), every c ≤ widthBound n
    has 3c + 1 ≤ 2^p2(n). -/
theorem three_mul_add_one_le_of_bound {n K C c : ℕ} (hn : 1 ≤ n)
    (hR : 3 ^ n ≤ K * p2_of n ^ C * (2 ^ p2_of n - 3 ^ n)) (hc : c ≤ widthBound n)
    (hL : 3 * (K * n * p2_of n ^ C) < 2 ^ p2_of n) : 3 * c + 1 ≤ 2 ^ p2_of n := by
  have hw : widthBound n ≤ K * n * p2_of n ^ C := by
    unfold widthBound
    apply Nat.div_le_of_le_mul
    have h3 : 3 ^ (n - 1) ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) (Nat.sub_le n 1)
    calc n * 3 ^ (n - 1) ≤ n * 3 ^ n := Nat.mul_le_mul_left n h3
      _ ≤ n * (K * p2_of n ^ C * (2 ^ p2_of n - 3 ^ n)) := Nat.mul_le_mul_left n hR
      _ = (2 ^ p2_of n - 3 ^ n) * (K * n * p2_of n ^ C) := by ring
  have := hn
  omega

/-- With K = 1: 3 n p2(n)^C < 2^p2(n) once (C+1)(log2 p2(n) + 1) + 2 ≤ p2(n). -/
theorem three_mul_n_pow_lt {n C : ℕ}
    (h : (C + 1) * (Nat.log 2 (p2_of n) + 1) + 2 ≤ p2_of n) :
    3 * (1 * n * p2_of n ^ C) < 2 ^ p2_of n := by
  have hn := lt_p2_of_self n
  rw [Nat.one_mul]
  have h1 : n * p2_of n ^ C ≤ p2_of n ^ (C + 1) := by
    rw [pow_succ, mul_comm (p2_of n ^ C)]
    exact Nat.mul_le_mul_right _ hn.le
  have h2 := three_mul_pow_lt_two_pow h
  omega

/-- 32 ≤ p2(n) from Order 20 on. -/
theorem p2_of_ge_32 {n : ℕ} (hn : 20 ≤ n) : 32 ≤ p2_of n := by
  have h1 : 3 ^ 20 ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have h2 := p2_of_spec n
  have h3 : 2 ^ 31 < 2 ^ p2_of n := by
    calc 2 ^ 31 < 3 ^ 20 := by norm_num
      _ ≤ 3 ^ n := h1
      _ < 2 ^ p2_of n := h2
  have := (Nat.pow_lt_pow_iff_right (by norm_num)).mp h3
  omega

/-- 128 ≤ p2(n) from Order 81 on. -/
theorem p2_of_ge_128 {n : ℕ} (hn : 81 ≤ n) : 128 ≤ p2_of n := by
  have h1 : 3 ^ 81 ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have h2 := p2_of_spec n
  have h3 : 2 ^ 127 < 2 ^ p2_of n := by
    calc 2 ^ 127 < 3 ^ 81 := by norm_num
      _ ≤ 3 ^ n := h1
      _ < 2 ^ p2_of n := h2
  have := (Nat.pow_lt_pow_iff_right (by norm_num)).mp h3
  omega

/-- a (log2 L + 1) + 2 ≤ L from 2^m on, for a m + a + 2 ≤ 2^m. -/
theorem mul_log_add_le {a m L : ℕ} (hm : a * m + a + 2 ≤ 2 ^ m) (hL : 2 ^ m ≤ L)
    (hmono : ∀ k, m ≤ k → a * k + a + 2 ≤ 2 ^ k) : a * (Nat.log 2 L + 1) + 2 ≤ L := by
  have hk : m ≤ Nat.log 2 L := Nat.le_log_of_pow_le (by norm_num) hL
  have h1 := hmono _ hk
  have hL0 : L ≠ 0 := by
    have := Nat.one_le_two_pow (n := m)
    omega
  have h2 : 2 ^ Nat.log 2 L ≤ L := Nat.pow_log_le_self 2 hL0
  have := hm
  nlinarith

/-- a k + a + 2 ≤ 2^k from k₀ on, given it at k₀ and a ≤ 2^k₀. -/
theorem lin_le_two_pow {a k₀ : ℕ} (h0 : a * k₀ + a + 2 ≤ 2 ^ k₀) (ha : a ≤ 2 ^ k₀) :
    ∀ k, k₀ ≤ k → a * k + a + 2 ≤ 2 ^ k := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact h0
  | succ k hk ih =>
    have hp : 2 ^ k₀ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    rw [pow_succ]
    nlinarith

/-- The small Orders, by the kernel: 3 widthBound n + 1 ≤ 2^p2(n) for 1 ≤ n < 20. -/
theorem three_mul_widthBound_add_one_le_small :
    ∀ n, n < 20 → 3 * widthBound n + 1 ≤ 2 ^ p2_of n := by
  decide +kernel

/-- Without a hypothesis: 3 widthBound n + 1 ≤ 2^p2(n) for every Order n ≤ 10^60. -/
theorem three_mul_widthBound_add_one_le_upTo (n : ℕ) (hn : n ≤ 10 ^ 60) :
    3 * widthBound n + 1 ≤ 2 ^ p2_of n := by
  rcases lt_or_ge n 20 with h | h
  · exact three_mul_widthBound_add_one_le_small n h
  · have hL := p2_of_ge_32 h
    have hlog : 3 * (Nat.log 2 (p2_of n) + 1) + 2 ≤ p2_of n :=
      mul_log_add_le (m := 5) (by norm_num) (by norm_num; omega)
        (lin_le_two_pow (by norm_num) (by norm_num))
    exact three_mul_add_one_le_of_bound (K := 1) (C := 2) (by omega)
      (rhinBoundUpTo_one_two n (by omega) hn) le_rfl (three_mul_n_pow_lt hlog)

/-- Under Rhin's bound `RhinBound 1 14`: 3 widthBound n + 1 ≤ 2^p2(n) at every Order. -/
theorem three_mul_widthBound_add_one_le_of_rhin (hR : RhinBound 1 14) (n : ℕ) :
    3 * widthBound n + 1 ≤ 2 ^ p2_of n := by
  rcases le_or_gt n (10 ^ 60) with h | h
  · exact three_mul_widthBound_add_one_le_upTo n h
  · have h81 : 81 ≤ n := by
      have : (81 : ℕ) ≤ 10 ^ 60 := by norm_num
      omega
    have hL := p2_of_ge_128 h81
    have hlog : 15 * (Nat.log 2 (p2_of n) + 1) + 2 ≤ p2_of n :=
      mul_log_add_le (m := 7) (by norm_num) (by norm_num; omega)
        (lin_le_two_pow (by norm_num) (by norm_num))
    exact three_mul_add_one_le_of_bound (K := 1) (C := 14) (by omega)
      (hR n (by omega)) le_rfl (three_mul_n_pow_lt hlog)

end AcceleratedCollatz
