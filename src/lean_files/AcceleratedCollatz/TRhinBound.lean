-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TWidthBound

/-!
  Conditional polynomial finite check. `RhinBound K C`: 3^n ≤ K p2(n)^C (2^p2(n) - 3^n)
  for every Order n ≥ 1. Rhin (1987) gives it with K = 1 and exponent 13.3, so
  `RhinBound 1 14` (cited, not formalized). A bound from Order n₀ on gives
  `RhinBound (K + 3^n₀) C` (`rhinBound_of_rhinBoundFrom`). Under it widthBound n ≤ K 2^C n^(C+1)
  (`widthBound_le_of_rhinBound`), and ClassDrops follows from a check, per Order n, of
  the x with 1 < x ≤ K 2^C n^(C+1) (`classDrops_of_rhinBound`).
-/

namespace AcceleratedCollatz

/-- 2^p2(n) - 3^n is at least 3^n / (K p2(n)^C) for every Order n ≥ 1. -/
def RhinBound (K C : ℕ) : Prop :=
  ∀ n, 1 ≤ n → 3 ^ n ≤ K * p2_of n ^ C * (2 ^ p2_of n - 3 ^ n)

/-- `RhinBound` from Order n₀ on. -/
def RhinBoundFrom (K C n₀ : ℕ) : Prop :=
  ∀ n, n₀ ≤ n → 3 ^ n ≤ K * p2_of n ^ C * (2 ^ p2_of n - 3 ^ n)

/-- Finitely many exceptions are absorbed into the constant: K + 3^n₀. -/
theorem rhinBound_of_rhinBoundFrom {K C n₀ : ℕ} (hR : RhinBoundFrom K C n₀) :
    RhinBound (K + 3 ^ n₀) C := by
  intro n _
  have hd : 1 ≤ 2 ^ p2_of n - 3 ^ n := by
    have := p2_of_spec n
    omega
  have hp : 1 ≤ p2_of n ^ C := Nat.one_le_pow C (p2_of n) (by
    unfold p2_of
    omega)
  have hpd : 1 ≤ p2_of n ^ C * (2 ^ p2_of n - 3 ^ n) := Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero (by omega) (by omega))
  rcases le_or_gt n₀ n with h | h
  · calc 3 ^ n ≤ K * p2_of n ^ C * (2 ^ p2_of n - 3 ^ n) := hR n h
      _ ≤ (K + 3 ^ n₀) * p2_of n ^ C * (2 ^ p2_of n - 3 ^ n) := by
        gcongr
        exact Nat.le_add_right K (3 ^ n₀)
  · have h3 : 3 ^ n ≤ 3 ^ n₀ := Nat.pow_le_pow_right (by norm_num) h.le
    calc 3 ^ n ≤ 3 ^ n₀ * 1 := by omega
      _ ≤ 3 ^ n₀ * (p2_of n ^ C * (2 ^ p2_of n - 3 ^ n)) := Nat.mul_le_mul_left _ hpd
      _ ≤ (K + 3 ^ n₀) * p2_of n ^ C * (2 ^ p2_of n - 3 ^ n) := by
        rw [mul_assoc]
        gcongr
        exact Nat.le_add_left (3 ^ n₀) K

/-- p2(n) ≤ 2n for n ≥ 1. -/
theorem p2_of_le_two_mul {n : ℕ} (hn : 1 ≤ n) : p2_of n ≤ 2 * n := by
  have h1 : 2 ^ (p2_of n - 1) ≤ 3 ^ n := p2_of_spec_lower n
  have h2 : 3 ^ n < 4 ^ n := Nat.pow_lt_pow_left (by norm_num) (by omega)
  have h3 : (4 : ℕ) ^ n = 2 ^ (2 * n) := by
    rw [pow_mul]
    norm_num
  have h4 : 2 ^ (p2_of n - 1) < 2 ^ (2 * n) := by
    rw [← h3]
    exact lt_of_le_of_lt h1 h2
  have h5 : p2_of n - 1 < 2 * n := (Nat.pow_lt_pow_iff_right (by norm_num)).mp h4
  omega

/-- Under `RhinBound K C`: widthBound n ≤ K n p2(n)^C. -/
theorem widthBound_le_p2_of_rhinBound {K C : ℕ} (hR : RhinBound K C) (n : ℕ) :
    widthBound n ≤ K * n * p2_of n ^ C := by
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    simp [widthBound]
  · unfold widthBound
    apply Nat.div_le_of_le_mul
    have h3 : 3 ^ (n - 1) ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) (Nat.sub_le n 1)
    have hb := hR n hpos
    calc n * 3 ^ (n - 1) ≤ n * 3 ^ n := Nat.mul_le_mul_left n h3
      _ ≤ n * (K * p2_of n ^ C * (2 ^ p2_of n - 3 ^ n)) := Nat.mul_le_mul_left n hb
      _ = (2 ^ p2_of n - 3 ^ n) * (K * n * p2_of n ^ C) := by ring

/-- Under `RhinBound K C`: widthBound n ≤ K 2^C n^(C+1). -/
theorem widthBound_le_of_rhinBound {K C : ℕ} (hR : RhinBound K C) (n : ℕ) :
    widthBound n ≤ K * 2 ^ C * n ^ (C + 1) := by
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    simp [widthBound]
  · have hp : p2_of n ^ C ≤ (2 * n) ^ C := Nat.pow_le_pow_left (p2_of_le_two_mul hpos) C
    calc widthBound n ≤ K * n * p2_of n ^ C := widthBound_le_p2_of_rhinBound hR n
      _ ≤ K * n * (2 * n) ^ C := Nat.mul_le_mul_left (K * n) hp
      _ = K * 2 ^ C * n ^ (C + 1) := by ring

/-- Under `RhinBound K C`: ClassDrops at Order n from the drop of every x with
    1 < x ≤ K 2^C n^(C+1) whose word up to the coefficient stopping time has Order n. -/
theorem classDropsAt_of_rhinBound {K C : ℕ} (hR : RhinBound K C) (n : ℕ)
    (h : ∀ x, 1 < x → x ≤ K * 2 ^ C * n ^ (C + 1) → ∀ m, Admissible (tBits x m) →
      order (tBits x m) = n → tStep^[m] x < x) :
    ClassDropsAt n :=
  classDropsAt_of_width n fun x hx hxb =>
    h x hx (hxb.trans (widthBound_le_of_rhinBound hR n))

/-- Under `RhinBound K C`: ClassDrops from the per-Order checks up to K 2^C n^(C+1). -/
theorem classDrops_of_rhinBound {K C : ℕ} (hR : RhinBound K C)
    (h : ∀ n x, 1 < x → x ≤ K * 2 ^ C * n ^ (C + 1) → ∀ m, Admissible (tBits x m) →
      order (tBits x m) = n → tStep^[m] x < x) :
    ClassDrops :=
  classDrops_iff_forall_at.mpr fun n => classDropsAt_of_rhinBound hR n (h n)

set_option linter.hashCommand false in
#guard (List.range' 1 100).all fun n =>
  decide (3 ^ n ≤ p2_of n ^ 2 * (2 ^ p2_of n - 3 ^ n))

end AcceleratedCollatz
