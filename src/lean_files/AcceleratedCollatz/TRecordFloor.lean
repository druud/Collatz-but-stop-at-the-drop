-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TSmoothClass

/-!
  The fraction P/Q of a record Order Q (`RecordFrac`: P = p2(Q) at an upper record Order,
  P = p2(Q) - 1 at a lower one) gives the binary lengths of the powers of 3 by floors:
  ⌊i P/Q⌋ + 1 = p2(i) for 1 ≤ i < Q (`div_record_add_one`), and ⌊t Q/P⌋ + 1 is the number
  of powers of 3 below 2^t, the round-up of t log 2 / log 3, for 1 ≤ t < P
  (`div_record_swap_add_one`). These are the floors the A003586 program takes from
  `bestappr`, whose results are convergents, so record Orders.
-/

namespace AcceleratedCollatz

/-- P/Q is the fraction of a record Order Q ≥ 1: P = p2(Q) at an upper record Order,
    P = p2(Q) - 1 at a lower one. -/
def RecordFrac (P Q : ℕ) : Prop :=
  1 ≤ Q ∧ ((UpperRecord Q ∧ P = p2_of Q) ∨ (LowerRecord Q ∧ P = p2_of Q - 1))

/-- 2^(p2(i) - 1) < 3^i for i ≥ 1. -/
theorem two_pow_p2_sub_lt {i : ℕ} (hi : 1 ≤ i) : 2 ^ (p2_of i - 1) < 3 ^ i := by
  rcases Nat.lt_or_ge (2 ^ (p2_of i - 1)) (3 ^ i) with h | h
  · exact h
  · exfalso
    have heq : 2 ^ (p2_of i - 1) = 3 ^ i := le_antisymm (p2_of_spec_lower i) h
    have hodd : ¬ 2 ∣ 3 ^ i := by
      rw [Nat.Prime.dvd_iff_not_coprime Nat.prime_two]
      intro hc
      exact hc (Nat.Coprime.pow_right i (by decide))
    rcases Nat.eq_zero_or_pos (p2_of i - 1) with h0 | hpos
    · rw [h0, pow_zero] at heq
      have : 3 ≤ 3 ^ i := by
        calc 3 = 3 ^ 1 := by norm_num
          _ ≤ 3 ^ i := Nat.pow_le_pow_right (by norm_num) hi
      omega
    · apply hodd
      rw [← heq]
      exact dvd_pow_self 2 (by omega)

/-- a < b from 2^a < 2^b. -/
theorem lt_of_two_pow_lt {a b : ℕ} (h : 2 ^ a < 2 ^ b) : a < b :=
  (Nat.pow_lt_pow_iff_right (by norm_num)).mp h

/-- p2(Q) - 1 ≤ P ≤ p2(Q) for a record fraction. -/
theorem recordFrac_bounds {P Q : ℕ} (h : RecordFrac P Q) : p2_of Q - 1 ≤ P ∧ P ≤ p2_of Q := by
  rcases h.2 with ⟨_, hP⟩ | ⟨_, hP⟩
  · omega
  · omega

/-- For 1 ≤ i < Q: (p2(i) - 1) Q < i P < p2(i) Q. -/
theorem record_mul_bounds {P Q i : ℕ} (h : RecordFrac P Q) (hi1 : 1 ≤ i) (hiQ : i < Q) :
    (p2_of i - 1) * Q < i * P ∧ i * P < p2_of i * Q := by
  have hQ1 := h.1
  rcases h.2 with ⟨hR, hP⟩ | ⟨hR, hP⟩
  · subst hP
    refine ⟨?_, ?_⟩
    · apply lt_of_two_pow_lt
      have h1 : (2 ^ (p2_of i - 1)) ^ Q < (3 ^ i) ^ Q :=
        Nat.pow_lt_pow_left (two_pow_p2_sub_lt hi1) (by omega)
      have h2 : (3 ^ Q) ^ i < (2 ^ p2_of Q) ^ i :=
        Nat.pow_lt_pow_left (p2_of_spec Q) (by omega)
      calc 2 ^ ((p2_of i - 1) * Q) = (2 ^ (p2_of i - 1)) ^ Q := pow_mul 2 _ Q
        _ < (3 ^ i) ^ Q := h1
        _ = (3 ^ Q) ^ i := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
        _ < (2 ^ p2_of Q) ^ i := h2
        _ = 2 ^ (i * p2_of Q) := by rw [← pow_mul, Nat.mul_comm]
    · have := hR i hi1 hiQ
      rw [Nat.mul_comm (p2_of i) Q]
      exact this
  · subst hP
    refine ⟨?_, ?_⟩
    · have := hR i hi1 hiQ
      rw [Nat.mul_comm (p2_of i - 1) Q]
      exact this
    · apply lt_of_two_pow_lt
      have h1 : (2 ^ (p2_of Q - 1)) ^ i < (3 ^ Q) ^ i :=
        Nat.pow_lt_pow_left (two_pow_p2_sub_lt hQ1) (by omega)
      have h2 : (3 ^ i) ^ Q < (2 ^ p2_of i) ^ Q :=
        Nat.pow_lt_pow_left (p2_of_spec i) (by omega)
      calc 2 ^ (i * (p2_of Q - 1)) = (2 ^ (p2_of Q - 1)) ^ i := by
            rw [← pow_mul, Nat.mul_comm]
        _ < (3 ^ Q) ^ i := h1
        _ = (3 ^ i) ^ Q := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
        _ < (2 ^ p2_of i) ^ Q := h2
        _ = 2 ^ (p2_of i * Q) := by rw [← pow_mul]

/-- ⌊i P/Q⌋ + 1 = p2(i) for 1 ≤ i < Q. -/
theorem div_record_add_one {P Q i : ℕ} (h : RecordFrac P Q) (hi1 : 1 ≤ i) (hiQ : i < Q) :
    i * P / Q + 1 = p2_of i := by
  obtain ⟨hlo, hhi⟩ := record_mul_bounds h hi1 hiQ
  have hQ : 0 < Q := by
    have := h.1
    omega
  have hp1 : 1 ≤ p2_of i := by
    have := p2_of_spec i
    rcases Nat.eq_zero_or_pos (p2_of i) with h0 | h0
    · rw [h0, pow_zero] at this
      have : 1 ≤ 3 ^ i := Nat.one_le_pow _ _ (by norm_num)
      omega
    · exact h0
  have hdiv : i * P / Q = p2_of i - 1 := by
    apply Nat.div_eq_of_lt_le
    · exact hlo.le
    · rw [Nat.sub_add_cancel hp1]
      exact hhi
  omega

/-- The number of powers of 3 below 2^t is ⌊t Q/P⌋ + 1 for 1 ≤ t < P. -/
theorem div_record_swap_add_one {P Q t : ℕ} (h : RecordFrac P Q) (ht1 : 1 ≤ t) (htP : t < P) :
    t * Q / P + 1 = Nat.clog 3 (2 ^ t) := by
  have hP : 0 < P := by omega
  have hbP := recordFrac_bounds h
  have key : ∀ i, i < t * Q / P + 1 ↔ p2_of i ≤ t := by
    intro i
    rcases Nat.eq_zero_or_pos i with h0 | hi1
    · subst h0
      have : p2_of 0 = 1 := by
        unfold p2_of
        simp
      rw [this]
      exact ⟨fun _ => ht1, fun _ => Nat.succ_pos _⟩
    · rw [Nat.lt_succ_iff, Nat.le_div_iff_mul_le hP]
      rcases Nat.lt_or_ge i Q with hiQ | hiQ
      · have hd := div_record_add_one h hi1 hiQ
        obtain ⟨hlo, hhi⟩ := record_mul_bounds h hi1 hiQ
        have hQ : 0 < Q := by omega
        constructor
        · intro hle
          have : i * P / Q ≤ t * Q / Q := Nat.div_le_div_right hle
          rw [Nat.mul_div_cancel t hQ] at this
          rcases Nat.eq_or_lt_of_le this with heq | hlt
          · exfalso
            have hm := Nat.div_mul_le_self (i * P) Q
            have he : i * P = t * Q := by
              apply le_antisymm
              · exact hle
              · rw [← heq]
                exact hm
            rw [he, Nat.mul_div_cancel t hQ] at hd
            have h1 : (p2_of i - 1) * Q < t * Q := by
              rw [← he]
              exact hlo
            have h2 : t * Q < p2_of i * Q := by
              rw [← he]
              exact hhi
            have h1' := Nat.lt_of_mul_lt_mul_right h1
            have h2' := Nat.lt_of_mul_lt_mul_right h2
            omega
          · omega
        · intro hle
          have hlt : i * P / Q < t := by omega
          rw [Nat.div_lt_iff_lt_mul hQ] at hlt
          exact hlt.le
      · constructor
        · intro hle
          exfalso
          have h1 : Q * P ≤ i * P := Nat.mul_le_mul_right P hiQ
          have hQ1 := h.1
          have h2 : t * Q < P * Q := Nat.mul_lt_mul_of_pos_right htP (by omega)
          rw [Nat.mul_comm Q P] at h1
          omega
        · intro hle
          exfalso
          have := p2_of_mono hiQ
          omega
  apply le_antisymm
  · by_contra hlt
    push Not at hlt
    have := (key (Nat.clog 3 (2 ^ t))).mp hlt
    rw [p2_of_le_iff_lt_clog] at this
    exact lt_irrefl _ this
  · by_contra hlt
    push Not at hlt
    have := (p2_of_le_iff_lt_clog _ _).mpr hlt
    have h2 := (key (t * Q / P + 1)).mpr this
    exact lt_irrefl _ h2

end AcceleratedCollatz
