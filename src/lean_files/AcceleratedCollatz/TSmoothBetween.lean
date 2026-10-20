-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TBinomial
import AcceleratedCollatz.TRulerRecord

/-!
  The 3-smooth numbers between 3^n and 2^p2(n). 2^j 3^i lies strictly between
  them exactly when 1 ≤ i < n, j = p2(n) - p2(i) and the block factor of i is above that
  of n, in cross products 2^p2(i) 3^n < 2^p2(n) 3^i (`smooth_between_iff`). So none lies
  between them exactly when n is an upper record Order (`upperRecord_iff_none_between`).
-/

namespace AcceleratedCollatz

/-- 2^j 3^i lies strictly between 3^n and 2^p2(n) exactly when 1 ≤ i < n,
    j + p2(i) = p2(n) and 2^p2(i) 3^n < 2^p2(n) 3^i. -/
theorem smooth_between_iff {n i j : ℕ} :
    (3 ^ n < 2 ^ j * 3 ^ i ∧ 2 ^ j * 3 ^ i < 2 ^ p2_of n) ↔
      (1 ≤ i ∧ i < n ∧ j + p2_of i = p2_of n ∧
        2 ^ p2_of i * 3 ^ n < 2 ^ p2_of n * 3 ^ i) := by
  have hPn := p2_of_spec n
  have hLn := p2_of_spec_lower n
  have hPi := p2_of_spec i
  have hLi := p2_of_spec_lower i
  have hP1 : 1 ≤ p2_of n := by
    unfold p2_of
    omega
  have h2P : 2 ^ p2_of n = 2 * 2 ^ (p2_of n - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hP1]
  constructor
  · rintro ⟨hlo, hhi⟩
    have hin : i < n := by
      by_contra hge
      push Not at hge
      obtain ⟨e, he⟩ : ∃ e, i = n + e := ⟨i - n, by omega⟩
      rw [he, pow_add] at hlo hhi
      rcases Nat.eq_zero_or_pos e with he0 | hepos
      · rw [he0, pow_zero, Nat.mul_one] at hlo hhi
        rcases Nat.eq_zero_or_pos j with hj0 | hjpos
        · rw [hj0, pow_zero, Nat.one_mul] at hlo
          omega
        · have h2j : 2 ≤ 2 ^ j := by
            calc 2 = 2 ^ 1 := by norm_num
              _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hjpos
          have h1 : 2 * 3 ^ n ≤ 2 ^ j * 3 ^ n := Nat.mul_le_mul_right _ h2j
          omega
      · have h3e : 3 ≤ 3 ^ e := by
          calc 3 = 3 ^ 1 := by norm_num
            _ ≤ 3 ^ e := Nat.pow_le_pow_right (by norm_num) hepos
        have h1 : 3 ^ n * 3 ≤ 3 ^ n * 3 ^ e := Nat.mul_le_mul_left _ h3e
        have h2 : 3 ^ n * 3 ^ e ≤ 2 ^ j * (3 ^ n * 3 ^ e) :=
          Nat.le_mul_of_pos_left _ (by positivity)
        omega
    have hi1 : 1 ≤ i := by
      by_contra h0
      have hi0 : i = 0 := by omega
      rw [hi0, pow_zero, Nat.mul_one] at hlo hhi
      have hj : j < p2_of n := (Nat.pow_lt_pow_iff_right (by norm_num)).mp hhi
      have hj' : 2 ^ j ≤ 2 ^ (p2_of n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hupper : j + p2_of i ≤ p2_of n := by
      have h1 : 2 ^ j * 2 ^ (p2_of i - 1) ≤ 2 ^ j * 3 ^ i := Nat.mul_le_mul_left _ hLi
      have h2 : 2 ^ (j + (p2_of i - 1)) < 2 ^ p2_of n := by
        rw [pow_add]
        omega
      have h3 := (Nat.pow_lt_pow_iff_right (by norm_num)).mp h2
      have hpi : 1 ≤ p2_of i := by
        unfold p2_of
        omega
      omega
    have hlower : p2_of n ≤ j + p2_of i := by
      have h1 : 2 ^ j * 3 ^ i < 2 ^ j * 2 ^ p2_of i :=
        Nat.mul_lt_mul_of_pos_left hPi (by positivity)
      have h2 : 2 ^ (p2_of n - 1) < 2 ^ (j + p2_of i) := by
        rw [pow_add]
        omega
      have h3 := (Nat.pow_lt_pow_iff_right (by norm_num)).mp h2
      omega
    refine ⟨hi1, hin, by omega, ?_⟩
    have hjP : 2 ^ p2_of n = 2 ^ p2_of i * 2 ^ j := by
      rw [← pow_add]
      congr 1
      omega
    rw [hjP, Nat.mul_assoc]
    exact Nat.mul_lt_mul_of_pos_left hlo (by positivity)
  · rintro ⟨_, _, hj, hbf⟩
    have hjP : 2 ^ p2_of n = 2 ^ p2_of i * 2 ^ j := by
      rw [← pow_add]
      congr 1
      omega
    constructor
    · rw [hjP, Nat.mul_assoc] at hbf
      exact Nat.lt_of_mul_lt_mul_left hbf
    · rw [hjP, Nat.mul_comm (2 ^ p2_of i) (2 ^ j)]
      exact Nat.mul_lt_mul_of_pos_left hPi (by positivity)

/-- 3^a 2^p2(n) and 3^n 2^p2(a) differ for a < n. -/
theorem three_pow_mul_ne {a n : ℕ} (han : a < n) :
    3 ^ a * 2 ^ p2_of n ≠ 3 ^ n * 2 ^ p2_of a := by
  intro h
  obtain ⟨e, he⟩ : ∃ e, n = a + (e + 1) := ⟨n - a - 1, by omega⟩
  rw [he, pow_add, Nat.mul_assoc] at h
  have h1 : 2 ^ p2_of (a + (e + 1)) = 3 ^ (e + 1) * 2 ^ p2_of a :=
    Nat.eq_of_mul_eq_mul_left (by positivity) h
  have h3 : 3 ∣ 2 ^ p2_of (a + (e + 1)) := by
    rw [h1, pow_succ]
    exact Dvd.dvd.mul_right (Dvd.intro_left _ rfl) _
  have h4 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
  omega

/-- No 3-smooth number lies strictly between 3^n and 2^p2(n) exactly when n is an upper
    record Order. -/
theorem upperRecord_iff_none_between {n : ℕ} :
    UpperRecord n ↔
      ∀ i j, ¬(3 ^ n < 2 ^ j * 3 ^ i ∧ 2 ^ j * 3 ^ i < 2 ^ p2_of n) := by
  rw [upperRecord_iff_blockFactor]
  constructor
  · intro h i j hb
    obtain ⟨hi1, hin, _, hbf⟩ := smooth_between_iff.mp hb
    have hlt := (blockFactor_lt_iff_nat i n).mp (h i hi1 hin)
    have hc : 2 ^ p2_of i * 3 ^ n = 3 ^ n * 2 ^ p2_of i := Nat.mul_comm _ _
    have hd : 2 ^ p2_of n * 3 ^ i = 3 ^ i * 2 ^ p2_of n := Nat.mul_comm _ _
    omega
  · intro h a ha1 han
    rw [blockFactor_lt_iff_nat]
    rcases lt_trichotomy (3 ^ a * 2 ^ p2_of n) (3 ^ n * 2 ^ p2_of a) with hlt | heq | hgt
    · exact hlt
    · exact absurd heq (three_pow_mul_ne han)
    · exfalso
      have hle := p2_of_mono (le_of_lt han)
      apply h a (p2_of n - p2_of a)
      rw [smooth_between_iff]
      refine ⟨ha1, han, by omega, ?_⟩
      have hc : 2 ^ p2_of a * 3 ^ n = 3 ^ n * 2 ^ p2_of a := Nat.mul_comm _ _
      have hd : 2 ^ p2_of n * 3 ^ a = 3 ^ a * 2 ^ p2_of n := Nat.mul_comm _ _
      omega

end AcceleratedCollatz
