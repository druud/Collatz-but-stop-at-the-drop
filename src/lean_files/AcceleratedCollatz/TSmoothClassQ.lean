-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TLastRecordsQ

/-!
  The numbers 2^j q^i by their number of binary digits (odd q ≥ 3). 2^j q^i has
  j + p2Q(i) binary digits (`smoothQ_lt_two_pow_iff`, `smoothQ_digits`). So the numbers
  of k binary digits are 2^(k - p2Q(i)) q^i, one for each Order i with p2Q(i) ≤ k: the
  Orders below the round-up of k log 2 / log q (`p2Q_le_iff_lt_clog`). The number of
  pairs (j, i) with 2^j q^i < 2^B is the sum of these round-ups over k ≤ B
  (`card_smoothBelowQ`). Within the numbers of B binary digits, a larger block factor
  gives a larger number (`smoothQ_class_lt_iff`); so with the last record Orders a and b
  below some N, these numbers rise along i = k a mod (a + b), k = 0, 1, …
  (`smoothQ_class_mul_mod_lt`).
-/

namespace AcceleratedCollatz

variable {q : ℕ}

/-- 2^j q^i < 2^B exactly when j + p2Q(i) ≤ B. -/
theorem smoothQ_lt_two_pow_iff (hq : 3 ≤ q) {j i B : ℕ} :
    2 ^ j * q ^ i < 2 ^ B ↔ j + p2Q q i ≤ B := by
  rw [Nat.mul_comm]
  exact q_pow_mul_lt_iff hq

/-- 2^j q^i has k binary digits exactly when j + p2Q(i) = k. -/
theorem smoothQ_digits (hq : 3 ≤ q) {j i k : ℕ} (hk : 1 ≤ k) :
    (2 ^ (k - 1) ≤ 2 ^ j * q ^ i ∧ 2 ^ j * q ^ i < 2 ^ k) ↔ j + p2Q q i = k := by
  rw [← not_lt, smoothQ_lt_two_pow_iff hq, smoothQ_lt_two_pow_iff hq]
  omega

/-- The Orders i with p2Q(i) ≤ k are those below the round-up of k log 2 / log q. -/
theorem p2Q_le_iff_lt_clog (hq : 3 ≤ q) (i k : ℕ) :
    p2Q q i ≤ k ↔ i < Nat.clog q (2 ^ k) := by
  rw [← q_pow_lt_two_pow_iff hq, Nat.lt_clog_iff_pow_lt (by omega)]

/-- i < p2Q(i). -/
theorem lt_p2Q (hq : 3 ≤ q) (i : ℕ) : i < p2Q q i := by
  have h1 : 2 ^ i ≤ q ^ i := Nat.pow_le_pow_left (by omega) i
  have h2 := lt_of_le_of_lt h1 (p2Q_spec hq i)
  exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp h2

/-- The pairs (j, i) with 2^j q^i < 2^B. -/
def smoothBelowQ (q B : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range B ×ˢ Finset.range B).filter (fun p => 2 ^ p.1 * q ^ p.2 < 2 ^ B)

/-- (j, i) is in `smoothBelowQ q B` exactly when 2^j q^i < 2^B. -/
theorem mem_smoothBelowQ (hq : 3 ≤ q) {B : ℕ} {p : ℕ × ℕ} :
    p ∈ smoothBelowQ q B ↔ 2 ^ p.1 * q ^ p.2 < 2 ^ B := by
  unfold smoothBelowQ
  rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]
  constructor
  · intro h
    exact h.2
  · intro h
    have h1 := (smoothQ_lt_two_pow_iff hq).mp h
    have h2 := lt_p2Q hq p.2
    have h3 := one_le_p2Q q p.2
    exact ⟨⟨by omega, by omega⟩, h⟩

/-- The number of pairs (j, i) with 2^j q^i < 2^B is the sum over k ≤ B of the
    round-ups of k log 2 / log q. -/
theorem card_smoothBelowQ (hq : 3 ≤ q) (B : ℕ) :
    (smoothBelowQ q B).card = ∑ k ∈ Finset.range (B + 1), Nat.clog q (2 ^ k) := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun p => p.1 + p2Q q p.2)
    (t := Finset.range (B + 1))]
  · apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range] at hk
    have himg : (smoothBelowQ q B).filter (fun p => p.1 + p2Q q p.2 = k) =
        (Finset.range (Nat.clog q (2 ^ k))).image (fun i => (k - p2Q q i, i)) := by
      ext p
      rw [Finset.mem_filter, mem_smoothBelowQ hq, smoothQ_lt_two_pow_iff hq, Finset.mem_image]
      constructor
      · intro hp
        refine ⟨p.2, ?_, ?_⟩
        · rw [Finset.mem_range, ← p2Q_le_iff_lt_clog hq]
          omega
        · apply Prod.ext
          · change k - p2Q q p.2 = p.1
            omega
          · rfl
      · intro hp
        obtain ⟨i, hi, hip⟩ := hp
        rw [Finset.mem_range, ← p2Q_le_iff_lt_clog hq] at hi
        rw [← hip]
        change k - p2Q q i + p2Q q i ≤ B ∧ k - p2Q q i + p2Q q i = k
        omega
    rw [himg, Finset.card_image_of_injective, Finset.card_range]
    intro x y hxy
    exact (Prod.ext_iff.mp hxy).2
  · intro p hp
    rw [Finset.mem_coe, mem_smoothBelowQ hq, smoothQ_lt_two_pow_iff hq] at hp
    rw [Finset.mem_coe, Finset.mem_range]
    change p.1 + p2Q q p.2 < B + 1
    omega

/-- Among the numbers of B binary digits, 2^(B - p2Q(i)) q^i is below
    2^(B - p2Q(i')) q^i' exactly when the block factor of i is below that of i'. -/
theorem smoothQ_class_lt_iff {i i' B : ℕ} (hi : p2Q q i ≤ B) (hi' : p2Q q i' ≤ B) :
    2 ^ (B - p2Q q i) * q ^ i < 2 ^ (B - p2Q q i') * q ^ i' ↔
      blockFactorQ q i < blockFactorQ q i' := by
  rw [blockFactorQ_lt_iff]
  have hL : 2 ^ (B - p2Q q i) * q ^ i * (2 ^ p2Q q i * 2 ^ p2Q q i') =
      q ^ i * 2 ^ p2Q q i' * 2 ^ B := by
    have hB : 2 ^ B = 2 ^ (B - p2Q q i) * 2 ^ p2Q q i := by
      rw [← pow_add, Nat.sub_add_cancel hi]
    rw [hB]
    ring
  have hR : 2 ^ (B - p2Q q i') * q ^ i' * (2 ^ p2Q q i * 2 ^ p2Q q i') =
      q ^ i' * 2 ^ p2Q q i * 2 ^ B := by
    have hB : 2 ^ B = 2 ^ (B - p2Q q i') * 2 ^ p2Q q i' := by
      rw [← pow_add, Nat.sub_add_cancel hi']
    rw [hB]
    ring
  rw [← Nat.mul_lt_mul_right (a := 2 ^ p2Q q i * 2 ^ p2Q q i') (by positivity), hL, hR,
    Nat.mul_lt_mul_right (by positivity)]

/-- The numbers of B binary digits rise along i = k a mod (a + b), k = 0, 1, …, for the
    last record Orders a and b below some N. -/
theorem smoothQ_class_mul_mod_lt (hodd : Odd q) (hq : 3 ≤ q) {a b N B : ℕ}
    (h : LastRecordsQ q a b N) {k k' : ℕ} (hkk : k < k') (hk' : k' < a + b)
    (hi : p2Q q (k * a % (a + b)) ≤ B) (hi' : p2Q q (k' * a % (a + b)) ≤ B) :
    2 ^ (B - p2Q q (k * a % (a + b))) * q ^ (k * a % (a + b)) <
      2 ^ (B - p2Q q (k' * a % (a + b))) * q ^ (k' * a % (a + b)) :=
  (smoothQ_class_lt_iff hi hi').mpr (blockFactorQ_mul_mod_lt hodd hq h hkk hk')

end AcceleratedCollatz
