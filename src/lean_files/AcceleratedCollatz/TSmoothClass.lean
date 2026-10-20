-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TBlockRecord
import AcceleratedCollatz.TSmoothClassQ

/-!
  The 3-smooth numbers by their number of binary digits (paper sec:sweeps), the q = 3
  case of `TLastRecordsQ` and `TSmoothClassQ`. 2^j 3^i has j + p2(i) binary digits
  (`smooth_lt_two_pow_iff`, `smooth_digits`), so the 3-smooth numbers of k binary digits
  are 2^(k - p2(i)) 3^i for the Orders i below the round-up of k log 2 / log 3
  (`p2_of_le_iff_lt_clog`), and the number of 3-smooth numbers below 2^B is the sum of
  these round-ups over k ≤ B (`card_smoothBelow`). Among the numbers of B binary digits
  a larger block factor gives a larger number (`smooth_class_lt_iff`). With a the last
  lower and b the last upper record Order below some N ≥ 2 (`LastRecords`,
  `lastRecords_iff`, `exists_lastRecords`, `lastRecords_unique`): N ≤ a + b
  (`le_add_of_lastRecords`), the next record Order of either kind is a + b
  (`eq_add_of_lowerRecord`, `eq_add_of_upperRecord`), a p2(b) + b = b p2(a) + 1
  (`lastRecords_det`), the block factor rises along k a mod (a + b)
  (`blockFactor_mul_mod_lt`), which takes every Order below a + b
  (`exists_mul_mod_eq_of_lastRecords`). So the 3-smooth numbers of B binary digits rise
  along i = k a mod (a + b) (`smooth_class_mul_mod_lt`).
-/

namespace AcceleratedCollatz

/-- a is the last lower record Order below N, and b the last upper record Order
    below N. -/
def LastRecords (a b N : ℕ) : Prop := LastRecordsQ 3 a b N

/-- `LastRecords` in terms of `LowerRecord` and `UpperRecord`. -/
theorem lastRecords_iff (a b N : ℕ) :
    LastRecords a b N ↔
      (1 ≤ a ∧ a < N ∧ LowerRecord a ∧ ∀ x, a < x → x < N → ¬LowerRecord x) ∧
        (1 ≤ b ∧ b < N ∧ UpperRecord b ∧ ∀ x, b < x → x < N → ¬UpperRecord x) := by
  constructor
  · intro h
    exact ⟨⟨h.one_le_lower, h.lower_lt, h.lower, h.no_lower⟩,
      ⟨h.one_le_upper, h.upper_lt, h.upper, h.no_upper⟩⟩
  · intro h
    exact ⟨h.1.1, h.1.2.1, h.1.2.2.1, h.1.2.2.2, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

/-- Below 2 both last record Orders are 1. -/
theorem lastRecords_two : LastRecords 1 1 2 :=
  lastRecordsQ_two 3

/-- Every N ≥ 2 has last record Orders below it. -/
theorem exists_lastRecords {N : ℕ} (hN : 2 ≤ N) : ∃ a b, LastRecords a b N :=
  exists_lastRecordsQ (by decide) le_rfl hN

/-- The last record Orders below N are unique. -/
theorem lastRecords_unique {a b a' b' N : ℕ} (h : LastRecords a b N)
    (h' : LastRecords a' b' N) : a = a' ∧ b = b' :=
  lastRecordsQ_unique h h'

/-- N ≤ a + b. -/
theorem le_add_of_lastRecords {a b N : ℕ} (h : LastRecords a b N) : N ≤ a + b :=
  le_add_of_lastRecordsQ (by decide) le_rfl h

/-- A lower record Order N, with last record Orders a and b below it, is a + b. -/
theorem eq_add_of_lowerRecord {a b N : ℕ} (h : LastRecords a b N) (hR : LowerRecord N) :
    N = a + b :=
  eq_add_of_lowerRecordQ le_rfl h hR

/-- An upper record Order N, with last record Orders a and b below it, is a + b. -/
theorem eq_add_of_upperRecord {a b N : ℕ} (h : LastRecords a b N) (hR : UpperRecord N) :
    N = a + b :=
  eq_add_of_upperRecordQ (by decide) le_rfl h hR

/-- a and b are also the last record Orders below a + b. -/
theorem lastRecords_add {a b N : ℕ} (h : LastRecords a b N) : LastRecords a b (a + b) :=
  lastRecordsQ_add (by decide) le_rfl h

/-- a p2(b) + b = b p2(a) + 1. -/
theorem lastRecords_det {a b N : ℕ} (h : LastRecords a b N) :
    a * p2_of b + b = b * p2_of a + 1 :=
  lastRecordsQ_det (by decide) le_rfl h

/-- a and b are coprime. -/
theorem coprime_of_lastRecords {a b N : ℕ} (h : LastRecords a b N) : Nat.Coprime a b :=
  coprime_of_lastRecordsQ (by decide) le_rfl h

/-- The block factor rises along k a mod (a + b), k = 0, 1, …, a + b - 1. -/
theorem blockFactor_mul_mod_lt {a b N : ℕ} (h : LastRecords a b N) {k k' : ℕ} (hkk : k < k')
    (hk' : k' < a + b) : blockFactor (k * a % (a + b)) < blockFactor (k' * a % (a + b)) :=
  blockFactorQ_mul_mod_lt (by decide) le_rfl h hkk hk'

/-- Every Order below a + b is k a mod (a + b) for some k below a + b. -/
theorem exists_mul_mod_eq_of_lastRecords {a b N : ℕ} (h : LastRecords a b N) {i : ℕ}
    (hi : i < a + b) : ∃ k, k < a + b ∧ k * a % (a + b) = i :=
  exists_mul_mod_eq (by decide) le_rfl h hi

/-- 2^j 3^i < 2^B exactly when j + p2(i) ≤ B. -/
theorem smooth_lt_two_pow_iff {j i B : ℕ} : 2 ^ j * 3 ^ i < 2 ^ B ↔ j + p2_of i ≤ B :=
  smoothQ_lt_two_pow_iff le_rfl

/-- 2^j 3^i has k binary digits exactly when j + p2(i) = k. -/
theorem smooth_digits {j i k : ℕ} (hk : 1 ≤ k) :
    (2 ^ (k - 1) ≤ 2 ^ j * 3 ^ i ∧ 2 ^ j * 3 ^ i < 2 ^ k) ↔ j + p2_of i = k :=
  smoothQ_digits le_rfl hk

/-- The Orders i with p2(i) ≤ k are those below the round-up of k log 2 / log 3. -/
theorem p2_of_le_iff_lt_clog (i k : ℕ) : p2_of i ≤ k ↔ i < Nat.clog 3 (2 ^ k) :=
  p2Q_le_iff_lt_clog le_rfl i k

/-- The pairs (j, i) with 2^j 3^i < 2^B. -/
def smoothBelow (B : ℕ) : Finset (ℕ × ℕ) := smoothBelowQ 3 B

/-- (j, i) is in `smoothBelow B` exactly when 2^j 3^i < 2^B. -/
theorem mem_smoothBelow {B : ℕ} {p : ℕ × ℕ} :
    p ∈ smoothBelow B ↔ 2 ^ p.1 * 3 ^ p.2 < 2 ^ B :=
  mem_smoothBelowQ le_rfl

/-- The number of 3-smooth numbers below 2^B, as pairs (j, i), is the sum over k ≤ B of
    the round-ups of k log 2 / log 3. -/
theorem card_smoothBelow (B : ℕ) :
    (smoothBelow B).card = ∑ k ∈ Finset.range (B + 1), Nat.clog 3 (2 ^ k) :=
  card_smoothBelowQ le_rfl B

/-- Among the 3-smooth numbers of B binary digits, 2^(B - p2(i)) 3^i is below
    2^(B - p2(i')) 3^i' exactly when the block factor of i is below that of i'. -/
theorem smooth_class_lt_iff {i i' B : ℕ} (hi : p2_of i ≤ B) (hi' : p2_of i' ≤ B) :
    2 ^ (B - p2_of i) * 3 ^ i < 2 ^ (B - p2_of i') * 3 ^ i' ↔
      blockFactor i < blockFactor i' :=
  smoothQ_class_lt_iff hi hi'

/-- The 3-smooth numbers of B binary digits rise along i = k a mod (a + b), k = 0, 1, …,
    for the last record Orders a and b below some N. -/
theorem smooth_class_mul_mod_lt {a b N B : ℕ} (h : LastRecords a b N) {k k' : ℕ}
    (hkk : k < k') (hk' : k' < a + b) (hi : p2_of (k * a % (a + b)) ≤ B)
    (hi' : p2_of (k' * a % (a + b)) ≤ B) :
    2 ^ (B - p2_of (k * a % (a + b))) * 3 ^ (k * a % (a + b)) <
      2 ^ (B - p2_of (k' * a % (a + b))) * 3 ^ (k' * a % (a + b)) :=
  smoothQ_class_mul_mod_lt (by decide) le_rfl h hkk hk' hi hi'

end AcceleratedCollatz
