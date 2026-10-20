-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TBlockRecordQ
import AcceleratedCollatz.TBudget
import AcceleratedCollatz.TGridOrder
import AcceleratedCollatz.TRecordGapQ

/-!
  Record Orders by the block factor (paper fig:blockfactor), the q = 3 case of
  `TBlockRecordQ`. The block factor f(o) = 3^o / 2^p2(o) (`blockFactor`) is the level
  change across an admissible word of Order o (`seqProduct_eq_blockFactor`) and the
  reciprocal of the deficit ratio (`blockFactor_eq_inv`). The upper record Orders of
  `TGridOrder` are the Orders whose block factor is above every earlier one
  (`upperRecord_iff_blockFactor`), the lower record Orders those whose block factor is
  below every earlier one (`lowerRecord_iff_blockFactor`). In terms of p2 alone: at a
  lower record Order p2(n) = p2(a) + p2(n - a) for every 1 ≤ a < n
  (`lowerRecord_iff_add`), at an upper record Order p2(n) + 1 = p2(a) + p2(n - a)
  (`upperRecord_iff_add`). The gap between two neighbouring lower record Orders is an
  upper record Order (`upperRecord_sub_of_lowerRecord`), the gap between two
  neighbouring upper record Orders a lower one (`lowerRecord_sub_of_upperRecord`).
-/

namespace AcceleratedCollatz

/-- Block factor f(o) = 3^o / 2^p2(o): the level change across a block of Order o. -/
def blockFactor (o : ℕ) : ℚ := blockFactorQ 3 o

/-- f(o) = 3^o / 2^p2(o). -/
theorem blockFactor_eq (o : ℕ) : blockFactor o = 3 ^ o / 2 ^ p2_of o := by
  unfold blockFactor blockFactorQ
  rw [p2Q_three]
  norm_num

/-- The block factor is the reciprocal of the deficit ratio. -/
theorem blockFactor_eq_inv (o : ℕ) : blockFactor o = (deficitRatio o)⁻¹ := by
  rw [blockFactor_eq, deficitRatio, inv_div]

/-- An admissible word of Order o multiplies the level by f(o). -/
theorem seqProduct_eq_blockFactor {s : List Bool} (hA : Admissible s) :
    seqProduct s = blockFactor (order s) := by
  rw [blockFactor_eq, ← admissible_length s hA, eq_div_iff (by positivity)]
  exact seqProduct_mul_pow s

/-- Lower record Orders: p2(n) = p2(a) + p2(n - a) at every split. -/
theorem lowerRecord_iff_add (n : ℕ) :
    LowerRecord n ↔ ∀ a, 1 ≤ a → a < n → p2_of n = p2_of a + p2_of (n - a) :=
  lowerRecordQ_iff_add le_rfl n

/-- Upper record Orders: p2(n) + 1 = p2(a) + p2(n - a) at every split. -/
theorem upperRecord_iff_add (n : ℕ) :
    UpperRecord n ↔ ∀ a, 1 ≤ a → a < n → p2_of n + 1 = p2_of a + p2_of (n - a) :=
  upperRecordQ_iff_add le_rfl n

/-- Lower record Orders are the Orders whose block factor is below every earlier one. -/
theorem lowerRecord_iff_blockFactor (n : ℕ) :
    LowerRecord n ↔ ∀ a, 1 ≤ a → a < n → blockFactor n < blockFactor a :=
  lowerRecordQ_iff_blockFactorQ le_rfl n

/-- Upper record Orders are the Orders whose block factor is above every earlier one. -/
theorem upperRecord_iff_blockFactor (n : ℕ) :
    UpperRecord n ↔ ∀ a, 1 ≤ a → a < n → blockFactor a < blockFactor n :=
  upperRecordQ_iff_blockFactorQ (by decide) le_rfl n

/-- Between two neighbouring lower record Orders a < b the gap b - a is an upper record
    Order. -/
theorem upperRecord_sub_of_lowerRecord {a b : ℕ} (ha : 1 ≤ a) (hab : a < b)
    (hRa : LowerRecord a) (hRb : LowerRecord b)
    (hnone : ∀ x, a < x → x < b → ¬LowerRecord x) : UpperRecord (b - a) :=
  upperRecordQ_sub_of_lowerRecordQ le_rfl ha hab hRa hRb hnone

/-- Between two neighbouring upper record Orders a < b the gap b - a is a lower record
    Order. -/
theorem lowerRecord_sub_of_upperRecord {a b : ℕ} (ha : 1 ≤ a) (hab : a < b)
    (hRa : UpperRecord a) (hRb : UpperRecord b)
    (hnone : ∀ x, a < x → x < b → ¬UpperRecord x) : LowerRecord (b - a) :=
  lowerRecordQ_sub_of_upperRecordQ (by decide) le_rfl ha hab hRa hRb hnone

/-- Between a lower record Order a and the next one, p2(a + i) + 1 = p2(a) + p2(i). -/
theorem p2_of_add_of_lowerRecord {a b : ℕ} (hRa : LowerRecord a)
    (hnone : ∀ x, a < x → x < b → ¬LowerRecord x) {i : ℕ} (hi : 1 ≤ i) (hib : a + i < b) :
    p2_of (a + i) + 1 = p2_of a + p2_of i :=
  p2Q_add_of_lowerRecordQ le_rfl hRa hnone hi hib

end AcceleratedCollatz
