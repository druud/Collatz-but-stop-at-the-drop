-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TChainOrders

/-!
  Deficit budget. Every block lowers the level (3^o < 2^p2(o)), so the levels at
  the cuts decrease, and validity needs checking only at the last inner cut:
  `ValidOrders os ↔ LevelUp os.dropLast` (`validOrders_iff_dropLast`). In rational
  form, with the deficit ratio D(o) = 2^p2(o) / 3^o in (1, 2]: `LevelUp os` iff
  2 ∏ D(o_i) < 3 (`levelUp_iff_budget`), and validity iff 2 ∏_{i<k} D(o_i) < 3
  (`validOrders_iff_budget`).
-/

namespace AcceleratedCollatz

/-- 3^(Σo) ≤ 2^(Σp2(o)): blocks never raise the level. -/
theorem three_pow_sum_le (os : List ℕ) : 3 ^ os.sum ≤ 2 ^ (os.map p2_of).sum := by
  induction os with
  | nil =>
    simp
  | cons o os ih =>
    rw [List.sum_cons, List.map_cons, List.sum_cons, pow_add, pow_add]
    exact Nat.mul_le_mul (p2_of_spec o).le ih

/-- `LevelUp` of a longer list implies it for a prefix. -/
theorem levelUp_of_append (a b : List ℕ) (h : LevelUp (a ++ b)) : LevelUp a := by
  unfold LevelUp at h ⊢
  rw [List.map_append, List.sum_append, List.sum_append, ← add_assoc, ← add_assoc,
    pow_add 2 (1 + (a.map p2_of).sum), pow_add 3 (1 + a.sum)] at h
  have hb := three_pow_sum_le b
  by_contra hcon
  have hge : 3 ^ (1 + a.sum) ≤ 2 ^ (1 + (a.map p2_of).sum) := Nat.le_of_not_lt hcon
  have hmul := Nat.mul_le_mul hge hb
  omega

/-- `LevelUp []`: the level 3/2 after the leading 1. -/
theorem levelUp_nil : LevelUp [] := by
  unfold LevelUp
  norm_num

/-- Deficit budget: the Orders are valid iff the level at the last inner cut is > 1. -/
theorem validOrders_iff_dropLast (os : List ℕ) : ValidOrders os ↔ LevelUp os.dropLast := by
  constructor
  · intro h
    rcases Nat.lt_or_ge os.length 2 with hlen | hlen
    · have hd : os.dropLast = [] := by
        rw [← List.length_eq_zero_iff, List.length_dropLast]
        omega
      rw [hd]
      exact levelUp_nil
    · have hi := h (os.length - 1) (by omega) (by omega)
      rwa [← List.dropLast_eq_take] at hi
  · intro h i hi1 hi
    have ht : os.dropLast.take i = os.take i := by
      rw [List.dropLast_eq_take, List.take_take, min_eq_left (by omega)]
    have hsplit : os.dropLast = os.take i ++ os.dropLast.drop i := by
      rw [← ht, List.take_append_drop]
    rw [hsplit] at h
    exact levelUp_of_append _ _ h

/-- `LevelUp` of all Orders (tail [0]) implies validity. -/
theorem validOrders_of_levelUp (os : List ℕ) (h : LevelUp os) : ValidOrders os := by
  rw [validOrders_iff_dropLast]
  apply levelUp_of_append os.dropLast (os.drop (os.length - 1))
  rwa [List.dropLast_eq_take, List.take_append_drop]

/-- Deficit ratio D(o) = 2^p2(o) / 3^o, the reciprocal of the block factor. -/
def deficitRatio (o : ℕ) : ℚ := 2 ^ p2_of o / 3 ^ o

/-- 1 < D(o): every block lowers the level. -/
theorem one_lt_deficitRatio (o : ℕ) : 1 < deficitRatio o := by
  unfold deficitRatio
  have h3 : (0 : ℚ) < 3 ^ o := by
    positivity
  have hlt : (3 : ℚ) ^ o < 2 ^ p2_of o := by
    exact_mod_cast p2_of_spec o
  rw [lt_div_iff₀ h3, one_mul]
  exact hlt

/-- D(o) ≤ 2: a block at most halves the level. -/
theorem deficitRatio_le_two (o : ℕ) : deficitRatio o ≤ 2 := by
  unfold deficitRatio
  have h3 : (0 : ℚ) < 3 ^ o := by
    positivity
  have hn : (2 : ℚ) ^ (p2_of o - 1) ≤ 3 ^ o := by
    exact_mod_cast p2_of_spec_lower o
  have hp : p2_of o = (p2_of o - 1) + 1 := by
    unfold p2_of
    omega
  rw [div_le_iff₀ h3, hp, pow_succ]
  linarith

/-- ∏ D(o_i) = 2^(Σ p2(o_i)) / 3^(Σ o_i). -/
theorem prod_deficitRatio (os : List ℕ) :
    (os.map deficitRatio).prod = 2 ^ (os.map p2_of).sum / 3 ^ os.sum := by
  induction os with
  | nil =>
    simp
  | cons o t ih =>
    rw [List.map_cons, List.prod_cons, ih, List.map_cons, List.sum_cons, List.sum_cons,
      pow_add, pow_add, deficitRatio, div_mul_div_comm]

/-- Budget form of `LevelUp`: 2 ∏ D(o_i) < 3. -/
theorem levelUp_iff_budget (os : List ℕ) :
    LevelUp os ↔ 2 * (os.map deficitRatio).prod < 3 := by
  rw [prod_deficitRatio]
  have h3 : (0 : ℚ) < 3 ^ os.sum := by
    positivity
  rw [← mul_div_assoc, div_lt_iff₀ h3]
  unfold LevelUp
  rw [pow_add, pow_add, pow_one, pow_one]
  constructor
  · intro h
    exact_mod_cast h
  · intro h
    exact_mod_cast h

/-- Budget form of validity: 2 ∏_{i<k} D(o_i) < 3. -/
theorem validOrders_iff_budget (os : List ℕ) :
    ValidOrders os ↔ 2 * (os.dropLast.map deficitRatio).prod < 3 := by
  rw [validOrders_iff_dropLast, levelUp_iff_budget]

/-- Admissible words of Order ≥ 1 in budget form: chain blocks with
    2 ∏_{i<k} D(o_i) < 3, and tail [0] iff moreover 2 ∏_{i≤k} D(o_i) < 3. -/
theorem admissible_iff_chain_budget (s : List Bool) :
    (Admissible s ∧ 1 ≤ order s) ↔
      ∃ (bs : List (List Bool)) (t : List Bool),
        s = true :: (bs.flatten ++ t) ∧ (∀ b ∈ bs, IsChainBlock b) ∧
        2 * ((bs.map order).dropLast.map deficitRatio).prod < 3 ∧
        ((2 * ((bs.map order).map deficitRatio).prod < 3 ∧ t = [false]) ∨
          (¬ 2 * ((bs.map order).map deficitRatio).prod < 3 ∧ t = [])) := by
  simp only [← levelUp_iff_budget, ← validOrders_iff_dropLast]
  exact admissible_iff_chain s

end AcceleratedCollatz
