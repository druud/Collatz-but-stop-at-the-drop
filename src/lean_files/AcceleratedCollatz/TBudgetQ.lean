-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TChainQ

/-!
  Deficit budget of the q-family (odd q ≥ 3). The deficit ratio of an Order,
  D(o) = 2^p2Q(o) / q^o, lies in (1, 2]; it is 2 for o = 0 and below 2 for o ≥ 1
  (`one_lt_deficitRatioQ`, `deficitRatioQ_zero`, `deficitRatioQ_lt_two`). The level
  after a leading 1 and blocks of Orders os is above 1 iff 2 ∏ D(o_i) < q
  (`levelUpQ_iff_budgetQ`). So the admissible words of Order ≥ 1 are the words
  1 :: (B1 ++ ... ++ Bm) with admissible blocks whose Orders satisfy
  2 ∏_{i<m} D(o_i) < q and not 2 ∏_{i≤m} D(o_i) < q
  (`admissibleQ_iff_exists_chain_budgetQ`).
-/

namespace AcceleratedCollatz

variable {q : ℕ}

/-- Deficit ratio D(o) = 2^p2Q(o) / q^o, the reciprocal of the block factor. -/
def deficitRatioQ (q o : ℕ) : ℚ := 2 ^ p2Q q o / (q : ℚ) ^ o

/-- 1 < D(o): every block lowers the level. -/
theorem one_lt_deficitRatioQ (hq : 3 ≤ q) (o : ℕ) : 1 < deficitRatioQ q o := by
  unfold deficitRatioQ
  have hq0 : (0 : ℚ) < q := by
    exact_mod_cast (by omega : 0 < q)
  have hpos : (0 : ℚ) < (q : ℚ) ^ o := pow_pos hq0 o
  have hlt : (q : ℚ) ^ o < 2 ^ p2Q q o := by
    exact_mod_cast p2Q_spec hq o
  rw [lt_div_iff₀ hpos, one_mul]
  exact hlt

/-- D(o) ≤ 2: a block at most halves the level. -/
theorem deficitRatioQ_le_two (hq : 3 ≤ q) (o : ℕ) : deficitRatioQ q o ≤ 2 := by
  unfold deficitRatioQ
  have hq0 : (0 : ℚ) < q := by
    exact_mod_cast (by omega : 0 < q)
  have hpos : (0 : ℚ) < (q : ℚ) ^ o := pow_pos hq0 o
  have hn : (2 : ℚ) ^ (p2Q q o - 1) ≤ (q : ℚ) ^ o := by
    exact_mod_cast p2Q_spec_lower hq o
  have hone := one_le_p2Q q o
  have hp : p2Q q o = (p2Q q o - 1) + 1 := by
    omega
  rw [div_le_iff₀ hpos, hp, pow_succ]
  linarith

/-- D(0) = 2: the block [0] halves the level. -/
theorem deficitRatioQ_zero (q : ℕ) : deficitRatioQ q 0 = 2 := by
  simp [deficitRatioQ, p2Q]

/-- For odd q, D(o) < 2 for a block of Order ≥ 1. -/
theorem deficitRatioQ_lt_two (hodd : Odd q) (hq : 3 ≤ q) {o : ℕ} (ho : 1 ≤ o) :
    deficitRatioQ q o < 2 := by
  apply lt_of_le_of_ne (deficitRatioQ_le_two hq o)
  intro h
  unfold deficitRatioQ at h
  have hq0 : (0 : ℚ) < q := by
    exact_mod_cast (by omega : 0 < q)
  have hpos : (0 : ℚ) < (q : ℚ) ^ o := pow_pos hq0 o
  rw [div_eq_iff hpos.ne'] at h
  have hone := one_le_p2Q q o
  have hp : p2Q q o = (p2Q q o - 1) + 1 := by
    omega
  rw [hp, pow_succ] at h
  have h2 : (2 : ℚ) ^ (p2Q q o - 1) = (q : ℚ) ^ o := by
    linarith
  have hnat : 2 ^ (p2Q q o - 1) = q ^ o := by
    exact_mod_cast h2
  exact two_pow_ne_q_pow hodd hq ho hnat

/-- ∏ D(o_i) = 2^(Σ p2Q(o_i)) / q^(Σ o_i). -/
theorem prod_deficitRatioQ (q : ℕ) (os : List ℕ) :
    (os.map (deficitRatioQ q)).prod = 2 ^ (os.map (p2Q q)).sum / (q : ℚ) ^ os.sum := by
  induction os with
  | nil =>
    simp
  | cons o t ih =>
    rw [List.map_cons, List.prod_cons, ih, List.map_cons, List.sum_cons, List.sum_cons,
      pow_add, pow_add, deficitRatioQ, div_mul_div_comm]

/-- Budget form of `LevelUpQ`: 2 ∏ D(o_i) < q. -/
theorem levelUpQ_iff_budgetQ (hq : 3 ≤ q) (os : List ℕ) :
    LevelUpQ q os ↔ 2 * (os.map (deficitRatioQ q)).prod < q := by
  rw [prod_deficitRatioQ]
  have hq0 : (0 : ℚ) < q := by
    exact_mod_cast (by omega : 0 < q)
  have hpos : (0 : ℚ) < (q : ℚ) ^ os.sum := pow_pos hq0 _
  rw [← mul_div_assoc, div_lt_iff₀ hpos]
  unfold LevelUpQ
  rw [pow_add, pow_add, pow_one, pow_one]
  constructor
  · intro h
    exact_mod_cast h
  · intro h
    exact_mod_cast h

/-- The admissible words of Order ≥ 1 in budget form: 1 :: (B1 ++ ... ++ Bm) with
    admissible blocks, 2 ∏ D(o_i) < q over all blocks but the last, and not over all. -/
theorem admissibleQ_iff_exists_chain_budgetQ (hodd : Odd q) (hq : 3 ≤ q) (s : List Bool) :
    (AdmissibleQ q s ∧ 1 ≤ order s) ↔
      ∃ bs, IsSplitQ q s bs ∧
        2 * ((bs.map order).dropLast.map (deficitRatioQ q)).prod < q ∧
          ¬2 * ((bs.map order).map (deficitRatioQ q)).prod < q := by
  simp only [← levelUpQ_iff_budgetQ hq]
  exact admissibleQ_iff_exists_chainQ hodd hq s

end AcceleratedCollatz
