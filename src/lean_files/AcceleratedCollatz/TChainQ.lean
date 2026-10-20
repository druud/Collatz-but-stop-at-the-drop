-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TSplitQ

/-!
  The chain form of the q-family (odd q ≥ 3) depends only on the Orders of the blocks.
  With `LevelUpQ q os` (the level q^(1+Σo) / 2^(1+Σp2Q(o)) after a leading 1 and blocks
  of Orders os is above 1): for admissible blocks B1 .. Bm, of any Orders, the word
  1 :: (B1 ++ ... ++ Bm) is admissible iff `LevelUpQ` holds for the Orders of all blocks
  but the last and fails for the Orders of all of them (`admissibleQ_iff_chainQ`). A
  block lowers the level (`levelUpQ_of_append`), so the level is then above 1 at every
  inner block boundary. The admissible words of Order ≥ 1 are exactly these chains
  (`admissibleQ_iff_exists_chainQ`), each in one way (`splitQ_unique`). For q = 3 an
  Order-0 block can only be the last one; for q ≥ 5 it can follow the leading 1.
-/

namespace AcceleratedCollatz

variable {q : ℕ}

/-- Level after a leading 1 and blocks of Orders os is above 1. -/
def LevelUpQ (q : ℕ) (os : List ℕ) : Prop :=
  2 ^ (1 + (os.map (p2Q q)).sum) < q ^ (1 + os.sum)

/-- `LevelUpQ` is decidable. -/
instance (q : ℕ) (os : List ℕ) : Decidable (LevelUpQ q os) := by
  unfold LevelUpQ
  infer_instance

/-- After the leading 1 alone the level is above 1. -/
theorem levelUpQ_nil (hq : 3 ≤ q) : LevelUpQ q [] := by
  change 2 ^ (1 + 0) < q ^ (1 + 0)
  rw [Nat.add_zero, pow_one, pow_one]
  omega

/-- q^(Σ o) ≤ 2^(Σ p2Q(o)). -/
theorem q_pow_sum_le (hq : 3 ≤ q) (os : List ℕ) : q ^ os.sum ≤ 2 ^ (os.map (p2Q q)).sum := by
  induction os with
  | nil =>
    simp
  | cons o os ih =>
    rw [List.sum_cons, List.map_cons, List.sum_cons, pow_add, pow_add]
    exact Nat.mul_le_mul (p2Q_spec hq o).le ih

/-- A block lowers the level: `LevelUpQ` of a list gives `LevelUpQ` of a beginning. -/
theorem levelUpQ_of_append (hq : 3 ≤ q) (a b : List ℕ) (h : LevelUpQ q (a ++ b)) :
    LevelUpQ q a := by
  unfold LevelUpQ at h ⊢
  rw [List.map_append, List.sum_append, List.sum_append, ← add_assoc, ← add_assoc,
    pow_add 2 (1 + (a.map (p2Q q)).sum), pow_add q (1 + a.sum)] at h
  have hb := q_pow_sum_le hq b
  by_contra hcon
  have hge : q ^ (1 + a.sum) ≤ 2 ^ (1 + (a.map (p2Q q)).sum) := Nat.le_of_not_lt hcon
  exact absurd h (not_lt.mpr (Nat.mul_le_mul hge hb))

theorem levelUpQ_take (hq : 3 ≤ q) {os : List ℕ} (h : LevelUpQ q os) (i : ℕ) :
    LevelUpQ q (os.take i) := by
  apply levelUpQ_of_append hq (os.take i) (os.drop i)
  rw [List.take_append_drop]
  exact h

/-- Length of a concatenation of admissible blocks, from their Orders. -/
theorem length_flatten_admQ (hq : 3 ≤ q) (bs : List (List Bool))
    (hbs : ∀ b ∈ bs, AdmissibleQ q b) :
    bs.flatten.length = ((bs.map order).map (p2Q q)).sum := by
  induction bs with
  | nil =>
    simp
  | cons b t ih =>
    rw [List.flatten_cons, List.length_append, List.map_cons, List.map_cons, List.sum_cons,
      admissibleQ_length (by omega) (hbs b List.mem_cons_self),
      ih (fun c hc => hbs c (List.mem_cons_of_mem b hc))]

/-- The level after 1 :: blocks is above 1 iff `LevelUpQ` holds for their Orders. -/
theorem one_lt_levelQ_iff (hq : 3 ≤ q) (bs : List (List Bool))
    (hbs : ∀ b ∈ bs, AdmissibleQ q b) :
    1 < seqProductQ q (true :: bs.flatten) ↔ LevelUpQ q (bs.map order) := by
  rw [one_lt_seqProductQ_iff, order_cons_flatten, List.length_cons,
    length_flatten_admQ hq bs hbs, LevelUpQ, Nat.add_comm _ 1]

/-- For odd q the level after 1 :: blocks is below 1 iff `LevelUpQ` fails for their
    Orders. -/
theorem levelQ_lt_one_iff (hodd : Odd q) (hq : 3 ≤ q) (bs : List (List Bool))
    (hbs : ∀ b ∈ bs, AdmissibleQ q b) :
    seqProductQ q (true :: bs.flatten) < 1 ↔ ¬LevelUpQ q (bs.map order) := by
  rw [← one_lt_levelQ_iff hq bs hbs]
  have hne := seqProductQ_ne_one hodd hq (s := true :: bs.flatten) (List.cons_ne_nil _ _)
  constructor
  · intro h hgt
    linarith
  · intro h
    exact lt_of_le_of_ne (not_lt.mp h) hne

/-- Chain form: for admissible blocks, 1 :: (B1 ++ ... ++ Bm) is admissible iff the level
    is above 1 before the last block and below 1 after it; both depend on the Orders of
    the blocks only. -/
theorem admissibleQ_iff_chainQ (hodd : Odd q) (hq : 3 ≤ q) (bs : List (List Bool))
    (hbs : ∀ b ∈ bs, AdmissibleQ q b) :
    AdmissibleQ q (true :: bs.flatten) ↔
      LevelUpQ q (bs.map order).dropLast ∧ ¬LevelUpQ q (bs.map order) := by
  rw [admissibleQ_split_iff hq bs hbs, levelQ_lt_one_iff hodd hq bs hbs]
  have htake : ∀ i, ∀ b ∈ bs.take i, AdmissibleQ q b :=
    fun i b hb => hbs b (List.mem_of_mem_take hb)
  constructor
  · rintro ⟨hlev, hend⟩
    refine ⟨?_, hend⟩
    rcases Nat.lt_or_ge bs.length 2 with hlen | hlen
    · have hd : (bs.map order).dropLast = [] := by
        rw [← List.length_eq_zero_iff, List.length_dropLast, List.length_map]
        omega
      rw [hd]
      exact levelUpQ_nil hq
    · have h := hlev (bs.length - 1) (by omega) (by omega)
      rw [one_lt_levelQ_iff hq _ (htake _), List.map_take] at h
      rw [List.dropLast_eq_take, List.length_map]
      exact h
  · rintro ⟨hup, hend⟩
    refine ⟨?_, hend⟩
    intro i hi hil
    rw [one_lt_levelQ_iff hq _ (htake i), List.map_take]
    have h := levelUpQ_take hq hup i
    rw [List.dropLast_eq_take, List.take_take, List.length_map, min_eq_left (by omega)] at h
    exact h

/-- The chain decomposition of the q-family: the admissible words of Order ≥ 1 are
    exactly the words 1 :: (B1 ++ ... ++ Bm) with admissible blocks whose Orders keep the
    level above 1 before the last block and bring it below 1 after it. -/
theorem admissibleQ_iff_exists_chainQ (hodd : Odd q) (hq : 3 ≤ q) (s : List Bool) :
    (AdmissibleQ q s ∧ 1 ≤ order s) ↔
      ∃ bs, IsSplitQ q s bs ∧
        LevelUpQ q (bs.map order).dropLast ∧ ¬LevelUpQ q (bs.map order) := by
  constructor
  · rintro ⟨hA, hord⟩
    obtain ⟨bs, hbs⟩ := exists_splitQ hodd hq hA hord
    rw [hbs.eq] at hA
    exact ⟨bs, hbs, (admissibleQ_iff_chainQ hodd hq bs hbs.adm).mp hA⟩
  · rintro ⟨bs, hbs, hchain⟩
    refine ⟨?_, ?_⟩
    · rw [hbs.eq]
      exact (admissibleQ_iff_chainQ hodd hq bs hbs.adm).mpr hchain
    · rw [order_splitQ hbs]
      omega

end AcceleratedCollatz
