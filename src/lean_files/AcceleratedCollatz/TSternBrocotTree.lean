-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TSternBrocotQ
import AcceleratedCollatz.TWordPoint

/-!
  The point of a word is the Stern-Brocot point of its node (K. Ryde, Trees of Rationals:
  the tree by mediants, or by the matrices whose columns are the two fractions of a node).
  A word read from its first letter is a path of moves from the root 0/1, 1/0: a 1 moves
  to the right (the mediant replaces the fraction below), a 0 to the left (it replaces the
  fraction above) (`sbMove`, `sbNode`). The two fractions stay neighbours (`sbNode_det`);
  the point of the node is their mediant (`sbMed`), and it is the point of the word
  (`sbPoint_eq_sbMed`), in lowest terms (`sbNode_coprime`, `sbPoint_num`, `sbPoint_den`).
  A step of the walk towards log2 q is such a move (`sbStepQ_eq_sbMove`).
-/

namespace AcceleratedCollatz

/-- One move down the Stern-Brocot tree: the mediant replaces the fraction below for a 1
    (to the right), the fraction above for a 0 (to the left). -/
def sbMove (b : Bool) (s : SBNode) : SBNode :=
  if b then ⟨s.loNum + s.hiNum, s.loDen + s.hiDen, s.hiNum, s.hiDen⟩
  else ⟨s.loNum, s.loDen, s.loNum + s.hiNum, s.loDen + s.hiDen⟩

/-- The node reached from s by the moves of a word, its first letter first. -/
def sbNodeFrom (s : SBNode) : List Bool → SBNode
  | [] => s
  | b :: w => sbNodeFrom (sbMove b s) w

/-- The node of a word: its moves from the root. -/
def sbNode (w : List Bool) : SBNode := sbNodeFrom sbRoot w

/-- The mediant of the two fractions of a node: its point. -/
def sbMed (s : SBNode) : ℚ := ((s.loNum + s.hiNum : ℕ) : ℚ) / ((s.loDen + s.hiDen : ℕ) : ℚ)

/-- Every fraction p/n of a node mapped to (p + n)/n. -/
def sbShift (s : SBNode) : SBNode :=
  ⟨s.loNum + s.loDen, s.loDen, s.hiNum + s.hiDen, s.hiDen⟩

/-- Every fraction p/n of a node mapped to p/(p + n). -/
def sbSquash (s : SBNode) : SBNode :=
  ⟨s.loNum, s.loNum + s.loDen, s.hiNum, s.hiNum + s.hiDen⟩

theorem sbNodeFrom_nil (s : SBNode) : sbNodeFrom s [] = s := rfl

theorem sbNodeFrom_cons (s : SBNode) (b : Bool) (w : List Bool) :
    sbNodeFrom s (b :: w) = sbNodeFrom (sbMove b s) w := rfl

theorem sbMove_sbShift (b : Bool) (s : SBNode) : sbMove b (sbShift s) = sbShift (sbMove b s) := by
  cases b
  · simp only [sbMove, sbShift, Bool.false_eq_true, ↓reduceIte]
    ac_rfl
  · simp only [sbMove, sbShift, ↓reduceIte]
    ac_rfl

theorem sbMove_sbSquash (b : Bool) (s : SBNode) :
    sbMove b (sbSquash s) = sbSquash (sbMove b s) := by
  cases b
  · simp only [sbMove, sbSquash, Bool.false_eq_true, ↓reduceIte]
    ac_rfl
  · simp only [sbMove, sbSquash, ↓reduceIte]
    ac_rfl

theorem sbNodeFrom_sbShift (s : SBNode) (w : List Bool) :
    sbNodeFrom (sbShift s) w = sbShift (sbNodeFrom s w) := by
  induction w generalizing s with
  | nil =>
    rfl
  | cons b w ih =>
    rw [sbNodeFrom_cons, sbNodeFrom_cons, sbMove_sbShift, ih]

theorem sbNodeFrom_sbSquash (s : SBNode) (w : List Bool) :
    sbNodeFrom (sbSquash s) w = sbSquash (sbNodeFrom s w) := by
  induction w generalizing s with
  | nil =>
    rfl
  | cons b w ih =>
    rw [sbNodeFrom_cons, sbNodeFrom_cons, sbMove_sbSquash, ih]

/-- A word that starts with a 1: the node of the rest, shifted. -/
theorem sbNode_true_cons (w : List Bool) : sbNode (true :: w) = sbShift (sbNode w) := by
  have h : sbMove true sbRoot = sbShift sbRoot := rfl
  rw [sbNode, sbNodeFrom_cons, h, sbNodeFrom_sbShift]
  rfl

/-- A word that starts with a 0: the node of the rest, squashed. -/
theorem sbNode_false_cons (w : List Bool) : sbNode (false :: w) = sbSquash (sbNode w) := by
  have h : sbMove false sbRoot = sbSquash sbRoot := rfl
  rw [sbNode, sbNodeFrom_cons, h, sbNodeFrom_sbSquash]
  rfl

/-- The denominators of a node sum to at least 1. -/
theorem one_le_sbNode_den (w : List Bool) : 1 ≤ (sbNode w).loDen + (sbNode w).hiDen := by
  induction w with
  | nil =>
    change 1 ≤ 1 + 0
    omega
  | cons b w ih =>
    cases b
    · rw [sbNode_false_cons]
      change 1 ≤ (sbNode w).loNum + (sbNode w).loDen + ((sbNode w).hiNum + (sbNode w).hiDen)
      omega
    · rw [sbNode_true_cons]
      exact ih

/-- The two fractions of a node are neighbours. -/
theorem sbNode_det (w : List Bool) :
    (sbNode w).hiNum * (sbNode w).loDen = (sbNode w).loNum * (sbNode w).hiDen + 1 := by
  induction w with
  | nil =>
    rfl
  | cons b w ih =>
    cases b
    · rw [sbNode_false_cons]
      change (sbNode w).hiNum * ((sbNode w).loNum + (sbNode w).loDen) =
        (sbNode w).loNum * ((sbNode w).hiNum + (sbNode w).hiDen) + 1
      rw [Nat.mul_add, Nat.mul_add, Nat.mul_comm (sbNode w).hiNum (sbNode w).loNum]
      omega
    · rw [sbNode_true_cons]
      change ((sbNode w).hiNum + (sbNode w).hiDen) * (sbNode w).loDen =
        ((sbNode w).loNum + (sbNode w).loDen) * (sbNode w).hiDen + 1
      rw [Nat.add_mul, Nat.add_mul, Nat.mul_comm (sbNode w).hiDen (sbNode w).loDen]
      omega

/-- The mediant of a node and the fraction above it are neighbours. -/
theorem sbNode_med_det (w : List Bool) :
    (sbNode w).hiNum * ((sbNode w).loDen + (sbNode w).hiDen) =
      ((sbNode w).loNum + (sbNode w).hiNum) * (sbNode w).hiDen + 1 := by
  have h := sbNode_det w
  rw [Nat.mul_add, Nat.add_mul, Nat.mul_comm (sbNode w).hiNum (sbNode w).hiDen]
  omega

/-- The mediant of a node is in lowest terms. -/
theorem sbNode_coprime (w : List Bool) :
    Nat.Coprime ((sbNode w).loNum + (sbNode w).hiNum) ((sbNode w).loDen + (sbNode w).hiDen) := by
  have h := sbNode_med_det w
  have h1 : Nat.gcd ((sbNode w).loNum + (sbNode w).hiNum) ((sbNode w).loDen + (sbNode w).hiDen)
      ∣ (sbNode w).hiNum * ((sbNode w).loDen + (sbNode w).hiDen) :=
    Dvd.dvd.mul_left (Nat.gcd_dvd_right _ _) _
  have h2 : Nat.gcd ((sbNode w).loNum + (sbNode w).hiNum) ((sbNode w).loDen + (sbNode w).hiDen)
      ∣ ((sbNode w).loNum + (sbNode w).hiNum) * (sbNode w).hiDen :=
    Dvd.dvd.mul_right (Nat.gcd_dvd_left _ _) _
  rw [h] at h1
  exact Nat.dvd_one.mp ((Nat.dvd_add_right h2).mp h1)

theorem sbMed_sbShift (s : SBNode) (h : 1 ≤ s.loDen + s.hiDen) :
    sbMed (sbShift s) = sbMed s + 1 := by
  have hd : ((s.loDen + s.hiDen : ℕ) : ℚ) ≠ 0 := by
    have : (1 : ℚ) ≤ ((s.loDen + s.hiDen : ℕ) : ℚ) := by exact_mod_cast h
    linarith
  simp only [sbMed, sbShift]
  rw [div_add_one hd]
  congr 1
  push_cast
  ring

theorem sbMed_sbSquash (s : SBNode) (h : 1 ≤ s.loDen + s.hiDen) :
    sbMed (sbSquash s) = sbMed s / (sbMed s + 1) := by
  have hd : ((s.loDen + s.hiDen : ℕ) : ℚ) ≠ 0 := by
    have : (1 : ℚ) ≤ ((s.loDen + s.hiDen : ℕ) : ℚ) := by exact_mod_cast h
    linarith
  simp only [sbMed, sbSquash]
  rw [div_add_one hd, div_div_div_cancel_right₀ hd]
  congr 1
  push_cast
  ring

/-- The point of a word is the mediant of its node. -/
theorem sbPoint_eq_sbMed (w : List Bool) : sbPoint w = sbMed (sbNode w) := by
  induction w with
  | nil =>
    rw [sbPoint_nil]
    simp only [sbNode, sbNodeFrom, sbMed, sbRoot]
    norm_num
  | cons b w ih =>
    cases b
    · rw [sbPoint_false_cons, sbNode_false_cons, sbMed_sbSquash _ (one_le_sbNode_den w), ih]
    · rw [sbPoint_true_cons, sbNode_true_cons, sbMed_sbShift _ (one_le_sbNode_den w), ih]

/-- The numerator of the point of a word in lowest terms. -/
theorem sbPoint_num (w : List Bool) :
    (sbPoint w).num = ((sbNode w).loNum + (sbNode w).hiNum : ℕ) := by
  have hc := sbNode_coprime w
  have hd := one_le_sbNode_den w
  rw [sbPoint_eq_sbMed, sbMed]
  have e : ((((sbNode w).loNum + (sbNode w).hiNum : ℕ) : ℚ) /
      (((sbNode w).loDen + (sbNode w).hiDen : ℕ) : ℚ)) =
      ((((sbNode w).loNum + (sbNode w).hiNum : ℕ) : ℤ) : ℚ) /
      ((((sbNode w).loDen + (sbNode w).hiDen : ℕ) : ℤ) : ℚ) := by
    rw [Int.cast_natCast, Int.cast_natCast]
  rw [e]
  exact Rat.num_div_eq_of_coprime (by exact_mod_cast hd) hc

/-- The denominator of the point of a word in lowest terms. -/
theorem sbPoint_den (w : List Bool) :
    ((sbPoint w).den : ℤ) = ((sbNode w).loDen + (sbNode w).hiDen : ℕ) := by
  have hc := sbNode_coprime w
  have hd := one_le_sbNode_den w
  rw [sbPoint_eq_sbMed, sbMed]
  have e : ((((sbNode w).loNum + (sbNode w).hiNum : ℕ) : ℚ) /
      (((sbNode w).loDen + (sbNode w).hiDen : ℕ) : ℚ)) =
      ((((sbNode w).loNum + (sbNode w).hiNum : ℕ) : ℤ) : ℚ) /
      ((((sbNode w).loDen + (sbNode w).hiDen : ℕ) : ℤ) : ℚ) := by
    rw [Int.cast_natCast, Int.cast_natCast]
  rw [e]
  exact Rat.den_div_eq_of_coprime (by exact_mod_cast hd) hc

/-- A step of the walk towards log2 q is a move: to the left when the mediant lies above
    log2 q, else to the right. -/
theorem sbStepQ_eq_sbMove (q : ℕ) (s : SBNode) :
    sbStepQ q s = sbMove (!decide (q ^ (s.loDen + s.hiDen) < 2 ^ (s.loNum + s.hiNum))) s := by
  by_cases h : q ^ (s.loDen + s.hiDen) < 2 ^ (s.loNum + s.hiNum)
  · rw [sbStepQ_of_lt h]
    simp only [sbMove, h, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  · rw [sbStepQ_of_not_lt h]
    simp only [sbMove, h, decide_false, Bool.not_false, ↓reduceIte]

set_option linter.hashCommand false in
#guard sbNode [true, false, true, true] = ⟨5, 3, 2, 1⟩

end AcceleratedCollatz
