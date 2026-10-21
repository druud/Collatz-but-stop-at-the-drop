-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TRhoBound
import AcceleratedCollatz.TSieve

/-!
  The congruence bound of a split (generation 68). For a word w = u ++ v with class id c,
  T^|u|(c) has the parity bits v, so 2^|u| classId v - rho u ≤ 3^(order u) c. That bound
  lies above the cycle point rho w / D w (D s = 2^|s| - 3^(order s), in ℤ) iff c lies
  above the cycle point of the rotation v ++ u (`split_bound_iff`, from the identity
  `split_identity`). For w = true :: v with 3c + 1 ≤ 2^|w| the class id of v is T(c)
  (`classId_tail_eq_tStep`), so the bound of the split after the leading 1 is the drop at
  c itself (`split_one_iff`): the congruence data restate ClassDrops.
-/

namespace AcceleratedCollatz

/-- 2^|s| - 3^(order s) in ℤ. -/
def dInt (s : List Bool) : ℤ := 2 ^ s.length - 3 ^ order s

/-- affineNum from position k + j on 2^j N is 2^j times affineNum from k on N. -/
theorem affineNum_shift (t : List Bool) (k j N : ℕ) :
    affineNum t (k + j) (2 ^ j * N) = 2 ^ j * affineNum t k N := by
  induction t generalizing k N with
  | nil =>
    simp [affineNum]
  | cons b t ih =>
    cases b with
    | true =>
      simp only [affineNum, ↓reduceIte]
      have h : 3 * (2 ^ j * N) + 2 ^ (k + j) = 2 ^ j * (3 * N + 2 ^ k) := by
        rw [pow_add]
        ring
      rw [h, show k + j + 1 = k + 1 + j by omega, ih]
    | false =>
      simp only [affineNum, Bool.false_eq_true, ↓reduceIte]
      rw [show k + j + 1 = k + 1 + j by omega, ih]

/-- rho of a concatenation. -/
theorem rho_append (a b : List Bool) :
    rho (a ++ b) = 3 ^ order b * rho a + 2 ^ a.length * rho b := by
  have h := affineNum_shift b 0 a.length 0
  simp only [zero_add, mul_zero] at h
  unfold rho
  rw [affineNum_append, zero_add, affineNum_linear, h]

/-- The split identity: the bound of the split u | v against the cycle point of u ++ v is
    2^|u| times the drop inequality at c of the rotation v ++ u. -/
theorem split_identity (u v : List Bool) (c : ℤ) :
    (2 ^ u.length * c - rho u) * dInt (u ++ v) - 3 ^ order u * rho (u ++ v)
      = 2 ^ u.length * (c * dInt (v ++ u) - rho (v ++ u)) := by
  unfold dInt
  rw [rho_append, rho_append, order_append, order_append, List.length_append,
    List.length_append]
  push_cast
  ring

/-- The bound of the split u | v lies above the cycle point of u ++ v iff c lies above the
    cycle point of v ++ u. -/
theorem split_bound_iff (u v : List Bool) (c : ℤ) :
    3 ^ order u * (rho (u ++ v) : ℤ) < (2 ^ u.length * c - rho u) * dInt (u ++ v)
      ↔ (rho (v ++ u) : ℤ) < c * dInt (v ++ u) := by
  have hp : (0 : ℤ) < 2 ^ u.length := by positivity
  rw [← sub_pos, split_identity, mul_pos_iff_of_pos_left hp, sub_pos]

/-- For w = true :: v with 3 classId w + 1 ≤ 2^|w|, the class id of v is T(classId w). -/
theorem classId_tail_eq_tStep (v : List Bool)
    (h : 3 * classId (true :: v) + 1 ≤ 2 ^ (true :: v).length) :
    classId v = tStep (classId (true :: v)) := by
  have hb := tBits_classId (true :: v)
  simp only [List.length_cons, tBits, List.cons.injEq, decide_eq_true_eq] at hb h
  obtain ⟨hodd, hv⟩ := hb
  rw [tStep_odd _ hodd] at hv ⊢
  have hle : (3 * classId (true :: v) + 1) / 2 ≤ 2 ^ v.length := by
    rw [pow_succ] at h
    omega
  exact (classId_unique v _ (by omega) hle hv).symm

/-- The split after the leading 1: for 3c + 1 ≤ 2^|w| its bound lies above the cycle point
    of w iff c does, the drop at c. -/
theorem split_one_iff (v : List Bool)
    (h : 3 * classId (true :: v) + 1 ≤ 2 ^ (true :: v).length) :
    3 * (rho (true :: v) : ℤ) < (2 * classId v - 1) * dInt (true :: v)
      ↔ (rho (true :: v) : ℤ) < classId (true :: v) * dInt (true :: v) := by
  have hc := classId_tail_eq_tStep v h
  have hodd : classId (true :: v) % 2 = 1 := by
    have hb := tBits_classId (true :: v)
    simp only [List.length_cons, tBits, List.cons.injEq, decide_eq_true_eq] at hb
    exact hb.1
  rw [tStep_odd _ hodd] at hc
  have h2 : (2 * classId v - 1 : ℤ) = 3 * classId (true :: v) := by
    have : 2 * classId v = 3 * classId (true :: v) + 1 := by omega
    omega
  rw [h2, mul_assoc]
  constructor
  · intro h3
    linarith
  · intro h3
    linarith

end AcceleratedCollatz
