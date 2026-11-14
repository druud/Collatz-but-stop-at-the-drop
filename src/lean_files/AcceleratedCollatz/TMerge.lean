-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TParity

/-!
  Merging paths (Questions B66). Two different values with the same image under T are an odd
  o and 3o + 1 (`tStep_eq_tStep_iff`): a merge of two paths is such a pair one step before.
  For x = 32a + 5 the paths of x and x + 1 merge at step 5, in 9a + 2, and x drops at
  step 2 (`merge_thirtytwo_add_five`): 3 steps between the drop and the merge. Measured
  (`_tmp/bits_01/merge2.py`): for every odd x < 2^21 whose path merges with that of x + 1
  before 1, the merge comes at least 3 steps after the drop of x; not proved here.
-/

namespace AcceleratedCollatz

theorem tStep_eq_tStep_iff (v w : ℕ) (hvw : v ≠ w) :
    tStep v = tStep w ↔ (v % 2 = 1 ∧ w = 3 * v + 1) ∨ (w % 2 = 1 ∧ v = 3 * w + 1) := by
  unfold tStep
  constructor
  · intro h
    split at h <;> split at h <;> omega
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> subst_vars <;> split_ifs <;> omega

/-- x = 32a + 5: x -> 48a + 8 -> 24a + 4 -> 12a + 2 -> 6a + 1 -> 9a + 2 and
    x + 1 -> 16a + 3 -> 24a + 5 -> 36a + 8 -> 18a + 4 -> 9a + 2; the drop at step 2, the
    paths apart before step 5. -/
theorem merge_thirtytwo_add_five (a : ℕ) :
    tStep^[5] (32 * a + 5) = tStep^[5] (32 * a + 6) ∧
      (∀ j < 5, tStep^[j] (32 * a + 5) ≠ tStep^[j] (32 * a + 6)) ∧
      32 * a + 5 ≤ tStep (32 * a + 5) ∧ tStep^[2] (32 * a + 5) < 32 * a + 5 := by
  have s1 : tStep (32 * a + 5) = 48 * a + 8 := by unfold tStep; split <;> omega
  have s2 : tStep (48 * a + 8) = 24 * a + 4 := by unfold tStep; split <;> omega
  have s3 : tStep (24 * a + 4) = 12 * a + 2 := by unfold tStep; split <;> omega
  have s4 : tStep (12 * a + 2) = 6 * a + 1 := by unfold tStep; split <;> omega
  have s5 : tStep (6 * a + 1) = 9 * a + 2 := by unfold tStep; split <;> omega
  have t1 : tStep (32 * a + 6) = 16 * a + 3 := by unfold tStep; split <;> omega
  have t2 : tStep (16 * a + 3) = 24 * a + 5 := by unfold tStep; split <;> omega
  have t3 : tStep (24 * a + 5) = 36 * a + 8 := by unfold tStep; split <;> omega
  have t4 : tStep (36 * a + 8) = 18 * a + 4 := by unfold tStep; split <;> omega
  have t5 : tStep (18 * a + 4) = 9 * a + 2 := by unfold tStep; split <;> omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
    rw [s1, s2, s3, s4, s5, t1, t2, t3, t4, t5]
  · intro j hj
    interval_cases j <;>
      simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, s1, s2, s3, s4,
        t1, t2, t3, t4] <;> omega
  · rw [s1]; omega
  · simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
    rw [s1, s2]; omega

end AcceleratedCollatz
