-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TFiniteCheck

/-!
# The next finite check: up to Order 64497106

The record data for the next range check, computed by the kernel: five more steps of the
Stern–Brocot walk towards log2 3 from `sbWalk_102` (`sbWalk_107`), so 10781274 is an upper
record Order with p2(10781274) = 17087915, no upper record Order lies in
(10781274, 64497107), and widthBound 10781274 = 294401822513350. With them, a range check
of every x with 1 < x ≤ 294401822513350 gives `ClassDropsAt m` for every Order
m ≤ 64497106 (`classDropsAt_le_64497106`); the range check is the only hypothesis.

Each step is one comparison of q^n with 2^p; the largest, at step 107, compares numbers of
about 8.5·10^7 bits. Like `TFiniteCheck` this module needs `LEAN_NAT_MAX_SIZE` (see
`natMaxSizeNeededNext`).
-/

namespace AcceleratedCollatz

/-- The least value of `LEAN_NAT_MAX_SIZE` this module is known to build with. -/
def natMaxSizeNeededNext : ℕ := 1000000000

set_option linter.unusedTactic false in
/-- The Stern–Brocot walk towards log2 3 after 107 steps. -/
theorem sbWalk_107 : sbWalk 107 = ⟨85137581, 53715833, 17087915, 10781274⟩ := by
  run_tac do
    let v ← IO.getEnv "LEAN_NAT_MAX_SIZE"
    unless ((v.bind String.toNat?).getD 0) ≥ natMaxSizeNeededNext do
      throwError "set LEAN_NAT_MAX_SIZE to at least {natMaxSizeNeededNext}, \
        e.g. LEAN_NAT_MAX_SIZE=2000000000 lake build (found {v})"
  have h3 : sbWalk 103 = ⟨16785921, 10590737, 17087915, 10781274⟩ := by
    change sbWalkQ 3 (102 + 1) = _
    rw [sbWalkQ_succ]
    change sbStepQ 3 (sbWalk 102) = _
    rw [sbWalk_102, sbStepQ_of_lt (by decide +kernel)]
    rfl
  have h4 : sbWalk 104 = ⟨33873836, 21372011, 17087915, 10781274⟩ := by
    change sbWalkQ 3 (103 + 1) = _
    rw [sbWalkQ_succ]
    change sbStepQ 3 (sbWalk 103) = _
    rw [h3, sbStepQ_of_not_lt (by decide +kernel)]
    rfl
  have h5 : sbWalk 105 = ⟨50961751, 32153285, 17087915, 10781274⟩ := by
    change sbWalkQ 3 (104 + 1) = _
    rw [sbWalkQ_succ]
    change sbStepQ 3 (sbWalk 104) = _
    rw [h4, sbStepQ_of_not_lt (by decide +kernel)]
    rfl
  have h6 : sbWalk 106 = ⟨68049666, 42934559, 17087915, 10781274⟩ := by
    change sbWalkQ 3 (105 + 1) = _
    rw [sbWalkQ_succ]
    change sbStepQ 3 (sbWalk 105) = _
    rw [h5, sbStepQ_of_not_lt (by decide +kernel)]
    rfl
  change sbWalkQ 3 (106 + 1) = _
  rw [sbWalkQ_succ]
  change sbStepQ 3 (sbWalk 106) = _
  rw [h6, sbStepQ_of_not_lt (by decide +kernel)]
  rfl

/-- The record invariant of the walk at step 107. -/
theorem sbRecords_107 : SBRecordsQ 3 (sbWalk 107) := by
  have h := sbWalkQ_records (q := 3) (by decide) le_rfl 105
  have h2 : p2Q 3 1 + 105 = 107 := by
    have : p2Q 3 1 = 2 := p2_of_one
    omega
  rw [h2] at h
  exact h

set_option exponentiation.threshold 20000000 in
/-- p2(10781274) = 17087915. -/
theorem p2_of_10781274 : p2_of 10781274 = 17087915 := by
  have h := sbRecords_107.hi
  rw [sbWalk_107] at h
  exact h.symm

set_option exponentiation.threshold 20000000 in
/-- 10781274 is an upper record Order. -/
theorem upperRecord_10781274 : UpperRecord 10781274 := by
  have h := sbRecords_107.last.upper
  rw [sbWalk_107] at h
  exact h

/-- No upper record Order lies strictly between 10781274 and 64497107. -/
theorem not_upperRecord_10781274_64497107 :
    ∀ k, 10781274 < k → k ≤ 64497106 → ¬UpperRecord k := by
  intro k hk1 hk2
  have h := sbRecords_107.last.no_upper
  rw [sbWalk_107] at h
  have hk : k < 53715833 + 10781274 := by omega
  exact h k hk1 hk

/-- widthBound 10781274 = 294401822513350. -/
theorem widthBound_10781274 : widthBound 10781274 = 294401822513350 := by
  unfold widthBound
  rw [p2_of_10781274]
  decide +kernel

/-- ClassDrops at every Order up to 64497106, from the range check up to
    294401822513350 (the only hypothesis). -/
theorem classDropsAt_le_64497106
    (hX : ∀ x, 1 < x → x ≤ 294401822513350 → ∀ m, Admissible (tBits x m) → tStep^[m] x < x) :
    ∀ m, m ≤ 64497106 → ClassDropsAt m := fun _ hm =>
  classDropsAt_of_verified_record 294401822513350 hX (a := 10781274) (n := 64497106)
    (by norm_num) upperRecord_10781274 not_upperRecord_10781274_64497107
    (le_of_eq widthBound_10781274) hm

end AcceleratedCollatz
