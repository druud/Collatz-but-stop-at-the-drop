-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TSternBrocot
import AcceleratedCollatz.TWidthRecord

/-!
# The finite check of the width identity up to Order 10781273

The record data behind the finite check, computed by the kernel: the Stern–Brocot walk
towards log2 3 at step 102 (`sbWalk_102`), so 190537 is an upper record Order with
p2(190537) = 301994, no upper record Order lies in (190537, 10781274), and
widthBound 190537 = 984572779224. With them, a range check of every x with
1 < x ≤ 984572779224 gives `ClassDropsAt m` for every Order m ≤ 10781273
(`classDropsAt_le_10781273`); the range check is the only hypothesis.

The kernel compares numbers of about 1.7·10^7 bits here: building this module needs the
environment variable `LEAN_NAT_MAX_SIZE` of at least 300000000; `lake build` sets it through
the target `natMaxSize` of `lakefile.lean`, `lake env lean` and the editor need it set
outside. The proof of `sbWalk_102` checks it first.
After a reviewer's file sent by M. Winkler (Oct 2026).
-/

namespace AcceleratedCollatz

/-- The least value of `LEAN_NAT_MAX_SIZE` this module is known to build with. -/
def natMaxSizeNeeded : ℕ := 300000000

set_option linter.unusedTactic false in
/-- The Stern–Brocot walk towards log2 3 after 102 steps. -/
theorem sbWalk_102 : sbWalk 102 = ⟨16785921, 10590737, 301994, 190537⟩ := by
  run_tac do
    let v ← IO.getEnv "LEAN_NAT_MAX_SIZE"
    unless ((v.bind String.toNat?).getD 0) ≥ natMaxSizeNeeded do
      throwError "set LEAN_NAT_MAX_SIZE to at least {natMaxSizeNeeded}, \
        e.g. LEAN_NAT_MAX_SIZE=1000000000 lake build (found {v})"
  decide +kernel

/-- The record invariant of the walk at step 102. -/
theorem sbRecords_102 : SBRecordsQ 3 (sbWalk 102) := by
  have h := sbWalkQ_records (q := 3) (by decide) le_rfl 100
  have h2 : p2Q 3 1 + 100 = 102 := by
    have : p2Q 3 1 = 2 := p2_of_one
    omega
  rw [h2] at h
  exact h

set_option exponentiation.threshold 400000 in
/-- p2(190537) = 301994. -/
theorem p2_of_190537 : p2_of 190537 = 301994 := by
  have h := sbRecords_102.hi
  rw [sbWalk_102] at h
  exact h.symm

set_option exponentiation.threshold 400000 in
/-- 190537 is an upper record Order. -/
theorem upperRecord_190537 : UpperRecord 190537 := by
  have h := sbRecords_102.last.upper
  rw [sbWalk_102] at h
  exact h

/-- No upper record Order lies strictly between 190537 and 10781274. -/
theorem not_upperRecord_190537_10781274 :
    ∀ k, 190537 < k → k ≤ 10781273 → ¬UpperRecord k := by
  intro k hk1 hk2
  have h := sbRecords_102.last.no_upper
  rw [sbWalk_102] at h
  have hk : k < 10590737 + 190537 := by omega
  exact h k hk1 hk

/-- widthBound 190537 = 984572779224. -/
theorem widthBound_190537 : widthBound 190537 = 984572779224 := by
  unfold widthBound
  rw [p2_of_190537]
  decide +kernel

/-- ClassDrops at every Order up to 10781273, from the range check up to
    984572779224 (the only hypothesis). -/
theorem classDropsAt_le_10781273
    (hX : ∀ x, 1 < x → x ≤ 984572779224 → ∀ m, Admissible (tBits x m) → tStep^[m] x < x) :
    ∀ m, m ≤ 10781273 → ClassDropsAt m := fun _ hm =>
  classDropsAt_of_verified_record 984572779224 hX (a := 190537) (n := 10781273)
    (by norm_num) upperRecord_190537 not_upperRecord_190537_10781274
    (le_of_eq widthBound_190537) hm

end AcceleratedCollatz
