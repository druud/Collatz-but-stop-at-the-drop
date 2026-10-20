-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TBlockRecord
import AcceleratedCollatz.TSternBrocotQ

/-!
  The record Orders on the Stern–Brocot walk towards log2 3 (paper sec:chain): the q = 3
  case of TSternBrocotQ. `sbWalk k` holds the last fraction below log2 3 and the last one
  above it after k steps from 0/1 and 1/0. The upper record Orders n ≥ 1 are exactly the
  denominators of the fractions above log2 3 (`upperRecord_iff_sbWalk`), with numerator
  p2(n) (`sbWalk_hiNum`); the lower record Orders n ≥ 1 are exactly the denominators of
  the fractions below it (`lowerRecord_iff_sbWalk`), with numerator p2(n) - 1
  from step 2 on (`sbWalk_loNum`).
-/

namespace AcceleratedCollatz

/-- The Stern–Brocot walk towards log2 3 after k steps. -/
def sbWalk (k : ℕ) : SBNode := sbWalkQ 3 k

/-- The upper record Orders n ≥ 1 are exactly the denominators of the fractions above
    log2 3 on the Stern–Brocot walk towards it. -/
theorem upperRecord_iff_sbWalk {n : ℕ} (hn : 1 ≤ n) :
    UpperRecord n ↔ ∃ k, (sbWalk k).hiDen = n :=
  upperRecordQ_iff_sbWalkQ (by decide) le_rfl hn

/-- The lower record Orders n ≥ 1 are exactly the denominators of the fractions below
    log2 3 on the Stern–Brocot walk towards it. -/
theorem lowerRecord_iff_sbWalk {n : ℕ} (hn : 1 ≤ n) :
    LowerRecord n ↔ ∃ k, (sbWalk k).loDen = n :=
  lowerRecordQ_iff_sbWalkQ (by decide) le_rfl hn

/-- From step 2 on the fraction above is p2(b)/b. -/
theorem sbWalk_hiNum {k : ℕ} (hk : 2 ≤ k) : (sbWalk k).hiNum = p2_of (sbWalk k).hiDen := by
  have h : p2Q 3 1 = 2 := p2_of_one
  exact sbWalkQ_hiNum (by decide) le_rfl (by omega)

/-- From step 2 on the fraction below is (p2(a) - 1)/a. -/
theorem sbWalk_loNum {k : ℕ} (hk : 2 ≤ k) :
    (sbWalk k).loNum + 1 = p2_of (sbWalk k).loDen := by
  have h : p2Q 3 1 = 2 := p2_of_one
  exact sbWalkQ_loNum (by decide) le_rfl (by omega)

set_option linter.hashCommand false in
#guard (List.range 12).map (fun k => (sbWalk k).hiDen) = [0, 0, 1, 1, 3, 5, 5, 5, 17, 29, 41, 41]

set_option linter.hashCommand false in
#guard (List.range 12).map (fun k => (sbWalk k).loDen) = [1, 1, 1, 2, 2, 2, 7, 12, 12, 12, 12, 53]

set_option linter.hashCommand false in
#guard sbWalk 11 = ⟨84, 53, 65, 41⟩

end AcceleratedCollatz
