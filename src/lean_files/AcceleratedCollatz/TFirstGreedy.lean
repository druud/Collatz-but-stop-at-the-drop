-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TFirstGreedyQ
import AcceleratedCollatz.TFirstWord

/-!
  The first word of Order n as a greedy sum, q = 3 (the q = 3 case of TFirstGreedyQ): with
  a1 the largest lower record Order ≤ n, a2 the largest one ≤ n - a1, and so on, the first
  word of Order n is the first parts of the first words of a1, a2, ..., in turn, then a
  halving (`firstWord_eq_greedy`). The first word of Order 6 is three times the first part
  of the first word of Order 2, then a halving.
-/

namespace AcceleratedCollatz

/-- The first word of Order n is the first parts of the first words of its greedy sum of
    lower record Orders, in turn, then a halving. -/
theorem firstWord_eq_greedy {n : ℕ} {as : List ℕ} (h : IsGreedyLowQ 3 n as) :
    firstWord n = (as.map firstBody).flatten ++ [false] := by
  rw [← firstWordQ_three, ← firstBodyQ_three]
  exact firstWordQ_eq_greedy le_rfl h

set_option linter.hashCommand false in
#guard firstWord 6 = firstBody 2 ++ firstBody 2 ++ firstBody 2 ++ [false]

set_option linter.hashCommand false in
#guard firstWord 30 = firstBody 12 ++ firstBody 12 ++ firstBody 2 ++ firstBody 2 ++
  firstBody 2 ++ [false]

end AcceleratedCollatz
