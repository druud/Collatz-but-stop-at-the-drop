-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TBridge

/-!
  Order preservation (paper sec:fast): the positive entries of a vector sum to the
  order of its decoded word (`order_decodeVector`); for a start x0 > 1 that drops,
  the positive entries of its marked vector sum to the Order of its parity word up
  to the drop (`order_preservation`).
-/

namespace AcceleratedCollatz

/-- The order of a decoded vector is the sum of its positive entries. -/
theorem order_decodeVector (v : List ℤ) :
    (order (decodeVector v) : ℤ) = (v.filter (· > 0)).sum := by
  induction v with
  | nil => simp [decodeVector, order]
  | cons e rest ih =>
    rw [order_decodeVector_cons]
    by_cases he : e > 0
    · rw [order_expandEntry_pos e he, List.filter_cons_of_pos (by simpa using he), List.sum_cons]
      push_cast
      rw [ih, Int.toNat_of_nonneg (le_of_lt he)]
    · rw [order_expandEntry_nonpos e he, List.filter_cons_of_neg (by simpa using he)]
      simpa using ih

/-- Order preservation: for x0 > 1 that drops within the fuel, the positive entries of
    its marked vector sum to the Order of its parity word up to the drop. -/
theorem order_preservation (x0 fuel : ℕ) (hx0 : x0 > 1)
    (hterm : (trajStats x0 fuel x0).2.2 < x0) :
    (((markedVector fuel x0 x0).filter (· > 0)).sum : ℤ) =
      order (tBits x0 (decodeVector (markedVector fuel x0 x0)).length) := by
  rw [(decodeVector_eq_tBits x0 fuel hx0 hterm).1, order_decodeVector]

end AcceleratedCollatz
