-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.Zeta.TCycleZeroQ
import AcceleratedCollatz.TGridOrder
import AcceleratedCollatz.TAdmSet

/-!
  The zeros of OEIS A400061 (C191): for q = 3, `p2Q_mul_card_eq_choose_iff` in the terms of
  A400061 and A100982. With L = p2(n), A400061(n) = C(L, n) - L N(n) is 0 exactly at the upper
  record Orders 1, 3, 5, 17, 29, 41, 94, ... (`UpperRecord`: p2(n)/n below p2(a)/a for every
  1 ≤ a < n, that is the floor 3^n/2^p2(n) above all earlier floors).
-/

namespace AcceleratedCollatz

/-- C191: p2(n) · N(n) = C(p2(n), n) iff n is an upper record Order. -/
theorem p2_mul_card_admSet_eq_choose_iff (n : ℕ) :
    p2_of n * (admSet n).card = (p2_of n).choose n ↔ UpperRecord n := by
  rw [← admSetQ_three]
  exact p2Q_mul_card_eq_choose_iff (q := 3) (by decide) le_rfl n

end AcceleratedCollatz
