-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TRhoMaxRecord

/-!
  The finite check with the largest rho as the bound, at the record Orders: with a the
  last upper record Order up to n, `widthBoundMax` of every Order up to n is at most
  that of a (`widthBoundMax_le_of_upperRecord`), so a verified range that reaches
  `widthBoundMax a` gives ClassDrops at every Order up to n
  (`classDropsAt_of_verifiedMax_record`), as `classDropsAt_of_verified_record` does
  with `widthBound`.
-/

namespace AcceleratedCollatz

/-- With a the last upper record Order up to n, widthBoundMax of every Order up to n is
    at most that of a. -/
theorem widthBoundMax_le_of_upperRecord {a n : ℕ} (ha : 1 ≤ a) (hR : UpperRecord a)
    (hno : ∀ k, a < k → k ≤ n → ¬UpperRecord k) {m : ℕ} (hmn : m ≤ n) :
    widthBoundMax m ≤ widthBoundMax a := by
  rcases Nat.eq_zero_or_pos m with h0 | hpos
  · subst h0
    have h0 : widthBoundMax 0 = 0 := by
      decide
    omega
  · exact widthBoundMax_le_of_rmax_le (rmax_le_of_blockFactor_le ha hpos fun k hk1 hkm =>
      blockFactor_le_of_upperRecord hR hno k hk1 (by omega))

/-- A verified range that reaches widthBoundMax of the last upper record Order up to n
    gives ClassDrops at every Order up to n. -/
theorem classDropsAt_of_verifiedMax_record (X : ℕ)
    (hX : ∀ x, 1 < x → x ≤ X → ∀ m, Admissible (tBits x m) → tStep^[m] x < x)
    {a n : ℕ} (ha : 1 ≤ a) (hR : UpperRecord a)
    (hno : ∀ k, a < k → k ≤ n → ¬UpperRecord k) (haX : widthBoundMax a ≤ X)
    {m : ℕ} (hmn : m ≤ n) : ClassDropsAt m :=
  classDropsAt_of_verifiedMax X hX m
    ((widthBoundMax_le_of_upperRecord ha hR hno hmn).trans haX)

end AcceleratedCollatz
