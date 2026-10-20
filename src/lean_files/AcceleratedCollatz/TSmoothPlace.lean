-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TSmoothClass
import AcceleratedCollatz.TSmoothPlaceQ

/-!
  The place of 2^j 3^i among the 3-smooth numbers (paper sec:sweeps), the q = 3 case of
  `TSmoothPlaceQ`: below 2^j 3^i there are i j + p2(1) + ... + p2(i) of them, plus the
  sum over k ≤ j of the round-ups of k log 2 / log 3 (`card_smoothBelowAt`, Mintz 1981),
  counted as pairs of exponents, which is their count as numbers (`latticeOrd_two_three`).
  For i = 0 this is `card_smoothBelow` (`smoothBelowAt_zero`).
-/

namespace AcceleratedCollatz

/-- The pairs (j', i') with 2^j' 3^i' < 2^j 3^i. -/
def smoothBelowAt (j i : ℕ) : Finset (ℕ × ℕ) := smoothBelowAtQ 3 j i

/-- (j', i') is in `smoothBelowAt j i` exactly when 2^j' 3^i' < 2^j 3^i. -/
theorem mem_smoothBelowAt {j i : ℕ} {x : ℕ × ℕ} :
    x ∈ smoothBelowAt j i ↔ 2 ^ x.1 * 3 ^ x.2 < 2 ^ j * 3 ^ i :=
  mem_smoothBelowAtQ le_rfl

/-- For i = 0 these are the pairs of `smoothBelow`. -/
theorem smoothBelowAt_zero (B : ℕ) : smoothBelowAt B 0 = smoothBelow B :=
  smoothBelowAtQ_zero le_rfl B

/-- The number of 3-smooth numbers below 2^j 3^i, as pairs (j', i'), is i j, plus the sum
    of p2(k) over 1 ≤ k ≤ i, plus the sum over k ≤ j of the round-ups of
    k log 2 / log 3. -/
theorem card_smoothBelowAt (j i : ℕ) :
    (smoothBelowAt j i).card = i * j + ∑ k ∈ Finset.range i, p2_of (k + 1) +
      ∑ k ∈ Finset.range (j + 1), Nat.clog 3 (2 ^ k) :=
  card_smoothBelowAtQ (by decide) le_rfl j i

/-- The place of 2^j 3^i in the increasing list of the 3-smooth numbers, counted from 0,
    is the number of these pairs. -/
theorem latticeOrd_two_three (j i : ℕ) :
    latticeOrd 2 3 (2 ^ j * 3 ^ i) = (smoothBelowAt j i).card :=
  latticeOrd_eq_place (by decide) (by norm_num) (by norm_num) j i

end AcceleratedCollatz
