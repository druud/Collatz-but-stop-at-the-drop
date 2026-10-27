-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.PowDiffFarLow4

/-!
# Both walk bounds up to Order 10^200

The four stretches of each walk (`PowDiffFarRhin1` to `PowDiffFarRhin4`, `PowDiffFarLow1` to
`PowDiffFarLow4`) joined by `walkedTo_start` and `walkedTo_next`: the upper and the lower
side up to Order 10^200, and with both, no power of 2 comes close to a power of 3 for
exponents of 3 up to 10^200.
-/

namespace PowDiff

open AcceleratedCollatz

/-- The last end node lies past 10^200. -/
theorem farNode200_4_past : 10 ^ 200 < farNode200_4.loDen + farNode200_4.hiDen := by
  decide +kernel

/-- `RhinBound 1 2` for every Order 1 ≤ n ≤ 10^200. -/
theorem rhinBoundUpTo_one_two_200 : RhinBoundUpTo 1 2 (10 ^ 200) :=
  rhinBoundUpTo_of_walkedTo
    (walkedTo_next (walkedTo_next (walkedTo_next (walkedTo_start rhinStretch_200_1)
      rhinStretch_200_2)
      rhinStretch_200_3)
      rhinStretch_200_4)
    farNode200_4_past

/-- 2^(Q-1) (1 + Q^2) ≤ Q^2 3^n with Q = p2(n), for every Order 1 ≤ n ≤ 10^200. -/
theorem lowAt_upTo_200 : ∀ n, 1 ≤ n → n ≤ 10 ^ 200 → LowAt n :=
  lowAt_of_walkedTo
    (walkedTo_next (walkedTo_next (walkedTo_next (walkedTo_start lowStretch_200_1)
      lowStretch_200_2)
      lowStretch_200_3)
      lowStretch_200_4)
    farNode200_4_past

/-- min(2^i, 3^j) ≤ p2(j)^2 |2^i - 3^j| for 1 ≤ j ≤ 10^200. -/
theorem min_le_of_walk_200 {i j : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ 10 ^ 200) :
    min (2 ^ i) (3 ^ j) ≤ p2_of j ^ 2 * D (2 ^ i) (3 ^ j) :=
  min_le_of_walks rhinBoundUpTo_one_two_200 lowAt_upTo_200 hj1 hj

end PowDiff
