-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.PowDiffFarBracket

/-!
# The upper walk to 10^200, stretch 1 of 4

The kernel checks the upper fraction of every node from the root to `farNode200_1`, at
K = 2^1330 (bracket from 2663 bits; its ends as literals from `PowDiffFarBracket`).
Its end node comes from `PowDiffFarNodes`, through `PowDiffFarBracket`.
-/

namespace PowDiff

open AcceleratedCollatz

set_option exponentiation.threshold 2000 in
/-- Stretch 1 of the upper walk to 10^200, computed by the kernel. -/
theorem rhinStretch_200_1 :
    walkTo (rhinOKAt (2 ^ 1330) (log2Hi 3 2663 1330))
      (2 ^ 1330) (log2Lo 3 2663 1330) (log2Hi 3 2663 1330)
      farNode200_1 1600 (sbWalk 0) = true := by
  rw [farLo200_eq, farHi200_eq]
  decide +kernel

end PowDiff
