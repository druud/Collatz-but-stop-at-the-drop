-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.PowDiffFarRhin4

/-!
# The lower walk to 10^200, stretch 1 of 4

The kernel checks the lower fraction of every node from the root to `farNode200_1`, at
K = 2^1330 (bracket from 2663 bits; its ends as literals from `PowDiffFarBracket`).
It imports `PowDiffFarRhin4` only to run after it, so `lake build` never runs two stretches
side by side.
-/

namespace PowDiff

open AcceleratedCollatz

set_option exponentiation.threshold 2000 in
/-- Stretch 1 of the lower walk to 10^200, computed by the kernel. -/
theorem lowStretch_200_1 :
    walkTo (lowOKAt (2 ^ 1330) (log2Lo 3 2663 1330))
      (2 ^ 1330) (log2Lo 3 2663 1330) (log2Hi 3 2663 1330)
      farNode200_1 1600 (sbWalk 0) = true := by
  rw [farLo200_eq, farHi200_eq]
  decide +kernel

end PowDiff
