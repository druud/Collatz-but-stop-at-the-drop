-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.PowDiffFarRhin2

/-!
# The upper walk to 10^200, stretch 3 of 4

The kernel checks the upper fraction of every node from `farNode200_2` to `farNode200_3`, at
K = 2^1330 (bracket from 2663 bits; its ends as literals from `PowDiffFarBracket`).
It imports `PowDiffFarRhin2` only to run after it, so `lake build` never runs two stretches
side by side.
-/

namespace PowDiff

open AcceleratedCollatz

set_option exponentiation.threshold 2000 in
/-- Stretch 3 of the upper walk to 10^200, computed by the kernel. -/
theorem rhinStretch_200_3 :
    walkTo (rhinOKAt (2 ^ 1330) (log2Hi 3 2663 1330))
      (2 ^ 1330) (log2Lo 3 2663 1330) (log2Hi 3 2663 1330)
      farNode200_3 1600 farNode200_2 = true := by
  rw [farLo200_eq, farHi200_eq]
  decide +kernel

end PowDiff
