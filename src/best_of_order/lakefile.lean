-- SPDX-License-Identifier: MIT
import Lake
open Lake DSL

/-- The best of the Order: the exact statements of the paper *Collatz, but stop at the drop:
    the start words with the highest drop ratio*. Its words, maps and constants come from
    `AcceleratedCollatz` (one bridge file, `BestOfOrder.Bridge`); the table of bests stays
    script data. The packages directory is shared with `accelerated_collatz`. -/
package best_of_order where
  version := v!"0.1.0"
  keywords := #["math"]
  packagesDir := "../lean_files/.lake/packages"
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`linter.style.header, false⟩
  ]

require accelerated_collatz from ".." / "lean_files"

@[default_target]
lean_lib BestOfOrder where
  globs := #[.andSubmodules `BestOfOrder]
