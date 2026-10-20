-- SPDX-License-Identifier: MIT
import Lake
import Std.Internal.UV.System
open Lake DSL

package accelerated_collatz where
  version := v!"0.1.0"
  keywords := #["math"]
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`weak.linter.mathlibStandardSet, true⟩,
    ⟨`maxSynthPendingDepth, (3 : Nat)⟩,
    ⟨`linter.style.header, false⟩
  ]

require "leanprover-community" / "mathlib" @ git "v4.35.0-rc3"

/-- Sets `LEAN_NAT_MAX_SIZE` in Lake's own process, when unset, before any module of the
    library is compiled: TFiniteCheck needs at least 300000000. -/
target natMaxSize : Unit := do
  if (← IO.getEnv "LEAN_NAT_MAX_SIZE").isNone then
    Std.Internal.UV.System.osSetenv "LEAN_NAT_MAX_SIZE" "1000000000"
  return Job.pure ()

@[default_target]
lean_lib AcceleratedCollatz where
  globs := #[.andSubmodules `AcceleratedCollatz]
  extraDepTargets := #[`natMaxSize]
