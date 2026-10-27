/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
import Cases.LoopInvariant
import Driver

/-!
Measures `vcgen` and `vcgen … with finish` on the `LoopInvariant` block. `LoopInvariant(n)`
reports VC generation alone and the number of VCs. `LoopInvariantGrind(n)` reports VC generation
together with the `grind` proofs that re-establish the loop invariant at every exit.
-/

set_option experimental.vcgen true

open Lean Order Parser Meta Elab Tactic Sym Std WP
open LoopInvariant

namespace LoopInvariantGrind
def Goal (n : Nat) : Prop := LoopInvariant.Goal n
end LoopInvariantGrind

set_option maxRecDepth 10000
set_option maxHeartbeats 10000000

#eval runBenchUsingTactic ``LoopInvariant.Goal [``prog, ``exits]
  `(tactic| vcgen simplifying_assumptions [M.rdi_mk, M.rdx_mk, M.rcx_mk, M.r8_mk, M.lt_mk])
  `(tactic| sorry)
  [3, 8, 16, 24]

#eval runBenchUsingTactic ``LoopInvariantGrind.Goal [``LoopInvariant.Goal, ``prog, ``exits]
  `(tactic| vcgen simplifying_assumptions [M.rdi_mk, M.rdx_mk, M.rcx_mk, M.r8_mk, M.lt_mk]
    with finish -abstractProof)
  `(tactic| fail)
  [3, 8, 16, 24]
