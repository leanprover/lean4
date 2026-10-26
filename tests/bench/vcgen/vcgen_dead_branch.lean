/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
import Cases.DeadBranch
import Driver

set_option experimental.vcgen true

open Lean Order Parser Meta Elab Tactic Sym Std WP
open DeadBranch

-- Copy Goal into a separate namespace so the benchmark label reads `DeadBranchNoSimp(n)`
-- instead of colliding with the `DeadBranch(n)` label below.
namespace DeadBranchNoSimp
def Goal (n : Nat) : Prop := DeadBranch.Goal n
end DeadBranchNoSimp

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

#eval runBenchUsingTactic ``Goal [``loop, ``step] `(tactic| vcgen) `(tactic| fail)
  [100, 1000, 2000]

-- Every split keeps its dead path, so the number of verification conditions doubles with
-- each step.
#eval runBenchUsingTactic ``DeadBranchNoSimp.Goal [``DeadBranch.Goal, ``loop, ``step]
  `(tactic| vcgen -simp) `(tactic| grind)
  [6, 8, 10]
