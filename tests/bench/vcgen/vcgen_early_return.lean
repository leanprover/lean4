/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
import Cases.EarlyReturn
import Driver

/-! Benchmark driver for `vcgen` on loops with an early return: `EarlyReturn` has a loop with `n`
`return` sites. -/

set_option experimental.vcgen true

open Lean Order Parser Meta Elab Tactic Sym Std WP

set_option maxRecDepth 10000
set_option maxHeartbeats 10000000

#eval runBenchUsingTactic ``EarlyReturn.Goal [``EarlyReturn.step10, ``EarlyReturn.step20, ``EarlyReturn.step40]
  `(tactic| vcgen) `(tactic| sorry) [10, 20, 40]
