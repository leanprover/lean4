/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
import Cases.ScalarProduct
import Driver

/-!
Measures `vcgen … with finish` on the `ScalarProduct` block, together with the `grind` proofs that
re-establish the loop invariant at every exit.
-/

set_option experimental.vcgen true

open Lean Order Parser Meta Elab Tactic Sym Std WP
open ScalarProduct

set_option maxRecDepth 10000
set_option maxHeartbeats 10000000

#eval runBenchUsingTactic ``ScalarProduct.Goal [``prog, ``exits]
  `(tactic| vcgen with finish)
  `(tactic| fail)
  [4, 8, 12]
