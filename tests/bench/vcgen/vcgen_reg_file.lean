/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
import Cases.RegFile
import Driver

set_option experimental.vcgen true

open Lean Order Parser Meta Elab Tactic Sym Std WP
open RegFile

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

-- `vcgen` folds the state into a `Regs.mk` literal with the `@[vcgen_simp]` theorems.
#eval runBenchUsingTactic ``Goal [``loop, ``step] `(tactic| vcgen with finish) `(tactic| fail)
  [128, 256, 384]
