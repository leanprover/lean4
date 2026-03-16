/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
import Cases.AddSubCancelSimp
import Driver

open Lean Parser Meta Elab Tactic Sym Std Do SpecAttr
open AddSubCancelSimp

set_option maxRecDepth 10000
set_option maxHeartbeats 10000000

#eval runBenchUsingTactic ``Goal [``loop, ``step] `(tactic| mvcgen') `(tactic| grind)
  [100, 500, 1000]
