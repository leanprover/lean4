/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
import Cases.PurePrecond
import Driver

open Lean Parser Meta Elab Tactic Sym Std Do SpecAttr
open PurePrecond

set_option maxRecDepth 10000
set_option maxHeartbeats 10000000

example : Goal 10 := by
  simp only [Goal, loop, step]
  mvcgen'

#eval runBenchUsingTactic ``Goal [``loop, ``step] `(tactic| mvcgen') `(tactic| fail)
  [100, 400, 700]
