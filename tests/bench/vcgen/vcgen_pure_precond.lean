/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
import Cases.PurePrecond
import Driver

set_option mvcgen.warning false

open Lean Parser Meta Elab Tactic Sym Std Do
open PurePrecond

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

example : Goal 10 := by
  simp only [Goal, loop, step]
  vcgen

#eval runBenchUsingTactic ``Goal [``loop, ``step] `(tactic| vcgen) `(tactic| fail)
  [400, 2400, 4400]
