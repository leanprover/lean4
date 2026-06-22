/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
import Cases.ReaderState
import Driver

set_option mvcgen.warning false

open Lean Order Parser Meta Elab Tactic Sym Std Internal.Do
open ReaderState

set_option maxRecDepth 10000
set_option maxHeartbeats 10000000

#eval runBenchUsingTactic ``Goal [``loop, ``step] `(tactic| vcgen) `(tactic| sorry) -- grind scales superlinearly here
  [600, 1600, 2600]
  -- [1000]
