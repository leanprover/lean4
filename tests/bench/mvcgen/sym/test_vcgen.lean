/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
import Cases
import Driver

/-!
# VCGen Test Suite

Runs all VCGen test cases at small sizes (n=10) to verify correctness.
Each case exercises a different aspect of the VC generation:

- `AddSubCancel`: Basic add/sub loop in `StateM`
- `AddSubCancelDeep`: Same loop through a deep monad transformer stack
- `GetThrowSet`: Exception handling with `ExceptT`/`StateM`
- `PurePrecond`: Pure hypotheses `⌜φ⌝` in preconditions
- `ReaderState`: `ReaderT`/`StateM` combination
-/

open Lean Parser Meta Elab Tactic Sym Std Do SpecAttr

set_option maxRecDepth 10000
set_option maxHeartbeats 10000000

open AddSubCancel in
#eval runBenchUsingTactic ``Goal [``loop, ``step] `(tactic| mvcgen') `(tactic| grind) [10]

open AddSubCancelDeep in
#eval runBenchUsingTactic ``Goal [``loop, ``step] `(tactic| mvcgen') `(tactic| grind) [10]

open GetThrowSet in
#eval runBenchUsingTactic ``Goal [``loop, ``step] `(tactic| mvcgen') `(tactic| sorry) [10]

open PurePrecond in
#eval runBenchUsingTactic ``Goal [``loop, ``step] `(tactic| mvcgen') `(tactic| fail) [10]

open ReaderState in
#eval runBenchUsingTactic ``Goal [``loop, ``step] `(tactic| mvcgen') `(tactic| sorry) [10]
