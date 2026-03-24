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
- `AddSubCancelSimp`: Like `AddSubCancel` but using simp/equational specs
- `GetThrowSet`: Exception handling with `ExceptT`/`StateM`
- `PurePrecond`: Pure hypotheses `⌜φ⌝` in preconditions
- `ReaderState`: `ReaderT`/`StateM` combination
- `DiteSplit`: Dependent if-then-else (`if h : cond then ...`)
- `MatchSplit`: Pattern matching in monadic programs
- `MatchSplitState`: Match on state variable (discriminant = excess state arg)
-/

open Lean Parser Meta Elab Tactic Sym Std Do SpecAttr

set_option maxRecDepth 10000
set_option maxHeartbeats 10000000

open AddSubCancel in
#eval runBenchUsingTactic ``Goal [``loop, ``step] `(tactic| mvcgen') `(tactic| grind) [10]

open AddSubCancelDeep in
#eval runBenchUsingTactic ``Goal [``loop, ``step] `(tactic| mvcgen') `(tactic| grind) [10]

open AddSubCancelSimp in
#eval runBenchUsingTactic ``Goal [``loop, ``step] `(tactic| mvcgen') `(tactic| grind) [10]

open GetThrowSet in
#eval runBenchUsingTactic ``Goal [``loop, ``step] `(tactic| mvcgen') `(tactic| sorry) [10]

-- Test `mvcgen' with grind`: grind integrated into VCGen loop
open GetThrowSet in
#eval runBenchUsingTactic ``Goal [``loop, ``step] `(tactic| mvcgen' with grind) `(tactic| fail) [10]

-- Test `mvcgen' with grind` on AddSubCancel
open AddSubCancel in
#eval runBenchUsingTactic ``Goal [``loop, ``step] `(tactic| mvcgen' with grind) `(tactic| fail) [10]

open PurePrecond in
#eval runBenchUsingTactic ``Goal [``loop, ``step] `(tactic| mvcgen') `(tactic| fail) [10]

open ReaderState in
#eval runBenchUsingTactic ``Goal [``loop, ``step] `(tactic| mvcgen') `(tactic| sorry) [10]

open DiteSplit in
#eval runBenchUsingTactic ``Goal [``loop, ``step] `(tactic| mvcgen') `(tactic| sorry) [10]

open MatchSplit in
#eval runBenchUsingTactic ``Goal [``loop, ``step] `(tactic| mvcgen') `(tactic| sorry) [10]

open MatchSplitState in
#eval runBenchUsingTactic ``Goal [``loop, ``step] `(tactic| mvcgen') `(tactic| grind) [10]
