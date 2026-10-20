/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Types
public import Lean.Meta.Sym.Simp.SimpM
public import Lean.Meta.Sym.Apply
public import Lean.Meta.Sym.Simp.Discharger
import Lean.Meta.Tactic.Grind.Main
import Lean.Meta.Sym.Simp.Goal
import Lean.Meta.Sym.Intro
import Lean.Meta.Sym.Util
import Lean.Meta.Sym.InstantiateMVarsS
import Lean.Meta.Tactic.Grind.Solve
import Lean.Meta.Tactic.Assumption
namespace Lean.Meta.Grind

/-!
# Grind Goal API for Symbolic Simulation

This module provides an API for building symbolic simulation engines and
verification condition generators on top of `grind`. It wraps `Sym` operations
to work with `grind`'s `Goal` type, enabling users to carry `grind` state
through symbolic execution while using lightweight `Sym` operations for
the main loop.

## Typical usage pattern
```
let goal ← mkGoal mvarId
let .goal xs goal ← goal.introN 2 | failure
let .goal goal ← goal.simp methods | failure
let goal ← goal.internalizeAll
-- ... symbolic execution loop using goal.apply ...
let .closed ← goal.grind | failure
```

## Design

Operations like `introN`, `apply`, and `simp` run in `SymM` for performance.
`internalize` and `grind` run in `GrindM` to access the E-graph.

`Goal.mkSymSimpDischarger` creates a `Sym.simp` discharger that proves side conditions of
conditional rewrite rules using `grind`, sharing the goal's internalized local context
across discharge attempts.
-/


/--
Creates a `Goal` from an `MVarId`, applying `Sym` preprocessing.
Preprocessing ensures the goal is compatible with `Sym` operations.
-/
public def mkGoal (mvarId : MVarId) : GrindM Goal := do
  let mvarId ← Sym.preprocessMVar mvarId
  mkGoalCore mvarId

open Sym (SymM)

public inductive IntrosResult where
  | failed
  | goal (newDecls : Array FVarId) (goal : Goal)

/-- Introduces `num` binders from the goal's target. -/
public def Goal.introN (goal : Goal) (num : Nat) (hygienic : Bool := true) : SymM IntrosResult := do
  let .goal xs mvarId ← Sym.introN goal.mvarId num hygienic | return .failed
  return .goal xs { goal with mvarId }

/-- Introduces binders with the specified names. -/
public def Goal.intros (goal : Goal) (names : Array Name) (hygienic : Bool := true) : SymM IntrosResult := do
  let .goal xs mvarId ← Sym.intros goal.mvarId names hygienic | return .failed
  return .goal xs { goal with mvarId }

public inductive ApplyResult where
  | failed
  | goals (subgoals : List Goal)

/-- Applies a backward rule, returning subgoals on success. -/
public def Goal.apply (goal : Goal) (rule : Sym.BackwardRule) : SymM ApplyResult := do
  let .goals mvarIds ← rule.apply goal.mvarId | return .failed
  return .goals <| mvarIds.map fun mvarId => { goal with mvarId }

public inductive SimpGoalResult where
  | noProgress
  | closed
  | goal (goal : Goal)

/-- Simplifies the goal using the given methods. -/
public def Goal.simp (goal : Goal) (methods : Sym.Simp.Methods := {}) (config : Sym.Simp.Config := {}) : SymM SimpGoalResult := do
  match (← Sym.simpGoal goal.mvarId methods config) with
  | .goal mvarId => return .goal { goal with mvarId }
  | .noProgress  => return .noProgress
  | .closed => return .closed

/-- Like `simp`, but returns the original goal unchanged when no progress is made. -/
public def Goal.simpIgnoringNoProgress (goal : Goal) (methods : Sym.Simp.Methods := {}) (config : Sym.Simp.Config := {}) : SymM SimpGoalResult := do
  match (← Sym.simpGoal goal.mvarId methods config) with
  | .goal mvarId => return .goal { goal with mvarId }
  | .noProgress  => return .goal goal
  | .closed => return .closed

/--
Internalizes the next `num` hypotheses from the local context into the `grind` state (e.g., its E-graph).
-/
public def Goal.internalize (goal : Goal) (num : Nat) : GrindM Goal := do
  Grind.processHypotheses goal (some num)

/-- Internalizes all (un-internalized) hypotheses from the local context into the `grind` state. -/
public def Goal.internalizeAll (goal : Goal) : GrindM Goal := do
  Grind.processHypotheses goal none

public inductive GrindResult where
  | failed (goal : Goal)
  | closed

/--
Attempts to close the goal using `grind`.
Returns `.closed` on success, or `.failed` with the first subgoal that failed to be closed.
-/
public def Goal.grind (goal : Goal) : GrindM GrindResult := do
  if let some failure ← solve goal then
    return .failed failure
  else
    return .closed

/--
Closes the goal if its target matches a hypothesis.
Returns `true` on success.
-/
public def Goal.assumption (goal : Goal) : MetaM Bool := do
  -- **TODO**: add indexing
  goal.mvarId.assumptionCore

/--
Attempts to discharge the side condition `e` using `grind`, starting from `goal`'s state.

`goal`'s local context must be a prefix of the current local context, and its hypotheses
must have already been internalized (e.g., using `Goal.internalizeAll`). Only the remaining
local declarations (e.g., hypotheses introduced by `Sym.simp` when entering binders) are
internalized before invoking `grind`.

Results are marked as context-dependent since `grind` uses the local context.
Issues reported during the attempt are discarded because discharge attempts are speculative.
-/
def Goal.dischargeSymSimp (goal : Goal) (e : Expr) : GrindM Sym.Simp.DischargeResult := do
  -- `e` may contain metavariables assigned while processing the same rewrite step
  -- (e.g., hypotheses whose types mention previously discharged hypotheses).
  let e ← Sym.instantiateMVarsS e
  -- Issues live in the shared `Sym.State` (the base monad), not in the `Grind.State`
  -- copy discarded by `mkSymSimpDischarger`. Restore them since attempts are speculative.
  let savedIssues ← Sym.getIssues
  try
    let mvar ← mkFreshExprSyntheticOpaqueMVar e
    let goal := { goal with mvarId := mvar.mvarId! }
    let goal ← processHypotheses goal
    if (← solve goal).isSome then
      return .failed (contextDependent := true)
    else
      return .solved (← instantiateMVars mvar) (contextDependent := true)
  finally
    modifyThe Sym.State fun s => { s with issues := savedIssues }

/--
Creates a `Sym.simp` discharger that attempts to prove side conditions using `grind`.

The discharger is parametrized by the `grind` methods, context, and state `s`. Each discharge
attempt is terminal: it either produces a proof or fails. Thus, it runs `grind` on a copy of
`s` on top of the ambient `SymM` state, and the resulting `grind` state is discarded.

`goal` provides the initial `GoalState`. Internalizing the local context once (e.g., using
`Goal.internalizeAll`) and sharing the resulting `GoalState` across discharge attempts avoids
re-internalizing the common local context prefix for every side condition; only local
declarations introduced after `goal` was created are internalized per attempt.
-/
def mkSymSimpDischarger (goal : Goal) (methods : MethodsRef) (ctx : Context) (s : State) : Sym.Simp.Discharger := fun e => do
  goal.dischargeSymSimp e methods ctx |>.run' s

/--
Creates a `Sym.simp` discharger that attempts to prove side conditions using `grind`,
capturing the current `grind` methods, context, and state. See `mkSymSimpDischarger`.
-/
public def Goal.mkSymSimpDischarger (goal : Goal) : GrindM Sym.Simp.Discharger := do
  return Grind.mkSymSimpDischarger goal (← getMethodsRef) (← readThe Context) (← get)

end Lean.Meta.Grind
