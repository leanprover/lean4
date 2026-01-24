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
import Lean.Meta.Tactic.Grind.Main
import Lean.Meta.Sym.Simp.Goal
import Lean.Meta.Sym.Intro
import Lean.Meta.Sym.Util
import Lean.Meta.Tactic.Grind.Solve
import Lean.Meta.Tactic.Assumption
namespace Lean.Meta.Grind

public def mkGoal (mvarId : MVarId) : GrindM Goal := do
  let mvarId ← Sym.preprocessMVar mvarId
  mkGoalCore mvarId

open Sym (SymM)

public inductive IntrosResult where
  | failed
  | goal (newDecls : Array FVarId) (goal : Goal)

public def Goal.introN (goal : Goal) (num : Nat) : SymM IntrosResult := do
  let .goal xs mvarId ← Sym.introN goal.mvarId num | return .failed
  return .goal xs { goal with mvarId }

public def Goal.intros (goal : Goal) (names : Array Name) : SymM IntrosResult := do
  let .goal xs mvarId ← Sym.intros goal.mvarId names | return .failed
  return .goal xs { goal with mvarId }

public inductive ApplyResult where
  | failed
  | goals (subgoals : List Goal)

public def Goal.apply (goal : Goal) (rule : Sym.BackwardRule) : SymM ApplyResult := do
  let .goals mvarIds ← rule.apply goal.mvarId | return .failed
  return .goals <| mvarIds.map fun mvarId => { goal with mvarId }

public inductive SimpGoalResult where
  | noProgress
  | closed
  | goal (goal : Goal)

public def Goal.simp (goal : Goal) (methods : Sym.Simp.Methods := {}) (config : Sym.Simp.Config := {}) : SymM SimpGoalResult := do
  match (← Sym.simpGoal goal.mvarId methods config) with
  | .goal mvarId => return .goal { goal with mvarId }
  | .noProgress  => return .noProgress
  | .closed => return .closed

public def Goal.simpIgnoringNoProgress (goal : Goal) (methods : Sym.Simp.Methods := {}) (config : Sym.Simp.Config := {}) : SymM SimpGoalResult := do
  match (← Sym.simpGoal goal.mvarId methods config) with
  | .goal mvarId => return .goal { goal with mvarId }
  | .noProgress  => return .goal goal
  | .closed => return .closed

public def Goal.internalize (goal : Goal) (num : Nat) : GrindM Goal := do
  Grind.processHypotheses goal (some num)

public def Goal.internalizeAll (goal : Goal) : GrindM Goal := do
  Grind.processHypotheses goal none

public inductive GrindResult where
  | failed (goal : Goal)
  | closed

public def Goal.grind (goal : Goal) : GrindM GrindResult := do
  withProtectedMCtx (← getConfig) goal.mvarId fun mvarId => do
    if let some failure ← solve { goal with mvarId } then
      return .failed failure
    else
      return .closed

public def Goal.assumption (goal : Goal) : MetaM Bool := do
  -- **TODO**: add indexing
  goal.mvarId.assumptionCore

end Lean.Meta.Grind
