/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Grind.Combinators
import Lean.Meta.Tactic.Grind.Split
import Lean.Meta.Tactic.Grind.EMatch
import Lean.Meta.Tactic.Grind.Arith
import Lean.Meta.Tactic.Grind.Lookahead
import Lean.Meta.Tactic.Grind.SearchM

namespace Lean.Meta.Grind
/--
Try to solve/close the given goal.
Returns `some goal` if this subgoal failed to be closed,
and `none` if all subgoals were closed.
-/
def solve (goal : Goal) (fallback : Fallback) : GrindM (Option Goal) := do
  let (failed?, _) ← main.run goal
  return failed?
where
  main : SearchM (Option Goal) := do
    repeat
      if (← getGoal).inconsistent then
        if let some gen ← nextGoal? then
          intros gen
        else
          break
      if (← assertAll <||> Arith.check <||> ematch <||> lookahead <||> splitNext <||> Arith.Cutsat.mbtc <||> tryFallback) then
        continue
      return some (← getGoal) -- failed
    return none -- solved

  tryFallback : GoalM Bool := do
    fallback
    if (← isInconsistent)  then
      return true
    if (← (← get).mvarId.isAssigned) then
      -- User-provided fallback may not have properly set `inconsistent` flag.
      modify fun s => { s with inconsistent := true }
      return true
    return false

/-! TODO: delete rest of the file. -/

namespace Solve

structure State where
  todo     : List Goal
  failure? : Option Goal := none

private abbrev M := StateRefT State GrindM

def getNext? : M (Option Goal) := do
  let goal::todo := (← get).todo | return none
  modify fun s => { s with todo }
  return some goal

def pushGoal (goal : Goal) : M Unit :=
  modify fun s => { s with todo := goal :: s.todo }

def pushGoals (goals : List Goal) : M Unit :=
  modify fun s => { s with todo := goals ++ s.todo }

def setFailure (goal : Goal) : M Unit := do
  modify fun s => { s with failure? := some goal }

@[inline] def stepGuard (x : Goal → M Bool) (goal : Goal) : M Bool := do
  tryCatchRuntimeEx
    (x goal)
    fun ex => do
      if ex.isMaxHeartbeat || ex.isMaxRecDepth then
        reportIssue! ex.toMessageData
        setFailure goal
        return true
      else
        throw ex

def applyTac (x : GrindTactic) (goal : Goal) : M Bool := do
  let go (goal : Goal) : M Bool := do
    let some goals ← x goal | return false
    pushGoals goals
    return true
  stepGuard go goal

def tryAssertAll : Goal → M Bool := applyTac assertAllOld

def tryEmatch : Goal → M Bool := applyTac ematchOld

def tryArith : Goal → M Bool := applyTac Arith.checkOld

def tryLookahead : Goal → M Bool := applyTac lookaheadOld

def tryMBTC : Goal → M Bool := applyTac Arith.Cutsat.mbtcTac

def trySplit : Goal → M Bool := applyTac splitNextOld

partial def main (fallback : Fallback) : M Unit := do
  repeat do
    if (← get).failure?.isSome then
      return ()
    let some goal ← getNext? |
      return ()
    if goal.inconsistent then
      continue
    if (← tryAssertAll goal) then
      continue
    if (← tryArith goal) then
      continue
    if (← tryEmatch goal) then
      continue
    if (← tryLookahead goal) then
      continue
    if (← trySplit goal) then
      continue
    if (← tryMBTC goal) then
      continue
    let goal ← GoalM.run' goal fallback
    if goal.inconsistent || (← goal.mvarId.isAssigned) then
      continue
    setFailure goal

end Solve

/--
Try to solve/close the given goals.
Returns `some goal` if this subgoal failed to be closed,
and `none` if all subgoals were closed.
-/
def solveOld (goals : List Goal) (fallback : Fallback) : GrindM (Option Goal) := do
  let (_, s) ← Solve.main fallback |>.run { todo := goals }
  return s.failure?

end Lean.Meta.Grind
