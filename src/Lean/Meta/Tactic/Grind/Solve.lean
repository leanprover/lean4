/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Grind.Combinators
import Lean.Meta.Tactic.Grind.Split
import Lean.Meta.Tactic.Grind.EMatch

namespace Lean.Meta.Grind

namespace Solve

structure State where
  todo     : List Goal
  failures : List Goal := []
  stop     : Bool := false

private abbrev M := StateRefT State GrindM

def getNext? : M (Option Goal) := do
  let goal::todo := (← get).todo | return none
  modify fun s => { s with todo }
  return some goal

def pushGoal (goal : Goal) : M Unit :=
  modify fun s => { s with todo := goal :: s.todo }

def pushGoals (goals : List Goal) : M Unit :=
  modify fun s => { s with todo := goals ++ s.todo }

def pushFailure (goal : Goal) : M Unit := do
  modify fun s => { s with failures := goal :: s.failures }
  if (← get).failures.length ≥ (← getConfig).failures then
    modify fun s => { s with stop := true }

@[inline] def stepGuard (x : Goal → M Bool) (goal : Goal) : M Bool := do
  try
    x goal
  catch ex =>
    if ex.isMaxHeartbeat || ex.isMaxRecDepth then
      let goal ← goal.reportIssue ex.toMessageData
      pushFailure goal
      return true
    else
      throw ex

def applyTac (x : GrindTactic) (goal : Goal) : M Bool := do
  let go (goal : Goal) : M Bool := do
    let some goals ← x goal | return false
    pushGoals goals
    return true
  stepGuard go goal

def tryAssertNext : Goal → M Bool := applyTac assertNext

def tryEmatch : Goal → M Bool := applyTac ematchAndAssert

def trySplit : Goal → M Bool := applyTac splitNext

def maxNumFailuresReached : M Bool := do
  return (← get).failures.length ≥ (← getConfig).failures

partial def main : M Unit := do
  repeat do
    if (← get).stop then
      return ()
    let some goal ← getNext? |
      return ()
    if goal.inconsistent then
      continue
    if (← tryAssertNext goal) then
      continue
    if (← tryEmatch goal) then
      continue
    if (← trySplit goal) then
      continue
    pushFailure goal

end Solve

/--
Try to solve/close the given goals, and returns the ones that could not be solved.
-/
def solve (goals : List Goal) : GrindM (List Goal) := do
  let (_, s) ← Solve.main.run { todo := goals }
  let todo ← s.todo.mapM fun goal => do
    goal.reportIssue m!"this goal was not fully processed due to previous failures, threshold: `(failures := {(← getConfig).failures})`"
  return s.failures.reverse ++ todo

end Lean.Meta.Grind
