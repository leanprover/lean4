/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.SearchM
import Lean.Meta.Tactic.Grind.Split
import Lean.Meta.Tactic.Grind.EMatch
import Lean.Meta.Tactic.Grind.Lookahead
import Lean.Meta.Tactic.Grind.Intro
public section
namespace Lean.Meta.Grind

def checkSolvers : SearchM Bool := do
  if (← getConfig).trace then
    let some solverIds ← Solvers.check? | return false
    modify fun s => { s with steps := s.steps ++ solverIds.map (.solver ·) }
    return true
  else
    Solvers.check

def ematchStep : SearchM Bool := do
  if (← getConfig).trace then
    let .true ← ematch | return false
    -- TODO: Collect instances
    modify fun s => { s with steps := s.steps.push <| .instantiate [] [] }
    return true
  else
    ematch

def mbtcStep : SearchM Bool := do
  let .true ← Solvers.mbtc | return false
  if (← getConfig).trace then
    modify fun s => { s with steps := s.steps.push .mbtc }
  return true

def lookaheadStep : SearchM Bool := do
  let .true ← lookahead | return false
  if (← getConfig).trace then
    modify fun s => { s with steps := s.steps.push .lookahead }
  return true

/--
Try to solve/close the given goal.
Returns `some goal` if this subgoal failed to be closed,
and `none` if all subgoals were closed.
-/
def solve (goal : Goal) : GrindM (Option Goal) := do
  let (failed?, _) ← main.run goal
  return failed?
where
  main : SearchM (Option Goal) := do
    tryCatchRuntimeEx loop
      fun ex => do
        if ex.isMaxHeartbeat || ex.isMaxRecDepth then
          reportIssue! ex.toMessageData
          return some (← getGoal)
        else
          throw ex

  loop : SearchM (Option Goal) := do
    intros 0
    repeat
      if (← getGoal).inconsistent then
        if let some gen ← nextGoal? then
          intros gen
        else
          break
      if (← assertAll <||> checkSolvers <||> ematchStep <||> lookaheadStep <||> splitNext
           <||> mbtcStep) then
        continue
      return some (← getGoal) -- failed
    return none -- solved

end Lean.Meta.Grind
