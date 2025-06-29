/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Grind.Split
import Lean.Meta.Tactic.Grind.EMatch
import Lean.Meta.Tactic.Grind.Arith
import Lean.Meta.Tactic.Grind.Lookahead
import Lean.Meta.Tactic.Grind.SearchM

namespace Lean.Meta.Grind
def tryFallback : GoalM Bool := do
  (← getMethods).fallback
  if (← isInconsistent)  then
    return true
  if (← (← get).mvarId.isAssigned) then
    -- User-provided fallback may not have properly set `inconsistent` flag.
    modify fun s => { s with inconsistent := true }
    return true
  return false

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
      if (← assertAll <||> Arith.check <||> ematch <||> lookahead <||> splitNext <||> Arith.Cutsat.mbtc
          <||> Arith.Linear.mbtc <||> tryFallback) then
        continue
      return some (← getGoal) -- failed
    return none -- solved

end Lean.Meta.Grind
