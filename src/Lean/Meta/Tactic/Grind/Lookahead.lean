/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Grind.Types
import Lean.Meta.Tactic.Grind.Intro
import Lean.Meta.Tactic.Grind.Arith
import Lean.Meta.Tactic.Grind.Split
import Lean.Meta.Tactic.Grind.EMatch

namespace Lean.Meta.Grind

private partial def solve (generation : Nat) (goal : Goal) : GrindM Bool := do
  cont (← intros generation goal)
where
  cont (goals : List Goal) : GrindM Bool := do
    match goals with
    | [] => return true
    | [goal] => loop goal
    | _ => throwError "`grind` lookahead internal error, unexpected number of goals"

  loop (goal : Goal) : GrindM Bool := withIncRecDepth do
    if goal.inconsistent then
      return true
    else if let some goals ← assertNext goal then
      cont goals
    else if let some goals ← Arith.check goal then
      cont goals
    else if let some goals ← splitNext goal then
      cont goals
    else if let some goals ← ematchAndAssert goal then
      cont goals
    else
      return false

private def tryLookahead (e : Expr) : GoalM Bool := do
  -- TODO: if `e` is an arithmetic expression, we can avoid creating an auxiliary goal.
  -- We can assert it directly to the arithmetic module.
  -- Remark: We can simplify this code because the lookahead only really worked for arithmetic.
  trace_goal[grind.lookahead.try] "{e}"
  let proof? ← withoutModifyingState do
    let goal ← get
    let tag ← goal.mvarId.getTag
    let target ← mkArrow (mkNot e) (← getFalseExpr)
    let mvar ← mkFreshExprMVar target .syntheticOpaque tag
    let gen ← getGeneration e
    if (← solve gen { goal with mvarId := mvar.mvarId! }) then
      return some (← instantiateMVars mvar)
    else
      return none
  if let some proof := proof? then
    trace[grind.lookahead.assert] "{e}"
    pushEqTrue e <| mkApp2 (mkConst ``Grind.of_lookahead) e proof
    processNewFacts
    return true
  else
    return false

private def withLookaheadConfig (x : GrindM α) : GrindM α := do
  withTheReader Grind.Context
    (fun ctx => { ctx with config.qlia := true, cheapCases := true })
    x

def lookahead : GrindTactic := fun goal => do
  unless (← getConfig).lookahead do
    return none
  if goal.split.lookaheads.isEmpty then
    return none
  withLookaheadConfig do
  let (progress, goal) ← GoalM.run goal do
    let mut postponed := []
    let mut progress := false
    let infos := (← get).split.lookaheads
    modify fun s => { s with split.lookaheads := [] }
    for info in infos do
      if (← isInconsistent) then
        return true
      match (← checkSplitStatus info) with
      | .resolved => progress := true
      | .ready _ _ true
      | .notReady => postponed := info :: postponed
      | .ready _ _ false =>
        if (← tryLookahead info.getExpr) then
          progress := true
        else
          postponed := info :: postponed
    if progress then
      modify fun s => { s with
        split.lookaheads := s.split.lookaheads ++ postponed.reverse
      }
      return true
    else
      return false
  if progress then
    return some [goal]
  else
    return none

end Lean.Meta.Grind
