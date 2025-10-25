/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Types
import Lean.Meta.Tactic.Grind.Intro
import Lean.Meta.Tactic.Grind.Split
import Lean.Meta.Tactic.Grind.EMatch
public section
namespace Lean.Meta.Grind

private partial def solve (generation : Nat) : SearchM Bool := withIncRecDepth do
  unless (← get).choiceStack.isEmpty do
    return false -- `splitNext` should have been configured to not create choice points
  if (← getGoal).inconsistent then
    return true
  if (← intros' generation <||> assertAll <||> Solvers.check <||> splitNext <||> ematch) then
    solve generation
  else
    return false

private def tryLookahead (e : Expr) : GoalM Bool :=
  withTheReader Grind.Context
    (fun ctx => { ctx with config.qlia := true, cheapCases := true }) do
  -- TODO: if `e` is an arithmetic expression, we can avoid creating an auxiliary goal.
  -- We can assert it directly to the arithmetic module.
  -- Remark: We can simplify this code because the lookahead only really worked for arithmetic.
  trace_goal[grind.lookahead.try] "{e}"
  let goal ← get
  let proof? ← withoutModifyingMCtx do
    let tag ← goal.mvarId.getTag
    let target ← mkArrow (mkNot e) (← getFalseExpr)
    let mvar ← mkFreshExprSyntheticOpaqueMVar target tag
    let goalAux := { goal with mvarId := mvar.mvarId!, newFacts := {} }
    let gen ← getGeneration e
    let (ok, _) ← (solve gen).run goalAux
    if ok then
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

def lookahead : GoalM Bool := do
  unless (← getConfig).lookahead do
    return false
  if (← get).split.lookaheads.isEmpty then
    return false
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

end Lean.Meta.Grind
