/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Match.MatchEqs
import Lean.Meta.Tactic.Generalize

namespace Lean.Meta
namespace Split

private def genMatchDiscrs (mvarId : MVarId) (discrs : Array Expr) : MetaM (Array FVarId × MVarId) := do
  if discrs.all (·.isFVar) then
    return (discrs.map (·.fvarId!), mvarId)
  else
    let args ← discrs.mapM fun d => return { expr := d, hName? := (← mkFreshUserName `h) : GeneralizeArg }
    let (fvarIds, mvarId) ← generalize mvarId args
    return (fvarIds[:discrs.size], mvarId)

def splitMatch (mvarId : MVarId) (e : Expr) : MetaM (List MVarId) := do
  let some app ← matchMatcherApp? e | throwError "match application expected"
  let (discrFVarIds, mvarId) ← genMatchDiscrs mvarId app.discrs
  trace[Meta.debug] "split [1]:\n{MessageData.ofGoal mvarId}"
  let (reverted, mvarId) ← revert mvarId discrFVarIds
  trace[Meta.debug] "split [2]:\n{MessageData.ofGoal mvarId}"
  let (discrFVarIds, mvarId) ← introNP mvarId discrFVarIds.size
  trace[Meta.debug] "split [3]:\n{MessageData.ofGoal mvarId}"
  let discrs := discrFVarIds.map mkFVar
  let matchEqns ← Match.getEquationsFor app.matcherName
  withMVarContext mvarId do
    let motive ← mkLambdaFVars discrs (← getMVarType mvarId)
    trace[Meta.debug] "split [4]: {motive}"
    -- Fix universe
    let mut us := app.matcherLevels
    if let some uElimPos := app.uElimPos? then
      -- Set universe elimination level to zero (Prop).
      us := us.set! uElimPos levelZero
    trace[Meta.debug] "us: {us}"
    let splitter := mkAppN (mkConst matchEqns.splitterName us.toList) app.params
    let splitter := mkAppN (mkApp splitter motive) discrs
    trace[Meta.debug] "splitter: {splitter}"
    check splitter -- TODO
    let mvarIds ← apply mvarId splitter
    mvarIds.mapM fun mvarId => do
      trace[Meta.debug] "split [5]:\n{MessageData.ofGoal mvarId}"
      -- TODO: fix intros, use equation lemmas to reduce `match`-expressions
      let (_, mvarId) ← intros mvarId
      return mvarId

/-- Return an `if-then-else` or `match-expr` to split. -/
partial def findSplit? (env : Environment) (e : Expr) : Option Expr :=
  if let some target := e.find? fun e => !e.hasLooseBVars && (e.isIte || e.isDIte || isMatcherAppCore env e) then
    if e.isIte || e.isDIte then
      let cond := target.getArg! 1 5
      -- Try to find a nested `if` in `cond`
      findSplit? env cond |>.getD target
    else
      some target
  else
    none

end Split

open Split

def splitTarget? (mvarId : MVarId) : MetaM (Option (List MVarId)) := commitWhenSome? do
  if let some e := findSplit? (← getEnv) (← getMVarType mvarId) then
    if e.isIte || e.isDIte then
      return (← splitIfTarget? mvarId).map fun (s₁, s₂) => [s₁.mvarId, s₂.mvarId]
    else
      splitMatch mvarId e
  else
    return none

end Lean.Meta
