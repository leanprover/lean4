/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Elab.Tactic.Grind.Basic
import Lean.Meta.Tactic.Grind.Intro
import Lean.Meta.Tactic.Grind.RevertAll
import Lean.Elab.SyntheticMVars
import Lean.Meta.Tactic.Grind.Solve
namespace Lean.Elab.Tactic.Grind
open Meta Grind

/-- Elaborate `stx` in the current `MVarContext`. If given, the `expectedType` will be used to help
elaboration but not enforced (use `elabTermEnsuringType` to enforce an expected type). -/
def elabTerm (stx : Syntax) (expectedType? : Option Expr) (mayPostpone := false) : GrindTacticM Expr :=
  withRef stx do Term.withoutTacticIncrementality true do withMainContext do
    if (← read).recover then
      go
    else
      Term.withoutErrToSorry go
where
  go : GrindTacticM Expr := do
    let e ← Term.elabTerm stx expectedType?
    Term.synthesizeSyntheticMVars (postpone := .ofBool mayPostpone)
    let e ← instantiateMVars e
    return e

@[builtin_grind_tactic Parser.Tactic.Grind.«have»] def evalHave : GrindTactic := fun stx => withMainContext do
  let `(grind| have $decl:letDecl) := stx | throwUnsupportedSyntax
  let stx' ← `(have $decl:letDecl; False)
  let e ← elabTerm stx' none
  let .letE n t v _ _ := e
    | throwError "elaborated term is not a `have` declaration{indentExpr e}"
  if t.hasMVar then throwError "type has metavariables{indentExpr t}"
  if v.hasMVar then throwError "value has metavariables{indentExpr v}"
  let goal ← getMainGoal
  let mvarId ← goal.mvarId.assert n t v
  let goal := { goal with mvarId }
  replaceMainGoal [goal]
  liftAction <| Action.intros 0

@[builtin_grind_tactic Parser.Tactic.Grind.haveSilent] def evalHaveSilent : GrindTactic := fun stx => withMainContext do
  let `(grind| have $[$id?:ident]? : $prop:term) := stx | throwUnsupportedSyntax
  let id := if let some id := id? then id.getId else `this
  let id := if id.hasMacroScopes then id else markGrindName id
  let prop ← elabTerm prop none
  let mvar ← mkFreshExprMVar prop
  let mvarId := mvar.mvarId!
  let goal :: goals ← getGoals | throwNoGoalsToBeSolved
  let goalNew := { goal with mvarId }
  setGoals [goalNew]
  if let some goal ← liftGrindM <| solve goalNew then
    let params := (← read).params
    let result ← liftGrindM do mkResult params (some goal)
    throwError "`finish` failed\n{← result.toMessageData}"
  let v ← instantiateMVars mvar
  let mvarId ← goal.mvarId.assert id prop v
  let goal := { goal with mvarId }
  setGoals (goal :: goals)
  liftAction <| Action.intros 0

end Lean.Elab.Tactic.Grind
