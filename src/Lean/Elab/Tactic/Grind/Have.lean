/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Elab.Tactic.Grind.Basic
import Init.Grind.Interactive
import Lean.Meta.Tactic.Assert
import Lean.Meta.Tactic.Grind.Intro
import Lean.Meta.Tactic.Grind.SearchM
import Lean.Elab.SyntheticMVars
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
  match stx with
  | `(grind| have $decl:letDecl) =>
    let stx' ← `(have $decl:letDecl; False)
    let e ← elabTerm stx' none
    let .letE n t v _ _ := e
      | throwError "elaborated term is not a `have` declaration{indentExpr e}"
    if t.hasMVar then throwError "type has metavariables{indentExpr t}"
    if v.hasMVar then throwError "value has metavariables{indentExpr v}"
    let goal ← getMainGoal
    let mvarId ← goal.mvarId.assert n t v
    let goal := { goal with mvarId }
    let (goal, _) ← liftGrindM <| withCheapCasesOnly <| SearchM.run goal do
      intros 0
      getGoal
    replaceMainGoal [goal]
  | _ => throwUnsupportedSyntax

end Lean.Elab.Tactic.Grind
