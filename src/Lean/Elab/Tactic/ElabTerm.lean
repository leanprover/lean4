/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.CollectMVars
import Lean.Meta.Tactic.Apply
import Lean.Meta.Tactic.Assert
import Lean.Elab.Tactic.Basic
import Lean.Elab.SyntheticMVars

namespace Lean.Elab.Tactic
open Meta

/- `elabTerm` for Tactics and basic tactics that use it. -/

def elabTerm (stx : Syntax) (expectedType? : Option Expr) (mayPostpone := false) : TacticM Expr :=
  withRef stx $ liftTermElabM $ Term.withoutErrToSorry do
    let e ← Term.elabTerm stx expectedType?
    Term.synthesizeSyntheticMVars mayPostpone
    instantiateMVars e

def elabTermEnsuringType (stx : Syntax) (expectedType? : Option Expr) (mayPostpone := false) : TacticM Expr := do
  let e ← elabTerm stx expectedType? mayPostpone
  ensureHasType expectedType? e

@[builtinTactic «exact»] def evalExact : Tactic := fun stx =>
  match_syntax stx with
  | `(tactic| exact $e) => do
    let (g, gs) ← getMainGoal
    withMVarContext g do
      let decl ← getMVarDecl g
      let val  ← elabTermEnsuringType e decl.type
      ensureHasNoMVars val
      assignExprMVar g val
    setGoals gs
  | _ => throwUnsupportedSyntax

def elabTermWithHoles (stx : Syntax) (expectedType? : Option Expr) (tagSuffix : Name) (allowNaturalHoles := false) : TacticM (Expr × List MVarId) := do
  let val ← elabTermEnsuringType stx expectedType?
  let newMVarIds ← getMVarsNoDelayed val
  /- ignore let-rec auxiliary variables, they are synthesized automatically later -/
  let newMVarIds ← newMVarIds.filterM fun mvarId => return !(← Term.isLetRecAuxMVar mvarId)
  let newMVarIds ←
    if allowNaturalHoles then
      pure newMVarIds.toList
    else
      let naturalMVarIds ← newMVarIds.filterM fun mvarId => return (← getMVarDecl mvarId).kind.isNatural
      let syntheticMVarIds ← newMVarIds.filterM fun mvarId => return !(← getMVarDecl mvarId).kind.isNatural
      Term.logUnassignedUsingErrorInfos naturalMVarIds
      pure syntheticMVarIds.toList
  tagUntaggedGoals (← getMainTag) tagSuffix newMVarIds
  pure (val, newMVarIds)

/- If `allowNaturalHoles == true`, then we allow the resultant expression to contain unassigned "natural" metavariables.
   Recall that "natutal" metavariables are created for explicit holes `_` and implicit arguments. They are meant to be
   filled by typing constraints.
   "Synthetic" metavariables are meant to be filled by tactics and are usually created using the synthetic hole notation `?<hole-name>`. -/
def refineCore (stx : Syntax) (tagSuffix : Name) (allowNaturalHoles : Bool) : TacticM Unit := do
  let (g, gs) ← getMainGoal
  withMVarContext g do
    let decl ← getMVarDecl g
    let (val, gs') ← elabTermWithHoles stx decl.type tagSuffix allowNaturalHoles
    assignExprMVar g val
    setGoals (gs ++ gs')

@[builtinTactic «refine»] def evalRefine : Tactic := fun stx =>
  match_syntax stx with
  | `(tactic| refine $e) => refineCore e `refine (allowNaturalHoles := false)
  | _                    => throwUnsupportedSyntax

@[builtinTactic «refine!»] def evalRefineBang : Tactic := fun stx =>
  match_syntax stx with
  | `(tactic| refine! $e) => refineCore e `refine (allowNaturalHoles := true)
  | _                     => throwUnsupportedSyntax

@[builtinTactic Lean.Parser.Tactic.apply] def evalApply : Tactic := fun stx =>
  match_syntax stx with
  | `(tactic| apply $e) => do
    let (g, gs) ← getMainGoal
    let gs' ← withMVarContext g do
      let decl ← getMVarDecl g
      let val  ← elabTerm e none true
      let gs'  ← Meta.apply g val
      Term.synthesizeSyntheticMVarsNoPostponing
      pure gs'
    -- TODO: handle optParam and autoParam
    setGoals (gs' ++ gs)
  | _ => throwUnsupportedSyntax

/--
  Elaborate `stx`. If it a free variable, return it. Otherwise, assert it, and return the free variable.
  Note that, the main goal is updated when `Meta.assert` is used in the second case. -/
def elabAsFVar (stx : Syntax) (userName? : Option Name := none) : TacticM FVarId := do
  let (mvarId, others) ← getMainGoal
  withMVarContext mvarId do
    let e ← elabTerm stx none
    match e with
    | Expr.fvar fvarId _ => pure fvarId
    | _ =>
      let type ← inferType e
      let intro (userName : Name) (preserveBinderNames : Bool) : TacticM FVarId := do
        let (fvarId, mvarId) ← liftMetaM do
          let mvarId ← Meta.assert mvarId userName type e
          Meta.intro1Core mvarId preserveBinderNames
        setGoals $ mvarId::others
        pure fvarId
      match userName? with
      | none          => intro `h false
      | some userName => intro userName true

end Lean.Elab.Tactic
