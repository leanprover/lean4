/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.CollectMVars
import Lean.Meta.Tactic.Apply
import Lean.Meta.Tactic.Constructor
import Lean.Meta.Tactic.Assert
import Lean.Elab.Tactic.Basic
import Lean.Elab.SyntheticMVars

namespace Lean.Elab.Tactic
open Meta

/- `elabTerm` for Tactics and basic tactics that use it. -/

def elabTerm (stx : Syntax) (expectedType? : Option Expr) (mayPostpone := false) : TacticM Expr :=
  withRef stx <| Term.withoutErrToSorry do
    let e ← Term.elabTerm stx expectedType?
    Term.synthesizeSyntheticMVars mayPostpone
    instantiateMVars e

def elabTermEnsuringType (stx : Syntax) (expectedType? : Option Expr) (mayPostpone := false) : TacticM Expr := do
  let e ← elabTerm stx expectedType? mayPostpone
  Term.ensureHasType expectedType? e

/- Try to close main goal using `x target`, where `target` is the type of the main goal.  -/
def closeMainUsing (x : Expr → TacticM Expr) : TacticM Unit := do
  let (g, gs) ← getMainGoal
  withMVarContext g do
    let decl ← getMVarDecl g
    let val  ← x decl.type
    ensureHasNoMVars val
    assignExprMVar g val
  setGoals gs

@[builtinTactic «exact»] def evalExact : Tactic := fun stx =>
  match stx with
  | `(tactic| exact $e) => closeMainUsing (fun type => elabTermEnsuringType e type)
  | _                   => throwUnsupportedSyntax

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
      discard <| Term.logUnassignedUsingErrorInfos naturalMVarIds
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
    setGoals (gs' ++ gs)

@[builtinTactic «refine»] def evalRefine : Tactic := fun stx =>
  match stx with
  | `(tactic| refine $e) => refineCore e `refine (allowNaturalHoles := false)
  | _                    => throwUnsupportedSyntax

@[builtinTactic «refine'»] def evalRefine' : Tactic := fun stx =>
  match stx with
  | `(tactic| refine' $e) => refineCore e `refine' (allowNaturalHoles := true)
  | _                     => throwUnsupportedSyntax

def evalApplyLikeTactic (tac : MVarId → Expr → MetaM (List MVarId)) (e : Syntax) : TacticM Unit := do
  let (g, gs) ← getMainGoal
  let gs' ← withMVarContext g do
    let decl ← getMVarDecl g
    let val  ← elabTerm e none true
    let gs'  ← tac g val
    Term.synthesizeSyntheticMVarsNoPostponing
    pure gs'
  setGoals (gs' ++ gs)

@[builtinTactic Lean.Parser.Tactic.apply] def evalApply : Tactic := fun stx =>
  match stx with
  | `(tactic| apply $e) => evalApplyLikeTactic Meta.apply e
  | _ => throwUnsupportedSyntax

@[builtinTactic Lean.Parser.Tactic.existsIntro] def evalExistsIntro : Tactic := fun stx =>
  match stx with
  | `(tactic| exists $e) => evalApplyLikeTactic (fun mvarId e => return [(← Meta.existsIntro mvarId e)]) e
  | _ => throwUnsupportedSyntax

@[builtinTactic Lean.Parser.Tactic.withReducible] def evalWithReducible : Tactic := fun stx =>
  withReducible <| evalTactic stx[1]

@[builtinTactic Lean.Parser.Tactic.withReducibleAndInstances] def evalWithReducibleAndInstances : Tactic := fun stx =>
  withReducibleAndInstances <| evalTactic stx[1]

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
        setGoals <| mvarId::others
        pure fvarId
      match userName? with
      | none          => intro `h false
      | some userName => intro userName true

@[builtinTactic Lean.Parser.Tactic.rename] def evalRename : Tactic := fun stx =>
  match stx with
  | `(tactic| rename $typeStx:term => $h:ident) => do
    let (mvarId, others) ← getMainGoal
    withMVarContext mvarId do
      let fvarId ← withoutModifyingState <| withNewMCtxDepth do
        let type ← elabTerm typeStx none (mayPostpone := true)
        let fvarId? ← (← getLCtx).findDeclRevM? fun localDecl => do
          if (← isDefEq type localDecl.type) then return localDecl.fvarId else return none
        match fvarId? with
        | none => throwError "failed to find a hypothesis with type{indentExpr type}"
        | some fvarId => return fvarId
      let lctxNew := (← getLCtx).setUserName fvarId h.getId
      let mvarNew ← mkFreshExprMVarAt lctxNew (← getLocalInstances) (← getMVarType mvarId) MetavarKind.syntheticOpaque (← getMVarTag mvarId)
      assignExprMVar mvarId mvarNew
      setGoals (mvarNew.mvarId! :: others)
  | _ => throwUnsupportedSyntax

/--
   Make sure `expectedType` does not contain free and metavariables.
   It applies zeta-reduction to eliminate let-free-vars.
-/
private def preprocessPropToDecide (expectedType : Expr) : TermElabM Expr := do
  let mut expectedType ← instantiateMVars expectedType
  if expectedType.hasFVar then
    expectedType ← zetaReduce expectedType
  if expectedType.hasFVar || expectedType.hasMVar then
    throwError "expected type must not contain free or meta variables{indentExpr expectedType}"
  return expectedType

@[builtinTactic Lean.Parser.Tactic.decide] def evalDecide : Tactic := fun stx =>
  closeMainUsing fun expectedType => do
    let expectedType ← preprocessPropToDecide expectedType
    let d ← mkDecide expectedType
    let d ← instantiateMVars d
    let r ← withDefault <| whnf d
    unless r.isConstOf ``true do
      throwError "failed to reduce to 'true'{indentExpr r}"
    let s := d.appArg! -- get instance from `d`
    let rflPrf ← mkEqRefl (toExpr true)
    return mkApp3 (Lean.mkConst `ofDecideEqTrue) expectedType s rflPrf

private def mkNativeAuxDecl (baseName : Name) (type val : Expr) : TermElabM Name := do
  let auxName ← Term.mkAuxName baseName
  let decl := Declaration.defnDecl {
    name := auxName, levelParams := [], type := type, value := val,
    hints := ReducibilityHints.abbrev,
    safety := DefinitionSafety.safe
  }
  addDecl decl
  compileDecl decl
  pure auxName

@[builtinTactic Lean.Parser.Tactic.nativeDecide] def evalNativeDecide : Tactic := fun stx =>
  closeMainUsing fun expectedType => do
    let expectedType ← preprocessPropToDecide expectedType
    let d ← mkDecide expectedType
    let auxDeclName ← mkNativeAuxDecl `_nativeDecide (Lean.mkConst `Bool) d
    let rflPrf ← mkEqRefl (toExpr true)
    let s := d.appArg! -- get instance from `d`
    return mkApp3 (Lean.mkConst `ofDecideEqTrue) expectedType s <| mkApp3 (Lean.mkConst `Lean.ofReduceBool) (Lean.mkConst auxDeclName) (toExpr true) rflPrf

end Lean.Elab.Tactic
