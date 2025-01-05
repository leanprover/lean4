/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.AbstractNestedProofs
import Lean.Meta.Transform
import Lean.Meta.Tactic.Util
import Lean.Meta.Tactic.Clear

namespace Lean.Meta.Grind
/--
Throws an exception if target of the given goal contains metavariables.
-/
def _root_.Lean.MVarId.ensureNoMVar (mvarId : MVarId) : MetaM Unit := do
  let type ← instantiateMVars (← mvarId.getType)
  if type.hasExprMVar then
    throwTacticEx `grind mvarId "goal contains metavariables"

/--
Throws an exception if target is not a proposition.
-/
def _root_.Lean.MVarId.ensureProp (mvarId : MVarId) : MetaM Unit := do
  let type ← mvarId.getType
  unless (← isProp type) do
    throwTacticEx `grind mvarId "goal is not a proposition"

def _root_.Lean.MVarId.transformTarget (mvarId : MVarId) (f : Expr → MetaM Expr) : MetaM MVarId := mvarId.withContext do
  mvarId.checkNotAssigned `grind
  let tag ← mvarId.getTag
  let type ← mvarId.getType
  let typeNew ← f type
  let mvarNew ← mkFreshExprSyntheticOpaqueMVar typeNew tag
  mvarId.assign mvarNew
  return mvarNew.mvarId!

/--
Unfolds all `reducible` declarations occurring in `e`.
-/
def unfoldReducible (e : Expr) : MetaM Expr :=
  let pre (e : Expr) : MetaM TransformStep := do
    let .const declName _ := e.getAppFn | return .continue
    unless (← isReducible declName) do return .continue
    let some v ← unfoldDefinition? e | return .continue
    return .visit v
  Core.transform e (pre := pre)

/--
Unfolds all `reducible` declarations occurring in the goal's target.
-/
def _root_.Lean.MVarId.unfoldReducible (mvarId : MVarId) : MetaM MVarId :=
  mvarId.transformTarget Grind.unfoldReducible

/--
Abstracts nested proofs occurring in the goal's target.
-/
def _root_.Lean.MVarId.abstractNestedProofs (mvarId : MVarId) (mainDeclName : Name) : MetaM MVarId :=
  mvarId.transformTarget (Lean.Meta.abstractNestedProofs mainDeclName)

/--
Beta-reduces the goal's target.
-/
def _root_.Lean.MVarId.betaReduce (mvarId : MVarId) : MetaM MVarId :=
  mvarId.transformTarget (Core.betaReduce ·)

/--
If the target is not `False`, applies `byContradiction`.
-/
def _root_.Lean.MVarId.byContra? (mvarId : MVarId) : MetaM (Option MVarId) := mvarId.withContext do
  mvarId.checkNotAssigned `grind.by_contra
  let target ← mvarId.getType
  if target.isFalse then return none
  let targetNew ← mkArrow (mkNot target) (mkConst ``False)
  let tag ← mvarId.getTag
  let mvarNew ← mkFreshExprSyntheticOpaqueMVar targetNew tag
  mvarId.assign <| mkApp2 (mkConst ``Classical.byContradiction) target mvarNew
  return mvarNew.mvarId!

/--
Clears auxiliary decls used to encode recursive declarations.
`grind` eliminates them to ensure they are not accidentally used by its proof automation.
-/
def _root_.Lean.MVarId.clearAuxDecls (mvarId : MVarId) : MetaM MVarId := mvarId.withContext do
  mvarId.checkNotAssigned `grind.clear_aux_decls
  let mut toClear := []
  for localDecl in (← getLCtx) do
    if localDecl.isAuxDecl then
      toClear := localDecl.fvarId :: toClear
  if toClear.isEmpty then
    return mvarId
  let mut mvarId := mvarId
  for fvarId in toClear do
    try
      mvarId ← mvarId.clear fvarId
    catch _ =>
      throwTacticEx `grind.clear_aux_decls mvarId "failed to clear local auxiliary declaration"
  return mvarId

/--
In the `grind` tactic, during `Expr` internalization, we don't expect to find `Expr.mdata`.
This function ensures `Expr.mdata` is not found during internalization.
Recall that we do not internalize `Expr.lam` children.
Recall that we still have to process `Expr.forallE` because of `ForallProp.lean`.
Moreover, we may not want to reduce `p → q` to `¬p ∨ q` when `(p q : Prop)`.
-/
def eraseIrrelevantMData (e : Expr) : CoreM Expr := do
  let pre (e : Expr) := do
    match e with
    | .letE .. | .lam .. => return .done e
    | .mdata _ e => return .continue e
    | _ => return .continue e
  Core.transform e (pre := pre)

/--
Converts nested `Expr.proj`s into projection applications if possible.
-/
def foldProjs (e : Expr) : MetaM Expr := do
  let post (e : Expr) := do
    let .proj structName idx s := e | return .done e
    let some info := getStructureInfo? (← getEnv) structName |
      trace[grind.issues] "found `Expr.proj` but `{structName}` is not marked as structure{indentExpr e}"
      return .done e
    if h : idx < info.fieldNames.size then
      let fieldName := info.fieldNames[idx]
      return .done (← mkProjection s fieldName)
    else
      trace[grind.issues] "found `Expr.proj` with invalid field index `{idx}`{indentExpr e}"
      return .done e
  Meta.transform e (post := post)

/--
Normalizes universe levels in constants and sorts.
-/
def normalizeLevels (e : Expr) : CoreM Expr := do
  let pre (e : Expr) := do
    match e with
    | .sort u => return .done <| e.updateSort! u.normalize
    | .const _ us => return .done <| e.updateConst! (us.map Level.normalize)
    | _ => return .continue
  Core.transform e (pre := pre)

/--
Normalizes the given expression using the `grind` simplification theorems and simprocs.
This function is used for normalzing E-matching patterns. Note that it does not return a proof.
-/
@[extern "lean_grind_normalize"] -- forward definition
opaque normalize (e : Expr) : MetaM Expr

end Lean.Meta.Grind
