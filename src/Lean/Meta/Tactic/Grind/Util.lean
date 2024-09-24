/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.AbstractNestedProofs
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
Unfold all `reducible` declarations occurring in `e`.
-/
def unfoldReducible (e : Expr) : MetaM Expr :=
  let pre (e : Expr) : MetaM TransformStep := do
    let .const declName _ := e.getAppFn | return .continue
    unless (← isReducible declName) do return .continue
    let some v ← unfoldDefinition? e | return .continue
    return .visit v
  Core.transform e (pre := pre)

/--
Unfold all `reducible` declarations occurring in the goal's target.
-/
def _root_.Lean.MVarId.unfoldReducible (mvarId : MVarId) : MetaM MVarId :=
  mvarId.transformTarget Grind.unfoldReducible

/--
Abstract nested proofs occurring in the goal's target.
-/
def _root_.Lean.MVarId.abstractNestedProofs (mvarId : MVarId) (mainDeclName : Name) : MetaM MVarId :=
  mvarId.transformTarget (Lean.Meta.abstractNestedProofs mainDeclName)

/--
Beta-reduce the goal's target.
-/
def _root_.Lean.MVarId.betaReduce (mvarId : MVarId) : MetaM MVarId :=
  mvarId.transformTarget (Core.betaReduce ·)

/--
If the target is not `False`, apply `byContradiction`.
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
Clear auxiliary decls used to encode recursive declarations.
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

end Lean.Meta.Grind
