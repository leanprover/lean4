/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.SymM
public import Lean.Meta.Transform
import Lean.Util.ForEachExpr
namespace Lean.Meta.Sym

/--
Instantiates metavariables and applies `shareCommon`, which maintains the `SymM`
invariants enabled in the current configuration (see `Sym.Config`).
-/
public def preprocessExpr (e : Expr) : SymM Expr := do
  -- This function relies on `shareCommon` to unfold reducible constants, so the
  -- corresponding check must not have been disabled (e.g., via `withoutShareCommonChecks`).
  assert! (← getConfig).enforceUnfoldReducible
  shareCommon (← instantiateMVars e)

/--
Helper function that removes gaps, instantiate metavariables, and applies `shareCommon`.
Gaps are `none` cells at `lctx.decls`. In `SymM`, we assume these cells don't exist.
-/
def preprocessLCtx (lctx : LocalContext) : SymM LocalContext := do
  let auxDeclToFullName := lctx.auxDeclToFullName
  let mut fvarIdToDecl := {}
  let mut decls := {}
  let mut index := 0
  for decl in lctx do
    let decl ← match decl with
      | .cdecl _ fvarId userName type bi kind =>
        let type ← preprocessExpr type
        pure <| LocalDecl.cdecl index fvarId userName type bi kind
      | .ldecl _ fvarId userName type value nondep kind =>
        let type ← preprocessExpr type
        let value ← preprocessExpr value
        pure <| LocalDecl.ldecl index fvarId userName type value nondep kind
    index := index + 1
    decls := decls.push (some decl)
    fvarIdToDecl := fvarIdToDecl.insert decl.fvarId decl
  return { fvarIdToDecl, decls, auxDeclToFullName }

/--
Instantiates assigned metavariables, applies `shareCommon`, and eliminates holes (aka `none` cells)
in the local context.
-/
public def preprocessMVar (mvarId : MVarId) : SymM MVarId := do
  let mvarDecl ← mvarId.getDecl
  let lctx ← preprocessLCtx mvarDecl.lctx
  let type ← preprocessExpr mvarDecl.type
  let mvarNew ← mkFreshExprMVarAt lctx mvarDecl.localInstances type .syntheticOpaque mvarDecl.userName
  mvarId.assign mvarNew
  return mvarNew.mvarId!

/-- Debug helper: throws if any subexpression of `e` is not in the table of maximally shared terms. -/
public def _root_.Lean.Expr.checkMaxShared (e : Expr) (msg := "") : SymM Unit := do
  e.forEach fun e => do
    if let some prev := (← get).share.set.find? { expr := e } then
      unless isSameExpr prev.expr e do
        throwNotMaxShared e
    else
      throwNotMaxShared e
where
  throwNotMaxShared (e : Expr) : SymM Unit := do
    let msg := if msg == "" then msg else s!"[{msg}] "
    throwError "{msg}term is not in the maximally shared table{indentExpr e}"

/-- Debug helper: throws if any subexpression of the goal's target type is not in the table of maximally shared. -/
public def _root_.Lean.MVarId.checkMaxShared (mvarId : MVarId) (msg := "") : SymM Unit := do
  (← mvarId.getDecl).type.checkMaxShared msg

/-- Quick filter for checking whether we can skip `normalizeLevels`. -/
def levelsAlreadyNormalized (e : Expr) : Bool :=
  Option.isNone <| e.find? fun
    | .const _ us => us.any (! ·.isAlreadyNormalizedCheap)
    | .sort u => !u.isAlreadyNormalizedCheap
    | _ => false

/--
Normalizes universe levels in constants and sorts.
-/
public def normalizeLevels (e : Expr) : CoreM Expr := do
  if levelsAlreadyNormalized e then return e
  let pre (e : Expr) := do
    match e with
    | .sort u => return .done <| e.updateSort! u.normalize
    | .const _ us => return .done <| e.updateConst! (us.map Level.normalize)
    | _ => return .continue
  Core.transform e (pre := pre)

end Lean.Meta.Sym
