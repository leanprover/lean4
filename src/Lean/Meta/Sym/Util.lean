/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.SymM
public import Lean.Meta.Transform
import Init.Grind.Util
import Lean.Meta.WHNF
namespace Lean.Meta.Sym

/--
Returns `true` if `declName` is the name of a grind helper declaration that
should not be unfolded by `unfoldReducible`.
-/
def isGrindGadget (declName : Name) : Bool :=
  declName == ``Grind.EqMatch

/--
Auxiliary function for implementing `unfoldReducible` and `unfoldReducibleSimproc`.
Performs a single step.
-/
public def unfoldReducibleStep (e : Expr) : MetaM TransformStep := do
  let .const declName _ := e.getAppFn | return .continue
  unless (← isReducible declName) do return .continue
  if isGrindGadget declName then return .continue
  -- See comment at isUnfoldReducibleTarget.
  if (← getEnv).isProjectionFn declName then return .continue
  let some v ← unfoldDefinition? e | return .continue
  return .visit v

def isUnfoldReducibleTarget (e : Expr) : CoreM Bool := do
  let env ← getEnv
  return Option.isSome <| e.find? fun e => Id.run do
    let .const declName _ := e | return false
    if getReducibilityStatusCore env declName matches .reducible then
      -- Remark: it is wasteful to unfold projection functions since
      -- kernel projections are folded again in the `foldProjs` preprocessing step.
      return !isGrindGadget declName && !env.isProjectionFn declName
    else
      return false

/--
Unfolds all `reducible` declarations occurring in `e`.
This is meant as a preprocessing step. It does **not** guarantee maximally shared terms
-/
public def unfoldReducible (e : Expr) : MetaM Expr := do
  if !(← isUnfoldReducibleTarget e) then return e
  Meta.transform e (pre := unfoldReducibleStep)

/--
Instantiates metavariables, unfold reducible, and applies `shareCommon`.
-/
def preprocessExpr (e : Expr) : SymM Expr := do
  shareCommon (← unfoldReducible (← instantiateMVars e))

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

end Lean.Meta.Sym
