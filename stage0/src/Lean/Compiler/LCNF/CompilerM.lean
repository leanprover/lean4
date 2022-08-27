/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.CoreM
import Lean.Compiler.LCNF.Basic
import Lean.Compiler.LCNF.LCtx

namespace Lean.Compiler.LCNF

/--
The state managed by the `CompilerM` `Monad`.
-/
structure CompilerM.State where
  /--
  A `LocalContext` to store local declarations from let binders
  and other constructs in as we move through `Expr`s.
  -/
  lctx     : LCtx := {}
  /-- Next auxiliary variable suffix -/
  nextIdx : Nat := 1
deriving Inhabited

abbrev CompilerM := StateRefT CompilerM.State CoreM

instance : AddMessageContext CompilerM where
  addMessageContext msgData := do
    let env ← getEnv
    let lctx := (← get).lctx.toLocalContext
    let opts ← getOptions
    return MessageData.withContext { env, lctx, opts, mctx := {} } msgData

def getLocalDecl (fvarId : FVarId) : CompilerM LocalDecl := do
  let some decl := (← get).lctx.localDecls.find? fvarId | throwError "unknown free variable {fvarId.name}"
  return decl

def getFunDecl (fvarId : FVarId) : CompilerM FunDecl := do
  let some decl := (← get).lctx.funDecls.find? fvarId | throwError "unknown local function {fvarId.name}"
  return decl

@[inline] def modifyLCtx (f : LCtx → LCtx) : CompilerM Unit := do
   modify fun s => { s with lctx := f s.lctx }

def eraseFVar (fvarId : FVarId) : CompilerM Unit := do
  modifyLCtx fun lctx => lctx.erase fvarId

abbrev FVarSubst := Std.HashMap FVarId FVarId

def FVarSubst.applyToFVar (s : FVarSubst) (fvarId : FVarId) : FVarId :=
  match s.find? fvarId with
  | some fvarId' => fvarId'
  | none => fvarId

partial def FVarSubst.applyToExpr (s : FVarSubst) (e : Expr) : Expr :=
  go e
where
  go (e : Expr) : Expr :=
    if e.hasFVar then
      match e with
      | .fvar fvarId => .fvar (s.applyToFVar fvarId)
      | .lit .. | .const .. | .sort .. | .mvar .. | .bvar .. => e
      | .app f a => e.updateApp! (go f) (go a)
      | .mdata _ b => e.updateMData! (go b)
      | .proj _ _ b => e.updateProj! (go b)
      | .forallE _ d b _ => e.updateForallE! (go d) (go b)
      | .lam _ d b _ => e.updateLambdaE! (go d) (go b)
      | .letE _ t v b _ => e.updateLet! (go t) (go v) (go b)
    else
      e

namespace Internalize

abbrev M := StateRefT FVarSubst CompilerM

@[inline] private def translateFVarId (fvarId : FVarId) : M FVarId :=
  return (← get).applyToFVar fvarId

@[inline] private def translateExpr (e : Expr) : M Expr :=
  return (← get).applyToExpr e

private def mkNewFVarId (fvarId : FVarId) : M FVarId := do
  let fvarId' ← Lean.mkFreshFVarId
  modify fun s => s.insert fvarId fvarId'
  return fvarId'

private def addParam (p : Param) : M Param := do
  let type ← translateExpr p.type
  let fvarId ← mkNewFVarId p.fvarId
  modifyLCtx fun lctx => lctx.addLocalDecl fvarId p.binderName type
  return { p with fvarId, type }

end Internalize

open Internalize in
/--
Refresh free variables ids in `code`, and store their declarations in the local context.
-/
partial def Code.internalize (code : Code) : CompilerM Code :=
  go code |>.run' {}
where
  goFunDecl (decl : FunDecl) : M FunDecl := do
    let type ← translateExpr decl.type
    let params ← decl.params.mapM addParam
    let value ← go decl.value
    let fvarId ← mkNewFVarId decl.fvarId
    let decl := { decl with fvarId, params, type, value }
    modifyLCtx fun lctx => lctx.addFunDecl decl
    return decl

  go (code : Code) : M Code := do
    match code with
    | .let decl k =>
      let type ← translateExpr decl.type
      let value ← translateExpr decl.value
      let fvarId ← mkNewFVarId decl.fvarId
      modifyLCtx fun lctx => lctx.addLetDecl fvarId decl.binderName type value
      let k ← go k
      return .let { decl with fvarId, type, value } k
    | .fun decl k =>
      return .fun (← goFunDecl decl) (← go k)
    | .jp decl k =>
      return .jp (← goFunDecl decl) (← go k)
    | .return fvarId => return .return (← translateFVarId fvarId)
    | .jmp fvarId args => return .jmp (← translateFVarId fvarId) (← args.mapM translateExpr)
    | .unreach type => return .unreach (← translateExpr type)
    | .cases c =>
      let discr ← translateFVarId c.discr
      let alts ← c.alts.mapM fun
        | .alt ctorName params k => return .alt ctorName (← params.mapM addParam) (← go k)
        | .default k => return .default (← go k)
      return .cases { c with discr, alts }

/-!
Helper functions for creating LCNF local declarations.
-/

def mkParam (binderName : Name) (type : Expr) : CompilerM Param := do
  let fvarId ← mkFreshFVarId
  modifyLCtx fun lctx => lctx.addLocalDecl fvarId binderName type
  return { fvarId, binderName, type }

def mkLetDecl (binderName : Name) (type : Expr) (value : Expr) : CompilerM LetDecl := do
  let fvarId ← mkFreshFVarId
  modifyLCtx fun lctx => lctx.addLetDecl fvarId binderName type value
  return { fvarId, binderName, type, value }

def mkFunDecl (binderName : Name) (type : Expr) (params : Array Param) (value : Code) : CompilerM FunDecl := do
  let fvarId ← mkFreshFVarId
  let funDecl := { fvarId, binderName, type, params, value }
  modifyLCtx fun lctx => lctx.addFunDecl funDecl
  return funDecl

private unsafe def updateParamImp (p : Param) (type : Expr) : CompilerM Param := do
  if ptrEq type p.type then
    return p
  else
    let p := { p with type }
    modifyLCtx fun lctx => lctx.addLocalDecl p.fvarId p.binderName p.type
    return p

@[implementedBy updateParamImp] opaque updateParam (p : Param) (type : Expr) : CompilerM Param

private unsafe def updateLetDeclImp (decl : LetDecl) (type : Expr) (value : Expr) : CompilerM LetDecl := do
  if ptrEq type decl.type && ptrEq value decl.value then
    return decl
  else
    let decl := { decl with type, value }
    modifyLCtx fun lctx => lctx.addLetDecl decl.fvarId decl.binderName decl.type decl.value
    return decl

@[implementedBy updateLetDeclImp] opaque updateLetDecl (decl : LetDecl) (type : Expr) (value : Expr) : CompilerM LetDecl

def FVarSubst.applyToParam (s : FVarSubst) (p : Param) : CompilerM Param :=
  updateParam p (s.applyToExpr p.type)

def FVarSubst.applyToParams (s : FVarSubst) (ps : Array Param) : CompilerM (Array Param) :=
  ps.mapM s.applyToParam

def FVarSubst.applyToLetDecl (s : FVarSubst) (decl : LetDecl) : CompilerM LetDecl :=
  updateLetDecl decl (s.applyToExpr decl.type) (s.applyToExpr decl.value)

def mkFreshBinderName (binderName := `_x): CompilerM Name := do
  let declName := .num binderName (← get).nextIdx
  modify fun s => { s with nextIdx := s.nextIdx + 1 }
  return declName

def mkFreshJpName : CompilerM Name := do
  mkFreshBinderName `_jp

def mkAuxParam (type : Expr) : CompilerM Param := do
  mkParam (← mkFreshBinderName `_y) type

def CompilerM.run (x : CompilerM α) (s : State := {}) : CoreM α :=
  x |>.run' s

end Lean.Compiler.LCNF
