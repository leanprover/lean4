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

@[inline] def modifyLCtx (f : LCtx → LCtx) : CompilerM Unit := do
   modify fun s => { s with lctx := f s.lctx }

namespace Internalize

structure State where
  fvarIdMap : Std.HashMap FVarId FVarId := {}
  deriving Inhabited

abbrev M := StateRefT State CompilerM

private def translateFVarIdCore (s : State) (fvarId : FVarId) : FVarId :=
  match s.fvarIdMap.find? fvarId with
  | some fvarId' => fvarId'
  | none => fvarId

private partial def translateCore (s : State) (e : Expr) : Expr :=
  go e
where
  go (e : Expr) : Expr :=
    match e with
    | .fvar fvarId => .fvar (translateFVarIdCore s fvarId)
    | .lit .. | .const .. | .sort .. | .mvar .. | .bvar .. => e
    | .app .. => mkAppN (go e.getAppFn) (e.getAppArgs.map go)
    | .mdata k b => .mdata k (go b)
    | .proj s i b => .proj s i (go b)
    | .forallE n d b bi => .forallE n (go d) (go b) bi
    | .lam n d b bi => .lam n (go d) (go b) bi
    | .letE n t v b nd => .letE n (go t) (go v) (go b) nd

@[inline] private def translateFVarId (fvarId : FVarId) : M FVarId :=
  return translateFVarIdCore (← get) fvarId

@[inline] private def translate (e : Expr) : M Expr :=
  return translateCore (← get) e

private def mkNewFVarId (fvarId : FVarId) : M FVarId := do
  let fvarId' ← Lean.mkFreshFVarId
  modify fun s => { s with fvarIdMap := s.fvarIdMap.insert fvarId fvarId' }
  return fvarId'

private def addParam (p : Param) : M Param := do
  let type ← translate p.type
  let fvarId ← mkNewFVarId p.fvarId
  modifyLCtx fun lctx => lctx.addLocalDecl fvarId p.binderName type
  return { p with fvarId, type }

end Internalize

open Internalize in
/--
Refresh free variables ids in `code`, and store their declarations in the local context.
-/
partial def internalize (code : Code) : CompilerM Code :=
  go code |>.run' {}
where
  goFunDecl (decl : FunDecl) : M FunDecl := do
    let type ← translate decl.type
    let params ← decl.params.mapM addParam
    let value ← go decl.value
    let fvarId ← mkNewFVarId decl.fvarId
    let decl := { decl with fvarId, params, type, value }
    modifyLCtx fun lctx => lctx.addFunDecl decl
    return decl

  go (code : Code) : M Code := do
    match code with
    | .let decl k =>
      let type ← translate decl.type
      let value ← translate decl.value
      let fvarId ← mkNewFVarId decl.fvarId
      modifyLCtx fun lctx => lctx.addLetDecl fvarId decl.binderName type value
      let k ← go k
      return .let { decl with fvarId, type, value } k
    | .fun decl k =>
      return .fun (← goFunDecl decl) (← go k)
    | .jp decl k =>
      return .jp (← goFunDecl decl) (← go k)
    | .return fvarId => return .return (← translateFVarId fvarId)
    | .jmp fvarId args => return .jmp (← translateFVarId fvarId) (← args.mapM translate)
    | .unreach type => return .unreach (← translate type)
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

def mkFreshBinderName (binderName := `_x): CompilerM Name := do
  let declName := .num binderName (← get).nextIdx
  modify fun s => { s with nextIdx := s.nextIdx + 1 }
  return declName

def mkFreshJpName : CompilerM Name := do
  mkFreshBinderName `_jp

def mkAuxParam (type : Expr) : CompilerM Param := do
  mkParam (← mkFreshBinderName `_y) type

end Lean.Compiler.LCNF
