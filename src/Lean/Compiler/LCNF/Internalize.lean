/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Compiler.LCNF.Bind

public section

namespace Lean.Compiler.LCNF

private def refreshBinderName (binderName : Name) : CompilerM Name := do
  match binderName with
  | .num p _ =>
    let r := .num p (← get).nextIdx
    modify fun s => { s with nextIdx := s.nextIdx + 1 }
    return r
  | _ => return binderName

namespace Internalize

abbrev InternalizeM := StateRefT FVarSubst CompilerM

/--
The `InternalizeM` monad is a translator. It "translates" the free variables
in the input expressions and `Code`, into new fresh free variables in the
local context.
-/
instance : MonadFVarSubst InternalizeM true where
  getSubst := get

instance : MonadFVarSubstState InternalizeM where
  modifySubst := modify

private def mkNewFVarId (fvarId : FVarId) : InternalizeM FVarId := do
  let fvarId' ← Lean.mkFreshFVarId
  addFVarSubst fvarId fvarId'
  return fvarId'

private partial def internalizeExpr (e : Expr) : InternalizeM Expr :=
  go e
where
  goApp (e : Expr) : InternalizeM Expr := do
    match e with
    | .app f a => return e.updateApp! (← goApp f) (← go a)
    | _ => go e

  go (e : Expr) : InternalizeM Expr := do
    if e.hasFVar then
      match e with
      | .fvar fvarId => match (← get)[fvarId]? with
        | some (.fvar fvarId') =>
          -- In LCNF, types can't depend on let-bound fvars.
          if (← findParam? fvarId').isSome then
            return .fvar fvarId'
          else
            return anyExpr
        | some .erased => return erasedExpr
        | some (.type e) | none => return e
      | .lit .. | .const .. | .sort .. | .mvar .. | .bvar .. => return e
      | .app f a => return e.updateApp! (← goApp f) (← go a) |>.headBeta
      | .mdata _ b => return e.updateMData! (← go b)
      | .proj _ _ b => return e.updateProj! (← go b)
      | .forallE _ d b _ => return e.updateForallE! (← go d) (← go b)
      | .lam _ d b _ => return e.updateLambdaE! (← go d) (← go b)
      | .letE .. => unreachable!
    else
      return e

def internalizeParam (p : Param) : InternalizeM Param := do
  let binderName ← refreshBinderName p.binderName
  let type ← internalizeExpr p.type
  let fvarId ← mkNewFVarId p.fvarId
  let p := { p with binderName, fvarId, type }
  modifyLCtx fun lctx => lctx.addParam p
  return p

def internalizeArg (arg : Arg) : InternalizeM Arg := do
  match arg with
  | .fvar fvarId =>
    match (← get)[fvarId]? with
    | some arg'@(.fvar _) => return arg'
    | some arg'@.erased | some arg'@(.type _) => return arg'
    | none => return arg
  | .type e => return arg.updateType! (← internalizeExpr e)
  | .erased => return arg

def internalizeArgs (args : Array Arg) : InternalizeM (Array Arg) :=
  args.mapM internalizeArg

private partial def internalizeLetValue (e : LetValue) : InternalizeM LetValue := do
  match e with
  | .erased | .lit .. => return e
  | .proj _ _ fvarId => match (← normFVar fvarId) with
    | .fvar fvarId' => return e.updateProj! fvarId'
    | .erased => return .erased
  | .const _ _ args => return e.updateArgs! (← internalizeArgs args)
  | .fvar fvarId args => match (← normFVar fvarId) with
    | .fvar fvarId' => return e.updateFVar! fvarId' (← internalizeArgs args)
    | .erased => return .erased

def internalizeLetDecl (decl : LetDecl) : InternalizeM LetDecl := do
  let binderName ← refreshBinderName decl.binderName
  let type ← internalizeExpr decl.type
  let value ← internalizeLetValue decl.value
  let fvarId ← mkNewFVarId decl.fvarId
  let decl := { decl with binderName, fvarId, type, value }
  modifyLCtx fun lctx => lctx.addLetDecl decl
  return decl

mutual

partial def internalizeFunDecl (decl : FunDecl) : InternalizeM FunDecl := do
  let type ← internalizeExpr decl.type
  let binderName ← refreshBinderName decl.binderName
  let params ← decl.params.mapM internalizeParam
  let value ← internalizeCode decl.value
  let fvarId ← mkNewFVarId decl.fvarId
  let decl := ⟨fvarId, binderName, params, type, value⟩
  modifyLCtx fun lctx => lctx.addFunDecl decl
  return decl

partial def internalizeCode (code : Code) : InternalizeM Code := do
  match code with
  | .let decl k => return .let (← internalizeLetDecl decl) (← internalizeCode k)
  | .fun decl k => return .fun (← internalizeFunDecl decl) (← internalizeCode k)
  | .jp decl k => return .jp (← internalizeFunDecl decl) (← internalizeCode k)
  | .return fvarId => withNormFVarResult (← normFVar fvarId) fun fvarId => return .return fvarId
  | .jmp fvarId args => withNormFVarResult (← normFVar fvarId) fun fvarId => return .jmp fvarId (← internalizeArgs args)
  | .unreach type => return .unreach (← internalizeExpr type)
  | .cases c =>
    withNormFVarResult (← normFVar c.discr) fun discr => do
      let resultType ← internalizeExpr c.resultType
      let internalizeAltCode (k : Code) : InternalizeM Code :=
        internalizeCode k
      let alts ← c.alts.mapM fun
        | .alt ctorName params k => return .alt ctorName (← params.mapM internalizeParam) (← internalizeAltCode k)
        | .default k => return .default (← internalizeAltCode k)
      return .cases ⟨c.typeName, resultType, discr, alts⟩

end

partial def internalizeCodeDecl (decl : CodeDecl) : InternalizeM CodeDecl := do
  match decl with
  | .let decl => return .let (← internalizeLetDecl decl)
  | .fun decl => return .fun (← internalizeFunDecl decl)
  | .jp decl => return .jp (← internalizeFunDecl decl)

end Internalize

/--
Refresh free variables ids in `code`, and store their declarations in the local context.
-/
partial def Code.internalize (code : Code) (s : FVarSubst := {}) : CompilerM Code :=
  Internalize.internalizeCode code |>.run' s

open Internalize in
def Decl.internalize (decl : Decl) (s : FVarSubst := {}): CompilerM Decl :=
  go decl |>.run' s
where
  go (decl : Decl) : InternalizeM Decl := do
    let type ← internalizeExpr decl.type
    let params ← decl.params.mapM internalizeParam
    let value ← decl.value.mapCodeM internalizeCode
    return { decl with type, params, value }

/--
Create a fresh local context and internalize the given decls.
-/
def cleanup (decl : Array Decl) : CompilerM (Array Decl) := do
  modify fun _ => {}
  decl.mapM fun decl => do
    modify fun s => { s with nextIdx := 1 }
    decl.internalize

def normalizeFVarIds (decl : Decl) : CoreM Decl := do
  let ngenSaved ← getNGen
  setNGen {}
  try
    CompilerM.run <| decl.internalize
  finally
    setNGen ngenSaved

end Lean.Compiler.LCNF
