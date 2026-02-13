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

abbrev InternalizeM (pu : Purity) := StateRefT (FVarSubst pu) CompilerM

/--
The `InternalizeM` monad is a translator. It "translates" the free variables
in the input expressions and `Code`, into new fresh free variables in the
local context.
-/
instance : MonadFVarSubst (InternalizeM pu) pu true where
  getSubst := get

instance : MonadFVarSubstState (InternalizeM pu) pu where
  modifySubst := modify

private def mkNewFVarId (fvarId : FVarId) : InternalizeM pu FVarId := do
  let fvarId' ← Lean.mkFreshFVarId
  addFVarSubst fvarId fvarId'
  return fvarId'

private partial def internalizeExpr (e : Expr) : InternalizeM pu Expr :=
  go e
where
  goApp (e : Expr) : InternalizeM pu Expr := do
    match e with
    | .app f a => return e.updateApp! (← goApp f) (← go a)
    | _ => go e

  go (e : Expr) : InternalizeM pu Expr := do
    if e.hasFVar then
      match e with
      | .fvar fvarId =>
        match (← get)[fvarId]? with
        | some (.fvar fvarId') =>
          -- In LCNF, types can't depend on let-bound fvars.
          if (← findParam? (pu := pu) fvarId').isSome then
            return .fvar fvarId'
          else
            return anyExpr
        | some .erased => return erasedExpr
        | some (.type e _) | none => return e
      | .lit .. | .const .. | .sort .. | .mvar .. | .bvar .. => return e
      | .app f a => return e.updateApp! (← goApp f) (← go a) |>.headBeta
      | .mdata _ b => return e.updateMData! (← go b)
      | .proj _ _ b => return e.updateProj! (← go b)
      | .forallE _ d b _ => return e.updateForallE! (← go d) (← go b)
      | .lam _ d b _ => return e.updateLambdaE! (← go d) (← go b)
      | .letE .. => unreachable!
    else
      return e

def internalizeParam (p : Param pu) : InternalizeM pu (Param pu) := do
  let binderName ← refreshBinderName p.binderName
  let type ← internalizeExpr p.type
  let fvarId ← mkNewFVarId p.fvarId
  let p := { p with binderName, fvarId, type }
  modifyLCtx fun lctx => lctx.addParam p
  return p

def internalizeArg (arg : Arg pu) : InternalizeM pu (Arg pu) := do
  match arg with
  | .fvar fvarId =>
    match (← get)[fvarId]? with
    | some arg'@(.fvar _) => return arg'
    | some arg'@.erased | some arg'@(.type _ _) => return arg'
    | none => return arg
  | .type e _ => return arg.updateType! (← internalizeExpr e)
  | .erased => return arg

def internalizeArgs (args : Array (Arg pu)) : InternalizeM pu (Array (Arg pu)) :=
  args.mapM internalizeArg

private partial def internalizeLetValue (e : LetValue pu) : InternalizeM pu (LetValue pu) := do
  match e with
  | .erased | .lit .. => return e
  | .proj _ _ fvarId _ | .oproj _ fvarId _ | .sproj _ _ fvarId _ | .uproj _ fvarId _ =>
    match (← normFVar fvarId) with
    | .fvar fvarId' => return e.updateProj! fvarId'
    | .erased => return .erased
  | .const _ _ args _ | .fap _ args _ | .pap _ args _ | .ctor _ args _ =>
    return e.updateArgs! (← internalizeArgs args)
  | .fvar fvarId args => match (← normFVar fvarId) with
    | .fvar fvarId' => return e.updateFVar! fvarId' (← internalizeArgs args)
    | .erased => return .erased
  | .reset n fvarId _ =>
    match (← normFVar fvarId) with
    | .fvar fvarId' => return e.updateReset! n fvarId'
    | .erased => return .erased
  | .reuse fvarId info updateHeader args _ =>
    match (← normFVar fvarId) with
    | .fvar fvarId' => return e.updateReuse! fvarId' info updateHeader (← internalizeArgs args)
    | .erased => return .erased
  | .unbox fvarId _ =>
    match (← normFVar fvarId) with
    | .fvar fvarId' => return e.updateUnbox! fvarId'
    | .erased => return .erased
  | .box ty fvarId _ =>
    match (← normFVar fvarId) with
    | .fvar fvarId' => return e.updateBox! ty fvarId'
    | .erased => return .erased

def internalizeLetDecl (decl : LetDecl pu) : InternalizeM pu (LetDecl pu) := do
  let binderName ← refreshBinderName decl.binderName
  let type ← internalizeExpr decl.type
  let value ← internalizeLetValue decl.value
  let fvarId ← mkNewFVarId decl.fvarId
  let decl := { decl with binderName, fvarId, type, value }
  modifyLCtx fun lctx => lctx.addLetDecl decl
  return decl

mutual

partial def internalizeFunDecl (decl : FunDecl pu) : InternalizeM pu (FunDecl pu) := do
  let type ← internalizeExpr decl.type
  let binderName ← refreshBinderName decl.binderName
  let params ← decl.params.mapM internalizeParam
  let value ← internalizeCode decl.value
  let fvarId ← mkNewFVarId decl.fvarId
  let decl := ⟨fvarId, binderName, params, type, value⟩
  modifyLCtx fun lctx => lctx.addFunDecl decl
  return decl

partial def internalizeCode (code : Code pu) : InternalizeM pu (Code pu) := do
  match code with
  | .let decl k => return .let (← internalizeLetDecl decl) (← internalizeCode k)
  | .fun decl k _ => return .fun (← internalizeFunDecl decl) (← internalizeCode k)
  | .jp decl k => return .jp (← internalizeFunDecl decl) (← internalizeCode k)
  | .return fvarId => withNormFVarResult (← normFVar fvarId) fun fvarId => return .return fvarId
  | .jmp fvarId args => withNormFVarResult (← normFVar fvarId) fun fvarId => return .jmp fvarId (← internalizeArgs args)
  | .unreach type => return .unreach (← internalizeExpr type)
  | .cases c =>
    withNormFVarResult (← normFVar c.discr) fun discr => do
      let resultType ← internalizeExpr c.resultType
      let alts ← c.alts.mapM fun
        | .alt ctorName params k _ => return .alt ctorName (← params.mapM internalizeParam) (← internalizeCode k)
        | .default k => return .default (← internalizeCode k)
        | .ctorAlt i k _ => return .ctorAlt i (← internalizeCode k)
      return .cases ⟨c.typeName, resultType, discr, alts⟩
  | .sset fvarId i offset y ty k _ =>
    withNormFVarResult (← normFVar fvarId) fun fvarId => do
    withNormFVarResult (← normFVar y) fun y => do
      return .sset fvarId i offset y (← internalizeExpr ty) (← internalizeCode k)
  | .uset fvarId offset y k _ =>
    withNormFVarResult (← normFVar fvarId) fun fvarId => do
    withNormFVarResult (← normFVar y) fun y => do
      return .uset fvarId offset y (← internalizeCode k)

end

partial def internalizeCodeDecl (decl : CodeDecl pu) : InternalizeM pu (CodeDecl pu) := do
  match decl with
  | .let decl => return .let (← internalizeLetDecl decl)
  | .fun decl _ => return .fun (← internalizeFunDecl decl)
  | .jp decl => return .jp (← internalizeFunDecl decl)
  | .uset var i y _ =>
    -- Something weird should be happening if these become erased...
    let .fvar var ← normFVar var | unreachable!
    let .fvar y ← normFVar y | unreachable!
    return .uset var i y
  | .sset var i offset y ty _ =>
    let .fvar var ← normFVar var | unreachable!
    let .fvar y ← normFVar y | unreachable!
    let ty ← normExpr ty
    return .sset var i offset y ty


end Internalize

/--
Refresh free variables ids in `code`, and store their declarations in the local context.
-/
partial def Code.internalize (code : Code pu) (s : FVarSubst pu := {}) : CompilerM (Code pu) :=
  Internalize.internalizeCode code |>.run' s

open Internalize in
def Decl.internalize (decl : Decl pu) (s : FVarSubst pu := {}): CompilerM (Decl pu) :=
  go decl |>.run' s
where
  go (decl : Decl pu) : InternalizeM pu (Decl pu) := do
    let type ← internalizeExpr decl.type
    let params ← decl.params.mapM internalizeParam
    let value ← decl.value.mapCodeM internalizeCode
    return { decl with type, params, value }

/--
Create a fresh local context and internalize the given decls.
-/
def cleanup (decl : Array (Decl pu)) : CompilerM (Array (Decl pu)) := do
  modify fun _ => {}
  decl.mapM fun decl => do
    modify fun s => { s with nextIdx := 1 }
    decl.internalize

def normalizeFVarIds (decl : Decl pu) : CoreM (Decl pu) := do
  let ngenSaved ← getNGen
  setNGen {}
  try
    CompilerM.run <| decl.internalize
  finally
    setNGen ngenSaved

end Lean.Compiler.LCNF
