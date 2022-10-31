/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Compiler.LCNF.MonoTypes
import Lean.Compiler.LCNF.InferType


set_option warningAsError false
#exit

namespace Lean.Compiler.LCNF

structure ToMonoM.State where
  typeParams : FVarIdSet := {}

abbrev ToMonoM := StateRefT ToMonoM.State CompilerM

def Param.toMono (param : Param) : ToMonoM Param := do
  if isTypeFormerType param.type then
    modify fun { typeParams, .. } => { typeParams := typeParams.insert param.fvarId }
  param.update (← toMonoType param.type)

def isTrivialConstructorApp? (e : Expr) : ToMonoM (Option Expr) := do
  let some ctorInfo := e.isConstructorApp? (← getEnv) | return none
  let some info ← hasTrivialStructure? ctorInfo.induct | return none
  assert! ctorInfo.numParams + info.fieldIdx < e.getAppNumArgs
  return e.getArg! (ctorInfo.numParams + info.fieldIdx)

def fvarToMono (e : Expr) : ToMonoM Expr := do
  if (← get).typeParams.contains e.fvarId! then
    return erasedExpr
  else
    return e

def argToMono (arg : Expr) : ToMonoM Expr := do
  if arg.isFVar then
    fvarToMono arg
  else
    return erasedExpr

def ctorAppToMono (ctorInfo : ConstructorVal) (args : Array Expr) : ToMonoM Expr := do
  let argsNew ← args[:ctorInfo.numParams].toArray.mapM fun param => do
    -- We only preserve constructor parameters that are types
    if isTypeFormerType (← inferType param) then
      toMonoType param
    else
      return erasedExpr
  let argsNew := argsNew ++ (← args[ctorInfo.numParams:].toArray.mapM argToMono)
  return mkAppN (mkConst ctorInfo.name) argsNew

partial def _root_.Lean.Expr.toMono (e : Expr) : ToMonoM Expr := do
  match e with
  | .fvar .. => fvarToMono e
  | .lit .. => return e
  | .const declName _ => return mkConst declName
  | .sort .. => return erasedExpr
  | .mvar .. | .bvar .. | .letE .. => unreachable!
  | .mdata _ b => return e.updateMData! (← b.toMono)
  | .proj structName fieldIdx b =>
    if let some info ← hasTrivialStructure? structName then
      if info.fieldIdx == fieldIdx then
        b.toMono
      else
        return erasedExpr
    else
      return e.updateProj! (← b.toMono)
  | .forallE .. | .lam .. => return erasedExpr
  | .app .. =>
    if e.isAppOf ``Decidable.isTrue then
      return mkConst ``Bool.true
    else if e.isAppOf ``Decidable.isFalse then
      return mkConst ``Bool.false
    else if let some arg ← isTrivialConstructorApp? e then
      arg.toMono
    else if let some ctorInfo := e.isConstructorApp? (← getEnv) then
      ctorAppToMono ctorInfo e.getAppArgs
    else
      let f := e.getAppFn
      let args := e.getAppArgs
      let args ← args.mapM argToMono
      return mkAppN (← f.toMono) args

def LetDecl.toMono (decl : LetDecl) : ToMonoM LetDecl := do
  let type ← toMonoType decl.type
  let value ← decl.value.toMono
  decl.update type value

mutual

partial def FunDeclCore.toMono (decl : FunDecl) : ToMonoM FunDecl := do
  let type ← toMonoType decl.type
  let params ← decl.params.mapM (·.toMono)
  let value ← decl.value.toMono
  decl.update type params value

/-- Convert `cases` `Decidable` => `Bool` -/
partial def decToMono (c : Cases) (_ : c.typeName == ``Decidable) : ToMonoM Code := do
  let resultType ← toMonoType c.resultType
  let alts ← c.alts.mapM fun alt => do
    match alt with
    | .default k => return alt.updateCode (← k.toMono)
    | .alt ctorName ps k =>
      eraseParams ps
      let ctorName := if ctorName == ``Decidable.isTrue then ``Bool.true else ``Bool.false
      return .alt ctorName #[] (← k.toMono)
  return .cases { c with resultType, alts, typeName := ``Bool }

/-- Eliminate `cases` for trivial structure. See `hasTrivialStructure?` -/
partial def trivialStructToMono (info : TrivialStructureInfo) (c : Cases) : ToMonoM Code := do
  assert! c.alts.size == 1
  let .alt ctorName ps k := c.alts[0]! | unreachable!
  assert! ctorName == info.ctorName
  assert! info.fieldIdx < ps.size
  let p := ps[info.fieldIdx]!
  eraseParams ps
  /- We reuse `p`s `fvarId` to avoid substitution -/
  let decl := { fvarId := p.fvarId, binderName := p.binderName, type := (← toMonoType p.type), value := .fvar c.discr }
  modifyLCtx fun lctx => lctx.addLetDecl decl
  let k ← k.toMono
  return .let decl k

partial def Code.toMono (code : Code) : ToMonoM Code := do
  match code with
  | .let decl k => return code.updateLet! (← decl.toMono) (← k.toMono)
  | .fun decl k | .jp decl k => return code.updateFun! (← decl.toMono) (← k.toMono)
  | .unreach type => return .unreach (← toMonoType type)
  | .return .. | .jmp .. => return code
  | .cases c =>
    if h : c.typeName == ``Decidable then
      decToMono c h
    else if let some info ← hasTrivialStructure? c.typeName then
      trivialStructToMono info c
    else
      -- TODO: `casesOn` `[implemented_by]` support
      let type ← toMonoType c.resultType
      let alts ← c.alts.mapM fun alt =>
        match alt with
        | .default k => return alt.updateCode (← k.toMono)
        | .alt _ ps k => return alt.updateAlt! (← ps.mapM (·.toMono)) (← k.toMono)
      return code.updateCases! type c.discr alts

end

def Decl.toMono (decl : Decl) : CompilerM Decl := do
  go |>.run' {}
where
  go : ToMonoM Decl := do
    let type ← toMonoType decl.type
    let params ← decl.params.mapM (·.toMono)
    let value ← decl.value.toMono
    let decl := { decl with type, params, value, levelParams := [] }
    decl.saveMono
    return decl

def toMono : Pass where
  name     := `toMono
  run      := fun decls => do
    let decls ← decls.filterM fun decl => do
      if hasLocalInst decl.type then
        /-
        Declaration is a "template" for the code specialization pass.
        So, we should delete it before going to next phase.
        -/
        decl.erase
        return false
      else
        return true
    decls.mapM (·.toMono)
  phase    := .base
  phaseOut := .mono

builtin_initialize
  registerTraceClass `Compiler.toMono (inherited := true)

end Lean.Compiler.LCNF
