/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Compiler.LCNF.MonoTypes
import Lean.Compiler.LCNF.InferType

namespace Lean.Compiler.LCNF

structure ToMonoM.State where
  typeParams : FVarIdSet := {}

abbrev ToMonoM := StateRefT ToMonoM.State CompilerM

def Param.toMono (param : Param) : ToMonoM Param := do
  if isTypeFormerType param.type then
    modify fun { typeParams, .. } => { typeParams := typeParams.insert param.fvarId }
  param.update (← toMonoType param.type)

def isTrivialConstructorApp? (declName : Name) (args : Array Arg) : ToMonoM (Option LetValue) := do
  let some (.ctorInfo ctorInfo) := (← getEnv).find? declName | return none
  let some info ← hasTrivialStructure? ctorInfo.induct | return none
  return args[ctorInfo.numParams + info.fieldIdx]!.toLetValue

def argToMono (arg : Arg) : ToMonoM Arg := do
  match arg with
  | .erased | .type .. => return .erased
  | .fvar fvarId =>
    if (← get).typeParams.contains fvarId then
      return .erased
    else
      return arg

def ctorAppToMono (ctorInfo : ConstructorVal) (args : Array Arg) : ToMonoM LetValue := do
  let argsNew : Array Arg ← args[:ctorInfo.numParams].toArray.mapM fun arg => do
    -- We only preserve constructor parameters that are types
    match arg with
    | .type type => return .type (← toMonoType type)
    | .fvar .. | .erased => return .erased
  let argsNew := argsNew ++ (← args[ctorInfo.numParams:].toArray.mapM argToMono)
  return .const ctorInfo.name [] argsNew

partial def LetValue.toMono (e : LetValue) : ToMonoM LetValue := do
  match e with
  | .erased | .value .. => return e
  | .const declName _ args =>
    if declName == ``Decidable.isTrue then
      return .const ``Bool.true [] #[]
    else if declName == ``Decidable.isFalse then
      return .const ``Bool.false [] #[]
    else if let some e' ← isTrivialConstructorApp? declName args then
      e'.toMono
    else if let some (.ctorInfo ctorInfo) := (← getEnv).find? declName then
      ctorAppToMono ctorInfo args
    else
      return .const declName [] (← args.mapM argToMono)
  | .fvar fvarId args =>
    if (← get).typeParams.contains fvarId then
      return .erased
    else
      return .fvar fvarId (← args.mapM argToMono)
  | .proj structName fieldIdx fvarId =>
    if (← get).typeParams.contains fvarId then
      return .erased
    else if let some info ← hasTrivialStructure? structName then
      if info.fieldIdx == fieldIdx then
        return .fvar fvarId #[]
      else
        return .erased
    else
      return e

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
  let decl := { fvarId := p.fvarId, binderName := p.binderName, type := (← toMonoType p.type), value := .fvar c.discr #[] }
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
