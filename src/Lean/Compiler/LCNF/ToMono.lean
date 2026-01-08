/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Compiler.ImplementedByAttr
public import Lean.Compiler.LCNF.InferType
public import Lean.Compiler.NoncomputableAttr

public section

namespace Lean.Compiler.LCNF

structure ToMonoM.State where
  typeParams : FVarIdHashSet := {}
  noncomputableVars : Std.HashMap FVarId Name := {}

abbrev ToMonoM := StateRefT ToMonoM.State CompilerM

def Param.toMono (param : Param) : ToMonoM Param := do
  if isTypeFormerType param.type then
    modify fun s => { s with typeParams := s.typeParams.insert param.fvarId }
  param.update (← toMonoType param.type)

def throwNoncomputableError {α : Type} (declName : Name) : ToMonoM α :=
  throwNamedError lean.dependsOnNoncomputable m!"failed to compile definition, consider marking it as 'noncomputable' because it depends on '{.ofConstName declName}', which is 'noncomputable'"

def checkFVarUse (fvarId : FVarId) : ToMonoM Unit := do
  if let some declName := (← get).noncomputableVars.get? fvarId then
    throwNoncomputableError declName

def checkFVarUseDeferred (resultFVar fvarId : FVarId) : ToMonoM Unit := do
  if let some declName := (← get).noncomputableVars.get? fvarId then
    modify fun s => { s with noncomputableVars := s.noncomputableVars.insert resultFVar declName }

@[inline]
def argToMonoBase (check : FVarId → ToMonoM Unit) (arg : Arg) : ToMonoM Arg := do
  match arg with
  | .erased | .type .. => return .erased
  | .fvar fvarId =>
    if (← get).typeParams.contains fvarId then
      return .erased
    else
      check fvarId
      return arg

def argToMono (arg : Arg) : ToMonoM Arg := argToMonoBase checkFVarUse arg

def argToMonoDeferredCheck (resultFVar : FVarId) (arg : Arg) : ToMonoM Arg :=
  argToMonoBase (checkFVarUseDeferred resultFVar) arg

def argsToMonoWithFnType (resultFVar : FVarId) (args : Array Arg) (type : Expr)
    : ToMonoM (Array Arg) := do
  let mut remainingType : Option Expr := some type
  let mut result := Array.emptyWithCapacity args.size
  for arg in args do
    let monoArg ← if let some (.forallE _ d b _ ) := remainingType then
      remainingType := some b
      if d.isErased then
        pure .erased
      else
        argToMonoDeferredCheck resultFVar arg
    else
      remainingType := none
      argToMonoDeferredCheck resultFVar arg
    result := result.push monoArg
  return result

def argsToMonoRedArg (resultFVar : FVarId) (args : Array Arg) (params : Array Param)
    (redArgs : Array Arg) : ToMonoM (Array Arg) := do
  let mut result := #[]
  let mut argIdx := 0
  for redArg in redArgs do
    match redArg with
    | .fvar fvarId =>
      while params[argIdx]!.fvarId != fvarId do
        argIdx := argIdx + 1
      let arg ← argToMonoDeferredCheck resultFVar args[argIdx]!
      argIdx := argIdx + 1
      result := result.push arg
    | .erased | .type _ => pure ()
  for arg in args[params.size...*] do
    let arg ← argToMonoDeferredCheck resultFVar arg
    result := result.push arg
  return result

def ctorAppToMono (resultFVar : FVarId) (ctorInfo : ConstructorVal) (args : Array Arg)
    : ToMonoM LetValue := do
  let argsNewParams : Array Arg := .replicate ctorInfo.numParams .erased
  let argsNewFields ← args[ctorInfo.numParams...*].toArray.mapM (argToMonoDeferredCheck resultFVar)
  let argsNew := argsNewParams ++ argsNewFields
  return .const ctorInfo.name [] argsNew

partial def LetValue.toMono (e : LetValue) (resultFVar : FVarId) : ToMonoM LetValue := do
  match e with
  | .erased | .lit .. => return e
  | .const declName _ args =>
    if declName == ``Decidable.isTrue then
      return .const ``Bool.true [] #[]
    else if declName == ``Decidable.isFalse then
      return .const ``Bool.false [] #[]
    else if declName == ``Decidable.decide then
      -- Decidable.decide is the identity function since Decidable
      -- and Bool have the same runtime representation.
      return args[1]!.toLetValue
    else if declName == ``Quot.mk then
      return args[2]!.toLetValue
    else if declName == ``Quot.lcInv then
      match args[2]! with
      | .fvar fvarId =>
        let mut extraArgs : Array Arg := .emptyWithCapacity (args.size - 3)
        for i in 3...args.size do
          let arg ← argToMono args[i]!
          extraArgs := extraArgs.push arg
        return .fvar fvarId extraArgs
      | .erased | .type _ =>
        return .erased
    else if declName == ``Nat.zero then
      return .lit (.nat 0)
    else if declName == ``Nat.succ then
      -- This should have been handled in Code.toMono.
      unreachable!
    else if let some (.ctorInfo ctorInfo) := (← getEnv).find? declName then
      if let some info ← hasTrivialStructure? ctorInfo.induct then
        args[ctorInfo.numParams + info.fieldIdx]!.toLetValue.toMono resultFVar
      else
        ctorAppToMono resultFVar ctorInfo args
    else
      let env ← getEnv
      if isNoncomputable env declName && !(isExtern env declName) then
        modify fun s => { s with noncomputableVars := s.noncomputableVars.insert resultFVar declName }
      if let some monoDecl ← getMonoDecl? declName then
        if args.size >= monoDecl.params.size then
          if let .code (.let { fvarId := resultFVar, value := .const callName _ callArgs, .. }
                             (.return retFVar)) := monoDecl.value then
            let redArgDeclName := declName ++ `_redArg
            if callName == redArgDeclName && retFVar == resultFVar then
              let args ← argsToMonoRedArg resultFVar args monoDecl.params callArgs
              return .const redArgDeclName [] args
        let args ← argsToMonoWithFnType resultFVar args monoDecl.type
        return .const declName [] args
      else
        let args ← args.mapM (argToMonoDeferredCheck resultFVar)
        return .const declName [] args
  | .fvar fvarId args =>
    if (← get).typeParams.contains fvarId then
      return .erased
    else
      checkFVarUseDeferred resultFVar fvarId
      return .fvar fvarId (← args.mapM (argToMonoDeferredCheck resultFVar))
  | .proj structName fieldIdx baseFVar =>
    if (← get).typeParams.contains baseFVar then
      return .erased
    else
      checkFVarUseDeferred resultFVar baseFVar
      if let some info ← hasTrivialStructure? structName then
        if info.fieldIdx == fieldIdx then
          return .fvar baseFVar #[]
        else
          return .erased
      else
        return e

def LetDecl.toMono (decl : LetDecl) : ToMonoM LetDecl := do
  let type ← toMonoType decl.type
  let value ← decl.value.toMono decl.fvarId
  decl.update type value

def mkFieldParamsForComputedFields (ctorType : Expr) (numParams : Nat) (numNewFields : Nat)
    (oldFields : Array Param) : ToMonoM (Array Param) := do
  let mut type := ctorType
  for _ in *...numParams do
    match type with
    | .forallE _ _ body _ =>
      type := body
    | _ => unreachable!
  let mut newFields := Array.emptyWithCapacity (oldFields.size + numNewFields)
  for _ in *...numNewFields do
    match type with
    | .forallE name fieldType body _ =>
      let param ← mkParam name (← toMonoType fieldType) false
      newFields := newFields.push param
      type := body
    | _ => unreachable!
  return newFields ++ oldFields

mutual

partial def FunDecl.toMono (decl : FunDecl) : ToMonoM FunDecl := do
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
  return .cases ⟨``Bool, resultType, c.discr, alts⟩

/-- Eliminate `cases` for `Nat`. -/
partial def casesNatToMono (c: Cases) (_ : c.typeName == ``Nat) : ToMonoM Code := do
  let resultType ← toMonoType c.resultType
  let natType := mkConst ``Nat
  let zeroDecl ← mkLetDecl `zero natType (.lit (.nat 0))
  let isZeroDecl ← mkLetDecl `isZero (mkConst ``Bool) (.const ``Nat.decEq [] #[.fvar c.discr, .fvar zeroDecl.fvarId])
  let alts ← c.alts.mapM fun alt => do
    match alt with
    | .default k => return alt.updateCode (← k.toMono)
    | .alt ctorName ps k =>
      eraseParams ps
      if ctorName == ``Nat.succ then
        let p := ps[0]!
        let oneDecl ← mkLetDecl `one natType (.lit (.nat 1))
        let subOneDecl := { fvarId := p.fvarId, binderName := p.binderName, type := natType, value := .const ``Nat.sub [] #[.fvar c.discr, .fvar oneDecl.fvarId] }
        modifyLCtx fun lctx => lctx.addLetDecl subOneDecl
        return .alt ``Bool.false #[] (.let oneDecl (.let subOneDecl (← k.toMono)))
      else
        return .alt ``Bool.true #[] (← k.toMono)
  return .let zeroDecl (.let isZeroDecl (.cases ⟨``Bool, resultType, isZeroDecl.fvarId, alts⟩))

/-- Eliminate `cases` for `Int`. -/
partial def casesIntToMono (c: Cases) (_ : c.typeName == ``Int) : ToMonoM Code := do
  let resultType ← toMonoType c.resultType
  let natType := mkConst ``Nat
  let zeroNatDecl ← mkLetDecl `natZero natType (.lit (.nat 0))
  let zeroIntDecl ← mkLetDecl `intZero (mkConst ``Int) (.const ``Int.ofNat [] #[.fvar zeroNatDecl.fvarId])
  let isNegDecl ← mkLetDecl `isNeg (mkConst ``Bool) (.const ``Int.decLt [] #[.fvar c.discr, .fvar zeroIntDecl.fvarId])
  let alts ← c.alts.mapM fun alt => do
    match alt with
    | .default k => return alt.updateCode (← k.toMono)
    | .alt ctorName ps k =>
      eraseParams ps
      let p := ps[0]!
      if ctorName == ``Int.negSucc then
        let absDecl ← mkLetDecl `abs natType (.const ``Int.natAbs [] #[.fvar c.discr])
        let oneDecl ← mkLetDecl `one natType (.lit (.nat 1))
        let subOneDecl := { fvarId := p.fvarId, binderName := p.binderName, type := natType, value := .const ``Nat.sub [] #[.fvar absDecl.fvarId, .fvar oneDecl.fvarId] }
        modifyLCtx fun lctx => lctx.addLetDecl subOneDecl
        return .alt ``Bool.true #[] (.let absDecl (.let oneDecl (.let subOneDecl (← k.toMono))))
      else
        let absDecl := { fvarId := p.fvarId, binderName := p.binderName, type := natType, value := .const ``Int.natAbs [] #[.fvar c.discr] }
        modifyLCtx fun lctx => lctx.addLetDecl absDecl
        return .alt ``Bool.false #[] (.let absDecl (← k.toMono))
  return .let zeroNatDecl (.let zeroIntDecl (.let isNegDecl (.cases ⟨``Bool, resultType, isNegDecl.fvarId, alts⟩)))

/-- Eliminate `cases` for `UInt` types. -/
partial def casesUIntToMono (c : Cases) (uintName : Name) (_ : c.typeName == uintName) : ToMonoM Code := do
  assert! c.alts.size == 1
  let .alt _ ps k := c.alts[0]! | unreachable!
  eraseParams ps
  let p := ps[0]!
  let decl := { fvarId := p.fvarId, binderName := p.binderName, type := anyExpr, value := .const (.str uintName "toBitVec") [] #[.fvar c.discr] }
  modifyLCtx fun lctx => lctx.addLetDecl decl
  let k ← k.toMono
  return .let decl k

/-- Eliminate `cases` for `Array. -/
partial def casesArrayToMono (c : Cases) (_ : c.typeName == ``Array) : ToMonoM Code := do
  assert! c.alts.size == 1
  let .alt _ ps k := c.alts[0]! | unreachable!
  eraseParams ps
  let p := ps[0]!
  let decl := { fvarId := p.fvarId, binderName := p.binderName, type := anyExpr, value := .const ``Array.toList [] #[.erased, .fvar c.discr] }
  modifyLCtx fun lctx => lctx.addLetDecl decl
  let k ← k.toMono
  return .let decl k

/-- Eliminate `cases` for `ByteArray. -/
partial def casesByteArrayToMono (c : Cases) (_ : c.typeName == ``ByteArray) : ToMonoM Code := do
  assert! c.alts.size == 1
  let .alt _ ps k := c.alts[0]! | unreachable!
  eraseParams ps
  let p := ps[0]!
  let decl := { fvarId := p.fvarId, binderName := p.binderName, type := anyExpr, value := .const ``ByteArray.data [] #[.fvar c.discr] }
  modifyLCtx fun lctx => lctx.addLetDecl decl
  let k ← k.toMono
  return .let decl k

/-- Eliminate `cases` for `FloatArray. -/
partial def casesFloatArrayToMono (c : Cases) (_ : c.typeName == ``FloatArray) : ToMonoM Code := do
  assert! c.alts.size == 1
  let .alt _ ps k := c.alts[0]! | unreachable!
  eraseParams ps
  let p := ps[0]!
  let decl := { fvarId := p.fvarId, binderName := p.binderName, type := anyExpr, value := .const ``FloatArray.data [] #[.fvar c.discr] }
  modifyLCtx fun lctx => lctx.addLetDecl decl
  let k ← k.toMono
  return .let decl k

/-- Eliminate `cases` for `String. -/
partial def casesStringToMono (c : Cases) (_ : c.typeName == ``String) : ToMonoM Code := do
  assert! c.alts.size == 1
  let .alt _ ps k := c.alts[0]! | unreachable!
  eraseParams ps
  let p := ps[0]!
  let decl := { fvarId := p.fvarId, binderName := p.binderName, type := anyExpr, value := .const ``String.toList [] #[.fvar c.discr] }
  modifyLCtx fun lctx => lctx.addLetDecl decl
  let k ← k.toMono
  return .let decl k

/-- Eliminate `cases` for `Thunk. -/
partial def casesThunkToMono (c : Cases) (_ : c.typeName == ``Thunk) : ToMonoM Code := do
  assert! c.alts.size == 1
  let .alt _ ps k := c.alts[0]! | unreachable!
  eraseParams ps
  let p := ps[0]!
  let letValue := .const ``Thunk.get [] #[.erased, .fvar c.discr]
  let letDecl ← mkLetDecl (← mkFreshBinderName `_x) anyExpr letValue
  let paramType := .const `PUnit []
  let decl := ⟨
    p.fvarId,
    p.binderName,
    #[← mkAuxParam paramType],
    (← mkArrow paramType anyExpr),
    .let letDecl (.return letDecl.fvarId)
  ⟩
  modifyLCtx fun lctx => lctx.addFunDecl decl
  let k ← k.toMono
  return .fun decl k

/-- Eliminate `cases` for `Task. -/
partial def casesTaskToMono (c : Cases) (_ : c.typeName == ``Task) : ToMonoM Code := do
  assert! c.alts.size == 1
  let .alt _ ps k := c.alts[0]! | unreachable!
  eraseParams ps
  let p := ps[0]!
  let decl := { fvarId := p.fvarId, binderName := p.binderName, type := anyExpr, value := .const ``Task.get [] #[.erased, .fvar c.discr] }
  modifyLCtx fun lctx => lctx.addLetDecl decl
  let k ← k.toMono
  return .let decl k

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
  | .let decl k =>
    match decl.value with
    | .const ``Nat.succ _ args =>
      let #[arg] := args | unreachable!
      let oneDecl ← mkAuxLetDecl (.lit (.nat 1))
      let decl ← decl.update decl.type (.const ``Nat.add [] #[arg, .fvar oneDecl.fvarId])
      return .let oneDecl (.let decl (← k.toMono))
    | _ =>
      return code.updateLet! (← decl.toMono) (← k.toMono)
  | .fun decl k | .jp decl k => return code.updateFun! (← decl.toMono) (← k.toMono)
  | .unreach type => return .unreach (← toMonoType type)
  | .jmp fvarId args => return code.updateJmp! fvarId (← args.mapM argToMono)
  | .return fvarId =>
    checkFVarUse fvarId
    return code
  | .cases c =>
    checkFVarUse c.discr
    if h : c.typeName == ``Decidable then
      decToMono c h
    else if h : c.typeName == ``Nat then
      casesNatToMono c h
    else if h : c.typeName == ``Int then
      casesIntToMono c h
    else if h : c.typeName == ``UInt8 then
      casesUIntToMono c ``UInt8 h
    else if h : c.typeName == ``UInt16 then
      casesUIntToMono c ``UInt16 h
    else if h : c.typeName == ``UInt32 then
      casesUIntToMono c ``UInt32 h
    else if h : c.typeName == ``UInt64 then
      casesUIntToMono c ``UInt64 h
    else if h : c.typeName == ``Array then
      casesArrayToMono c h
    else if h : c.typeName == ``ByteArray then
      casesByteArrayToMono c h
    else if h : c.typeName == ``FloatArray then
      casesFloatArrayToMono c h
    else if h : c.typeName == ``String then
      casesStringToMono c h
    else if h : c.typeName == ``Thunk then
      casesThunkToMono c h
    else if h : c.typeName == ``Task then
      casesTaskToMono c h
    else if let some info ← hasTrivialStructure? c.typeName then
      trivialStructToMono info c
    else
      let resultType ← toMonoType c.resultType
      let env ← getEnv
      let some (.inductInfo inductInfo) := env.find? c.typeName | panic! "expected inductive type"
      let casesOnName := mkCasesOnName inductInfo.name
      if (getImplementedBy? env casesOnName).isSome then
        -- TODO: Enforce that this is only used for computed fields.
        let typeName := c.typeName ++ `_impl
        let alts ← c.alts.mapM fun alt => do
          match alt with
          | .default k => return alt.updateCode (← k.toMono)
          | .alt ctorName ps k =>
            let implCtorName := ctorName ++ `_impl
            let some (.ctorInfo ctorInfo) := env.find? implCtorName | panic! "expected constructor"
            let numNewFields := ctorInfo.numFields - ps.size
            let ps ← mkFieldParamsForComputedFields ctorInfo.type ctorInfo.numParams numNewFields ps
            let k ← k.toMono
            return .alt implCtorName ps k
        return .cases ⟨typeName, resultType, c.discr, alts⟩
      else
        let alts ← c.alts.mapM fun alt =>
          match alt with
          | .default k => return alt.updateCode (← k.toMono)
          | .alt _ ps k => return alt.updateAlt! (← ps.mapM (·.toMono)) (← k.toMono)
        return code.updateCases! resultType c.discr alts

end

def Decl.toMono (decl : Decl) : CompilerM Decl := do
  go |>.run' {}
where
  go : ToMonoM Decl := do
    let type ← toMonoType decl.type
    let params ← decl.params.mapM (·.toMono)
    let value ← decl.value.mapCodeM (·.toMono)
    let decl := { decl with type, params, value, levelParams := [] }
    decl.saveMono
    return decl

def toMono : Pass where
  name     := `toMono
  run      := (·.mapM (·.toMono))
  phase    := .base
  phaseOut := .mono
  shouldAlwaysRunCheck := true

builtin_initialize
  registerTraceClass `Compiler.toMono (inherited := true)

end Lean.Compiler.LCNF
