/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Zwarich, Henrik Böving
-/
module

prelude
public import Lean.Compiler.LCNF.CompilerM
public import Lean.Compiler.LCNF.Irrelevant
import Lean.Compiler.LCNF.MonoTypes

namespace Lean.Compiler.LCNF

def impureTypeForEnum (numCtors : Nat) : Expr :=
  if numCtors == 1 then
    ImpureType.tagged
  else if numCtors < Nat.pow 2 8 then
    ImpureType.uint8
  else if numCtors < Nat.pow 2 16 then
    ImpureType.uint16
  else if numCtors < Nat.pow 2 32 then
    ImpureType.uint32
  else
    ImpureType.tagged

builtin_initialize impureTypeExt : CacheExtension Name Expr ←
  CacheExtension.register

builtin_initialize impureTrivialStructureInfoExt :
    CacheExtension Name (Option TrivialStructureInfo) ←
  CacheExtension.register

/--
The idea of this function is the same as in `ToMono`, however the notion of "irrelevancy" has
changed because we now have the `void` type which can only be erased in impure context and thus at
earliest at the conversion from mono to impure.
-/
public def hasTrivialImpureStructure? (declName : Name) : CoreM (Option TrivialStructureInfo) := do
  let isVoidType type := do
    let type ← Meta.whnfD type
    return type matches .proj ``Subtype 0 (.app (.const ``Void.nonemptyType []) _)
  let irrelevantType type :=
    Meta.isProp type <||> Meta.isTypeFormerType type <||> isVoidType type
  Irrelevant.hasTrivialStructure? impureTrivialStructureInfoExt irrelevantType declName

public def nameToImpureType (name : Name) : CoreM Expr := do
  match (← impureTypeExt.find? name) with
  | some type => return type
  | none =>
    let type ← fillCache
    impureTypeExt.insert name type
    return type
where fillCache : CoreM Expr := do
    match name with
    | ``UInt8 => return ImpureType.uint8
    | ``UInt16 => return ImpureType.uint16
    | ``UInt32 => return ImpureType.uint32
    | ``UInt64 => return ImpureType.uint64
    | ``USize => return ImpureType.usize
    | ``Float => return ImpureType.float
    | ``Float32 => return ImpureType.float32
    | ``lcErased => return ImpureType.erased
    -- `Int` is specified as an inductive type with two constructors that have relevant arguments,
    -- but it has the same runtime representation as `Nat` and thus needs to be special-cased here.
    | ``Int => return ImpureType.tobject
    | ``lcVoid => return ImpureType.void
    | _ =>
      let env ← Lean.getEnv
      let some (.inductInfo inductiveVal) := env.find? name | return ImpureType.tobject
      let ctorNames := inductiveVal.ctors
      let numCtors := ctorNames.length
      let mut numScalarCtors := 0
      for ctorName in ctorNames do
        let some (.ctorInfo ctorInfo) := env.find? ctorName | unreachable!
        let hasRelevantField ← Meta.MetaM.run' <|
                               Meta.forallTelescope ctorInfo.type fun params _ => do
          for field in params[ctorInfo.numParams...*] do
            let fieldType ← field.fvarId!.getType
            let lcnfFieldType ← toLCNFType fieldType
            let monoFieldType ← toMonoType lcnfFieldType
            if !monoFieldType.isErased then return true
          return false
        if !hasRelevantField then
          numScalarCtors := numScalarCtors + 1
      if numScalarCtors == numCtors then
        return impureTypeForEnum numCtors
      else if numScalarCtors == 0 then
        return ImpureType.object
      else
        return ImpureType.tobject

def isAnyProducingType (type : Expr) : Bool :=
  match type with
  | .const ``lcAny _ => true
  | .forallE _ _ b _ => isAnyProducingType b
  | _ => false

public partial def toImpureType (type : Expr) : CoreM Expr := do
  match type with
  | .const name _ => visitApp name #[]
  | .app .. =>
    -- All mono types are in headBeta form.
    let .const name _ := type.getAppFn | unreachable!
    visitApp name type.getAppArgs
  | .forallE _ _ b _ =>
    -- Type formers are erased, but can be used polymorphically as
    -- an arrow type producing `lcAny`. The runtime representation of
    -- erased values is a tagged scalar, so this means that any such
    -- polymorphic type must be represented as `.tobject`.
    if isAnyProducingType b then
      return ImpureType.tobject
    else
      return ImpureType.object
  | .mdata _ b => toImpureType b
  | _ => unreachable!
where
  visitApp (declName : Name) (args : Array Lean.Expr) : CoreM Expr := do
    if let some info ← hasTrivialImpureStructure? declName then
      let ctorType ← getOtherDeclBaseType info.ctorName []
      let monoType ← toMonoType (getParamTypes (← instantiateForall ctorType args[*...info.numParams]))[info.fieldIdx]!
      toImpureType monoType
    else
      nameToImpureType declName

public inductive CtorFieldInfo where
  | erased
  | object (i : Nat) (type : Expr)
  | usize  (i : Nat)
  | scalar (sz : Nat) (offset : Nat) (type : Expr)
  | void
  deriving Inhabited

namespace CtorFieldInfo

def format : CtorFieldInfo → Format
  | erased => "◾"
  | void => "void"
  | object i type => f!"obj@{i}:{type}"
  | usize i    => f!"usize@{i}"
  | scalar sz offset type => f!"scalar#{sz}@{offset}:{type}"

instance : ToFormat CtorFieldInfo := ⟨format⟩

end CtorFieldInfo

public structure CtorLayout where
  ctorInfo : CtorInfo
  fieldInfo : Array CtorFieldInfo
  deriving Inhabited

builtin_initialize ctorLayoutExt : CacheExtension Name CtorLayout ←
  CacheExtension.register

public def getCtorLayout (ctorName : Name) : CoreM CtorLayout := do
  match (← ctorLayoutExt.find? ctorName) with
  | some info => return info
  | none =>
    let info ← fillCache
    ctorLayoutExt.insert ctorName info
    return info
where fillCache := do
  let .some (.ctorInfo ctorInfo) := (← getEnv).find? ctorName | unreachable!
  Meta.MetaM.run' <| Meta.forallTelescopeReducing ctorInfo.type fun params _ => do
    let mut fields : Array CtorFieldInfo := .emptyWithCapacity ctorInfo.numFields
    let mut nextIdx := 0
    let mut has1BScalar := false
    let mut has2BScalar := false
    let mut has4BScalar := false
    let mut has8BScalar := false
    for field in params[ctorInfo.numParams...(ctorInfo.numParams + ctorInfo.numFields)] do
      let fieldType ← field.fvarId!.getType
      let lcnfFieldType ← LCNF.toLCNFType fieldType
      let monoFieldType ← LCNF.toMonoType lcnfFieldType
      let irFieldType ← toImpureType monoFieldType
      let ctorField ← match irFieldType with
      | ImpureType.object | ImpureType.tagged | ImpureType.tobject => do
        let i := nextIdx
        nextIdx := nextIdx + 1
        pure <| .object i irFieldType
      | ImpureType.usize => pure <| .usize 0
      | ImpureType.erased => .pure <| .erased
      | ImpureType.void => .pure <| .void
      | ImpureType.uint8 =>
        has1BScalar := true
        .pure <| .scalar 1 0 ImpureType.uint8
      | ImpureType.uint16 =>
        has2BScalar := true
        .pure <| .scalar 2 0 ImpureType.uint16
      | ImpureType.uint32 =>
        has4BScalar := true
        .pure <| .scalar 4 0 ImpureType.uint32
      | ImpureType.uint64 =>
        has8BScalar := true
        .pure <| .scalar 8 0 ImpureType.uint64
      | ImpureType.float32 =>
        has4BScalar := true
        .pure <| .scalar 4 0 ImpureType.float32
      | ImpureType.float =>
        has8BScalar := true
        .pure <| .scalar 8 0 ImpureType.float
      | _ => unreachable!
      fields := fields.push ctorField
    let numObjs := nextIdx
    ⟨fields, nextIdx⟩ := Id.run <| StateT.run (s := nextIdx) <| fields.mapM fun field => do
      match field with
      | .usize _ => do
        let i ← modifyGet fun nextIdx => (nextIdx, nextIdx + 1)
        return .usize i
      | .object .. | .scalar .. | .erased | .void => return field
    let numUSize := nextIdx - numObjs
    let adjustScalarsForSize (fields : Array CtorFieldInfo) (size : Nat) (nextOffset : Nat)
        : Array CtorFieldInfo × Nat :=
      Id.run <| StateT.run (s := nextOffset) <| fields.mapM fun field => do
        match field with
        | .scalar sz _ type => do
          if sz == size then
            let offset ← modifyGet fun nextOffset => (nextOffset, nextOffset + sz)
            return .scalar sz offset type
          else
            return field
        | .object .. | .usize _ | .erased | .void => return field
    let mut nextOffset := 0
    if has8BScalar then
      ⟨fields, nextOffset⟩ := adjustScalarsForSize fields 8 nextOffset
    if has4BScalar then
      ⟨fields, nextOffset⟩ := adjustScalarsForSize fields 4 nextOffset
    if has2BScalar then
      ⟨fields, nextOffset⟩ := adjustScalarsForSize fields 2 nextOffset
    if has1BScalar then
      ⟨fields, nextOffset⟩ := adjustScalarsForSize fields 1 nextOffset
    return {
      ctorInfo := {
        name := ctorName
        cidx := ctorInfo.cidx
        size := numObjs
        usize := numUSize
        ssize := nextOffset
      }
      fieldInfo := fields
    }

public def getOtherDeclImpureType (declName : Name) : CoreM Expr := do
  match (← impureTypeExt.find? declName) with
  | some type => return type
  | none =>
    let type ← toImpureType (← getOtherDeclMonoType declName)
    monoTypeExt.insert declName type
    return type

end Lean.Compiler.LCNF
