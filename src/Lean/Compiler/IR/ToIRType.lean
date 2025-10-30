/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Compiler.IR.Format
public import Lean.Compiler.LCNF.MonoTypes

public section

namespace Lean
namespace IR

open Lean.Compiler (LCNF.CacheExtension LCNF.isTypeFormerType LCNF.toLCNFType LCNF.toMonoType
  LCNF.TrivialStructureInfo LCNF.getOtherDeclBaseType LCNF.getParamTypes LCNF.instantiateForall
  LCNF.Irrelevant.hasTrivialStructure?)

def irTypeForEnum (numCtors : Nat) : IRType :=
  if numCtors == 1 then
    .tagged
  else if numCtors < Nat.pow 2 8 then
    .uint8
  else if numCtors < Nat.pow 2 16 then
    .uint16
  else if numCtors < Nat.pow 2 32 then
    .uint32
  else
    .tagged

builtin_initialize irTypeExt : LCNF.CacheExtension Name IRType ←
  LCNF.CacheExtension.register

builtin_initialize trivialStructureInfoExt :
    LCNF.CacheExtension Name (Option LCNF.TrivialStructureInfo) ←
  LCNF.CacheExtension.register

/--
The idea of this function is the same as in `ToMono`, however the notion of "irrelevancy" has
changed because we now have the `void` type which can only be erased in impure context and thus at
earliest at the conversion from mono to IR.
-/
def hasTrivialStructure? (declName : Name) : CoreM (Option LCNF.TrivialStructureInfo) := do
  let isVoidType type := do
    let type ← Meta.whnfD type
    return type matches .proj ``Subtype 0 (.app (.const ``Void.nonemptyType []) _)
  let irrelevantType type :=
    Meta.isProp type <||> Meta.isTypeFormerType type <||> isVoidType type
  LCNF.Irrelevant.hasTrivialStructure? trivialStructureInfoExt irrelevantType declName

def nameToIRType (name : Name) : CoreM IRType := do
  match (← irTypeExt.find? name) with
  | some type => return type
  | none =>
    let type ← fillCache
    irTypeExt.insert name type
    return type
where fillCache : CoreM IRType := do
    match name with
    | ``UInt8 => return .uint8
    | ``UInt16 => return .uint16
    | ``UInt32 => return .uint32
    | ``UInt64 => return .uint64
    | ``USize => return .usize
    | ``Int8 => return .int8
    | ``Int16 => return .int16
    | ``Int32 => return .int32
    | ``Int64 => return .int64
    | ``ISize => return .isize
    | ``Float => return .float
    | ``Float32 => return .float32
    | ``lcErased => return .erased
    -- `Int` is specified as an inductive type with two constructors that have relevant arguments,
    -- but it has the same runtime representation as `Nat` and thus needs to be special-cased here.
    | ``Int => return .tobject
    | ``lcVoid => return .void
    | _ =>
      let env ← Lean.getEnv
      let some (.inductInfo inductiveVal) := env.find? name | return .tobject
      let ctorNames := inductiveVal.ctors
      let numCtors := ctorNames.length
      let mut numScalarCtors := 0
      for ctorName in ctorNames do
        let some (.ctorInfo ctorInfo) := env.find? ctorName | unreachable!
        let hasRelevantField ← Meta.MetaM.run' <|
                               Meta.forallTelescope ctorInfo.type fun params _ => do
          for field in params[ctorInfo.numParams...*] do
            let fieldType ← field.fvarId!.getType
            let lcnfFieldType ← LCNF.toLCNFType fieldType
            let monoFieldType ← LCNF.toMonoType lcnfFieldType
            if !monoFieldType.isErased then return true
          return false
        if !hasRelevantField then
          numScalarCtors := numScalarCtors + 1
      if numScalarCtors == numCtors then
        return irTypeForEnum numCtors
      else if numScalarCtors == 0 then
        return .object
      else
        return .tobject

private def isAnyProducingType (type : Lean.Expr) : Bool :=
  match type with
  | .const ``lcAny _ => true
  | .forallE _ _ b _ => isAnyProducingType b
  | _ => false

partial def toIRType (type : Lean.Expr) : CoreM IRType := do
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
      return .tobject
    else
      return .object
  | .mdata _ b => toIRType b
  | _ => unreachable!
where
  visitApp (declName : Name) (args : Array Lean.Expr) : CoreM IRType := do
    if let some info ← hasTrivialStructure? declName then
      let ctorType ← LCNF.getOtherDeclBaseType info.ctorName []
      let monoType ← LCNF.toMonoType (LCNF.getParamTypes (← LCNF.instantiateForall ctorType args[*...info.numParams]))[info.fieldIdx]!
      toIRType monoType
    else
      nameToIRType declName

inductive CtorFieldInfo where
  | erased
  | object (i : Nat) (type : IRType)
  | usize  (i : Nat) (signed : Bool)
  | scalar (sz : Nat) (offset : Nat) (type : IRType)
  | void
  deriving Inhabited

namespace CtorFieldInfo

def format : CtorFieldInfo → Format
  | erased => "◾"
  | void => "void"
  | object i type => f!"obj@{i}:{type}"
  | usize i s => if s then f!"isize@{i}" else f!"usize@{i}"
  | scalar sz offset type => f!"scalar#{sz}@{offset}:{type}"

instance : ToFormat CtorFieldInfo := ⟨format⟩

end CtorFieldInfo

structure CtorLayout where
  ctorInfo : CtorInfo
  fieldInfo : Array CtorFieldInfo
  deriving Inhabited

builtin_initialize ctorLayoutExt : LCNF.CacheExtension Name CtorLayout ←
  LCNF.CacheExtension.register

def getCtorLayout (ctorName : Name) : CoreM CtorLayout := do
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
      let irFieldType ← toIRType monoFieldType
      let ctorField ← match irFieldType with
      | .object | .tagged | .tobject => do
        let i := nextIdx
        nextIdx := nextIdx + 1
        pure <| .object i irFieldType
      | .usize => pure <| .usize 0 false
      | .isize => pure <| .usize 0 true
      | .erased => .pure <| .erased
      | .void => .pure <| .void
      | .uint8 =>
        has1BScalar := true
        .pure <| .scalar 1 0 .uint8
      | .int8 =>
        has1BScalar := true
        .pure <| .scalar 1 0 .int8
      | .uint16 =>
        has2BScalar := true
        .pure <| .scalar 2 0 .uint16
      | .int16 =>
        has2BScalar := true
        .pure <| .scalar 2 0 .int16
      | .uint32 =>
        has4BScalar := true
        .pure <| .scalar 4 0 .uint32
      | .int32 =>
        has4BScalar := true
        .pure <| .scalar 4 0 .int32
      | .uint64 =>
        has8BScalar := true
        .pure <| .scalar 8 0 .uint64
      | .int64 =>
        has8BScalar := true
        .pure <| .scalar 8 0 .int64
      | .float32 =>
        has4BScalar := true
        .pure <| .scalar 4 0 .float32
      | .float =>
        has8BScalar := true
        .pure <| .scalar 8 0 .float
      | .struct .. | .union .. => unreachable!
      fields := fields.push ctorField
    let numObjs := nextIdx
    ⟨fields, nextIdx⟩ := Id.run <| StateT.run (s := nextIdx) <| fields.mapM fun field => do
      match field with
      | .usize _ s => do
        let i ← modifyGet fun nextIdx => (nextIdx, nextIdx + 1)
        return .usize i s
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
        | .object .. | .usize _ _ | .erased | .void => return field
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

end IR
end Lean
