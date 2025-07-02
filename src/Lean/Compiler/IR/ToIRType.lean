/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Environment
import Lean.Compiler.IR.Format
import Lean.Compiler.LCNF.CompilerM
import Lean.Compiler.LCNF.MonoTypes
import Lean.Compiler.LCNF.Types

namespace Lean
namespace IR

open Lean.Compiler (LCNF.CacheExtension LCNF.isTypeFormerType LCNF.toLCNFType LCNF.toMonoType)

builtin_initialize scalarTypeExt : LCNF.CacheExtension Name (Option IRType) ←
  LCNF.CacheExtension.register

def lowerEnumToScalarType? (name : Name) : CoreM (Option IRType) := do
  match (← scalarTypeExt.find? name) with
  | some info? => return info?
  | none =>
    let info? ← fillCache
    scalarTypeExt.insert name info?
    return info?
where fillCache : CoreM (Option IRType) := do
  let env ← Lean.getEnv
  let some (.inductInfo inductiveVal) := env.find? name | return none
  let ctorNames := inductiveVal.ctors
  let numCtors := ctorNames.length
  for ctorName in ctorNames do
    let some (.ctorInfo ctorVal) := env.find? ctorName | panic! "expected valid constructor name"
    if ctorVal.type.isForall then return none
  return if numCtors == 1 then
    none
  else if numCtors < Nat.pow 2 8 then
    some .uint8
  else if numCtors < Nat.pow 2 16 then
    some .uint16
  else if numCtors < Nat.pow 2 32 then
    some .uint32
  else
    none

def toIRType (e : Lean.Expr) : CoreM IRType := do
  match e with
  | .const name .. =>
    match name with
    | ``UInt8 => return .uint8
    | ``UInt16 => return .uint16
    | ``UInt32 => return .uint32
    | ``UInt64 => return .uint64
    | ``USize => return .usize
    | ``Float => return .float
    | ``Float32 => return .float32
    | ``lcErased => return .irrelevant
    | _ => nameToIRType name
  | .app f _ =>
    -- All mono types are in headBeta form.
    if let .const name _ := f then
      nameToIRType name
    else
      return .object
  | .forallE .. => return .object
  | _ => panic! "invalid type"
where
  nameToIRType name := do
    if let some scalarType ← lowerEnumToScalarType? name then
      return scalarType
    else
      return .object

inductive CtorFieldInfo where
  | irrelevant
  | object (i : Nat)
  | usize  (i : Nat)
  | scalar (sz : Nat) (offset : Nat) (type : IRType)
  deriving Inhabited

namespace CtorFieldInfo

def format : CtorFieldInfo → Format
  | irrelevant => "◾"
  | object i   => f!"obj@{i}"
  | usize i    => f!"usize@{i}"
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
      let ctorField ← match (← toIRType monoFieldType) with
      | .object | .tobject => do
        let i := nextIdx
        nextIdx := nextIdx + 1
        pure <| .object i
      | .usize => pure <| .usize 0
      | .irrelevant => .pure <| .irrelevant
      | .uint8 =>
        has1BScalar := true
        .pure <| .scalar 1 0 .uint8
      | .uint16 =>
        has2BScalar := true
        .pure <| .scalar 2 0 .uint16
      | .uint32 =>
        has4BScalar := true
        .pure <| .scalar 4 0 .uint32
      | .uint64 =>
        has8BScalar := true
        .pure <| .scalar 8 0 .uint64
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
      | .usize _ => do
        let i ← modifyGet fun nextIdx => (nextIdx, nextIdx + 1)
        return .usize i
      | .object _ | .scalar .. | .irrelevant => return field
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
        | .object _ | .usize _ | .irrelevant => return field
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
