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

def irTypeForEnum (numCtors : Nat) : IRType :=
  if numCtors == 1 then
    .object
  else if numCtors < Nat.pow 2 8 then
    .uint8
  else if numCtors < Nat.pow 2 16 then
    .uint16
  else if numCtors < Nat.pow 2 32 then
    .uint32
  else
    .object

builtin_initialize irTypeExt : LCNF.CacheExtension Name IRType ←
  LCNF.CacheExtension.register

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
    | ``Float => return .float
    | ``Float32 => return .float32
    | ``lcErased => return .irrelevant
    | _ =>
      let env ← Lean.getEnv
      let some (.inductInfo inductiveVal) := env.find? name | return .object
      let ctorNames := inductiveVal.ctors
      let numCtors := ctorNames.length
      for ctorName in ctorNames do
        let some (.ctorInfo ctorInfo) := env.find? ctorName | unreachable!
        let isRelevant ← Meta.MetaM.run' <|
                         Meta.forallTelescopeReducing ctorInfo.type fun params _ => do
          for field in params[ctorInfo.numParams...*] do
            let fieldType ← field.fvarId!.getType
            let lcnfFieldType ← LCNF.toLCNFType fieldType
            let monoFieldType ← LCNF.toMonoType lcnfFieldType
            if !monoFieldType.isErased then return true
          return false
        if isRelevant then return .object
      return irTypeForEnum numCtors

def toIRType (type : Lean.Expr) : CoreM IRType := do
  match type with
  | .const name _ => nameToIRType name
  | .app .. =>
    -- All mono types are in headBeta form.
    let .const name _ := type.getAppFn | unreachable!
    nameToIRType name
  | .forallE .. => return .object
  | _ => unreachable!

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
