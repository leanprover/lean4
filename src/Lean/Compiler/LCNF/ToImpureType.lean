/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Zwarich, Henrik Böving
-/
module

prelude
public import Lean.Compiler.LCNF.Irrelevant
import Lean.Compiler.LCNF.MonoTypes
import Init.Data.Format.Macro

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

/--
Maps each inductive type to its IR (impure) type representation. Populated eagerly in the type's
defining module by `setImpureType` (driven from `compileDecls`); consumers read it via
`nameToImpureType`. Persisted across modules because computing an inductive's impure type walks each
constructor's field types, which can reference constants from non-transitively (privately) imported
modules.
-/
builtin_initialize impureTypeExt : MapDeclarationExtension Expr ←
  mkMapDeclarationExtension (asyncMode := .sync)

builtin_initialize impureTrivialStructureInfoExt :
    MapDeclarationExtension (Option TrivialStructureInfo) ←
  mkMapDeclarationExtension (asyncMode := .sync)

/--
The idea of this function is the same as in `ToMono`, however the notion of "irrelevancy" has
changed because we now have the `void` type which can only be erased in impure context and thus at
earliest at the conversion from mono to impure.
-/
def impureIrrelevantType (type : Expr) : MetaM Bool := do
  let isVoidType type := do
    let type ← Meta.whnfD type
    return type matches .proj ``Subtype 0 (.app (.const ``Void.nonemptyType []) _)
  Meta.isProp type <||> Meta.isTypeFormerType type <||> isVoidType type

/-- Eagerly computes and persists the impure trivial-structure info of `declName`; see `compileDecls`. -/
public def setHasTrivialImpureStructure? (declName : Name) : CoreM Unit :=
  Irrelevant.setHasTrivialStructure? impureTrivialStructureInfoExt impureIrrelevantType declName

public def hasTrivialImpureStructure? (declName : Name) : CoreM (Option TrivialStructureInfo) :=
  Irrelevant.hasTrivialStructure? impureTrivialStructureInfoExt declName

/--
IR representations that are fixed independently of the environment: builtin scalar types and the
compiler's pseudo-constants (`lcErased`/`lcVoid`, which are not inductives). These never need to be
persisted in `impureTypeExt`.
-/
def builtinImpureType? : Name → Option Expr
  | ``UInt8 => some ImpureType.uint8
  | ``UInt16 => some ImpureType.uint16
  | ``UInt32 => some ImpureType.uint32
  | ``UInt64 => some ImpureType.uint64
  | ``USize => some ImpureType.usize
  | ``Float => some ImpureType.float
  | ``Float32 => some ImpureType.float32
  | ``lcErased => some ImpureType.erased
  -- `Int` is specified as an inductive type with two constructors that have relevant arguments,
  -- but it has the same runtime representation as `Nat` and thus needs to be special-cased here.
  | ``Int => some ImpureType.tobject
  | ``lcVoid => some ImpureType.void
  | _ => none

/--
Computes the IR (impure) type of `name` from scratch by inspecting its constructors. For inductives
this walks the constructor field types, so it must run in the defining module, where those types
(including private ones) are accessible.
-/
def computeImpureType (name : Name) : CoreM Expr := do
  if let some type := builtinImpureType? name then return type
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

/-- Eagerly computes and persists the IR type of inductive `name`; see `compileDecls`. -/
public def setImpureType (name : Name) : CoreM Unit := do
  if (builtinImpureType? name).isSome then return
  unless (impureTypeExt.find? (← getEnv) name).isSome do
    modifyEnv (impureTypeExt.insert · name (← computeImpureType name))

/--
Returns the IR (impure) type representation of `name`. Requires `compileDecls` to have been run for
inductive type `name`.
-/
public def nameToImpureType (name : Name) : CoreM Expr := do
  if let some type := builtinImpureType? name then return type
  let some (.inductInfo _) := (← getEnv).find? name | return ImpureType.tobject
  let some type := impureTypeExt.find? (← getEnv) name
    | throwError "`{name}` was not compiled; `compileDecls` must run on inductive types first"
  return type

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

builtin_initialize ctorLayoutExt : MapDeclarationExtension CtorLayout ←
  mkMapDeclarationExtension (asyncMode := .sync)

/-- Eagerly computes and persists the layout of constructor `ctorName`; see `compileDecls`. -/
public def setCtorLayout (ctorName : Name) : CoreM Unit := do
  unless (ctorLayoutExt.find? (← getEnv) ctorName).isSome do
    modifyEnv (ctorLayoutExt.insert · ctorName (← fillCache))
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

/--
Returns the runtime layout of constructor `ctorName`. Requires `compileDecls` to have been run for
its inductive type.
-/
public def getCtorLayout (ctorName : Name) : CoreM CtorLayout := do
  let some info := ctorLayoutExt.find? (← getEnv) ctorName
    | throwError "`{ctorName}` was not compiled; `compileDecls` must run on inductive types first"
  return info

/--
Eagerly computes and persists all cross-module compiler caches for the inductive types `typeNames`
(and their constructors) in their defining module; run from `compileDecls`.
-/
public def compileInductives (typeNames : Array Name) : CoreM Unit := do
  let inductiveNames ← typeNames.filterM fun n => return (← getEnv).find? n matches some (.inductInfo _)
  -- The readers are strict, so we fill in dependency phases across the whole (possibly mutual)
  -- block: each phase only reads caches filled by an earlier phase or an imported module.
  for typeName in inductiveNames do
    setHasTrivialStructure? typeName
    setHasTrivialImpureStructure? typeName
  for typeName in inductiveNames do  -- reads the trivial-structure info above
    setOtherDeclMonoType typeName
    setImpureType typeName
  for typeName in inductiveNames do  -- reads the type-level info above
    let .inductInfo iv ← getConstInfo typeName | unreachable!
    for ctorName in iv.ctors do
      setOtherDeclMonoType ctorName
      setCtorLayout ctorName

end Lean.Compiler.LCNF
