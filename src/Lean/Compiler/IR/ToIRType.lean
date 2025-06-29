/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Environment
import Lean.Compiler.IR.Format
import Lean.Compiler.LCNF.CompilerM

namespace Lean
namespace IR

open Lean.Compiler (LCNF.CacheExtension)

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
  cidx       : Nat
  fieldInfo  : List CtorFieldInfo
  numObjs    : Nat
  numUSize   : Nat
  scalarSize : Nat

@[extern "lean_ir_get_ctor_layout"]
opaque getCtorLayout (env : @& Environment) (ctorName : @& Name) : Except String CtorLayout

builtin_initialize ctorInfoExt : LCNF.CacheExtension Name (CtorInfo × (Array CtorFieldInfo)) ←
  LCNF.CacheExtension.register

def getCtorInfo (name : Name) : CoreM (CtorInfo × (Array CtorFieldInfo)) := do
  match (← ctorInfoExt.find? name) with
  | some info => return info
  | none =>
    let info ← fillCache
    ctorInfoExt.insert name info
    return info
where fillCache := do
  match getCtorLayout (← Lean.getEnv) name with
  | .ok ctorLayout =>
    return ⟨{
      name,
      cidx := ctorLayout.cidx,
      size := ctorLayout.numObjs,
      usize := ctorLayout.numUSize,
      ssize := ctorLayout.scalarSize
    }, ctorLayout.fieldInfo.toArray⟩
  | .error .. => panic! "unrecognized constructor"

end IR
end Lean
