/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Lean.Compiler.LCNF.CompilerM
import Lean.Compiler.LCNF.BaseTypes
import Lean.Compiler.LCNF.Util

namespace Lean.Compiler.LCNF

/--
Given a constructor, return a bitmask `m` s.t. `m[i]` is true if field `i` is
computationally relevant.
-/
def getRelevantCtorFields (ctorName : Name) (trivialType : Expr → MetaM Bool) :
    CoreM (Array Bool) := do
  let .ctorInfo info ← getConstInfo ctorName | unreachable!
  Meta.MetaM.run' do
    Meta.forallTelescopeReducing info.type fun xs _ => do
      let mut result := #[]
      for x in xs[info.numParams...*] do
        let type ← Meta.inferType x
        result := result.push !(← trivialType type)
      return result

/--
We say a structure has a trivial structure if it has not builtin support in the runtime,
it has only one constructor, and this constructor has only one relevant field.
-/
public structure TrivialStructureInfo where
  ctorName  : Name
  numParams : Nat
  fieldIdx  : Nat
  deriving Inhabited, Repr

/--
Return `some fieldIdx` if `declName` is the name of an inductive datatype s.t.
- It does not have builtin support in the runtime.
- It has only one constructor.
- This constructor has only one computationally relevant field.
-/
public def Irrelevant.hasTrivialStructure?
    (cacheExt : CacheExtension Name (Option TrivialStructureInfo))
    (trivialType : Expr → MetaM Bool) (declName : Name) : CoreM (Option TrivialStructureInfo) := do
  match (← cacheExt.find? declName) with
  | some info? => return info?
  | none =>
    let info? ← fillCache
    cacheExt.insert declName info?
    return info?
where fillCache : CoreM (Option TrivialStructureInfo) := do
  if isRuntimeBuiltinType declName then return none
  let .inductInfo info ← getConstInfo declName | return none
  if info.isUnsafe || info.isRec then return none
  let [ctorName] := info.ctors | return none
  let ctorType ← getOtherDeclBaseType ctorName []
  if ctorType.isErased then return none
  let mask ← getRelevantCtorFields ctorName trivialType
  let mut result := none
  for h : i in *...mask.size do
    if mask[i] then
      if result.isSome then return none
      result := some { ctorName, fieldIdx := i, numParams := info.numParams }
  return result


end Lean.Compiler.LCNF
