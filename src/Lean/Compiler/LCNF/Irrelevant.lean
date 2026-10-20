/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Lean.EnvExtension
public import Lean.Compiler.LCNF.CompilerM
import Lean.Compiler.LCNF.BaseTypes
import Lean.Compiler.LCNF.Util

namespace Lean.Compiler.LCNF

/--
Given a constructor, return a bitmask `m` s.t. `m[i]` is true if field `i` is
computationally relevant. Returns `none` if the constructor is not sufficiently public for the
result to be stable across modules.
-/
def getRelevantCtorFields? (ctorName : Name) (trivialType : Expr → MetaM Bool) :
    CoreM (Option (Array Bool)) := do
  let .ctorInfo info ← getConstInfo ctorName | unreachable!
  if !isPrivateName info.induct && isPrivateName ctorName then
    try
      withExporting do
      go info
    catch _ => return none
  else go info
where go info :=
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
Computes `some fieldIdx` if `declName` is the name of an inductive datatype s.t.
- It does not have builtin support in the runtime.
- It has only one constructor.
- This constructor has only one computationally relevant field.
- This information is stable across modules, i.e. the type is private or that field does not
  access private information.
-/
def Irrelevant.computeHasTrivialStructure?
    (trivialType : Expr → MetaM Bool) (declName : Name) : CoreM (Option TrivialStructureInfo) := do
  if isRuntimeBuiltinType declName then return none
  let .inductInfo info ← getConstInfo declName | return none
  if info.isUnsafe || info.isRec then return none
  let [ctorName] := info.ctors | return none
  let ctorType ← getOtherDeclBaseType ctorName []
  if ctorType.isErased then return none
  let some mask ← getRelevantCtorFields? ctorName trivialType
    | return none
  let mut result := none
  for h : i in *...mask.size do
    if mask[i] then
      if result.isSome then return none
      result := some { ctorName, fieldIdx := i, numParams := info.numParams }
  return result

/-- Eagerly computes and persists the trivial-structure info for `declName`; see `compileDecls`. -/
public def Irrelevant.setHasTrivialStructure?
    (infoExt : MapDeclarationExtension (Option TrivialStructureInfo))
    (trivialType : Expr → MetaM Bool) (declName : Name) : CoreM Unit := do
  unless (infoExt.find? (← getEnv) declName).isSome do
    modifyEnv (infoExt.insert · declName (← computeHasTrivialStructure? trivialType declName))

/-- Trivial-structure info for `declName` (`none` for non-inductives); requires `compileDecls` to
have been run for inductive `declName`. -/
public def Irrelevant.hasTrivialStructure?
    (infoExt : MapDeclarationExtension (Option TrivialStructureInfo))
    (declName : Name) : CoreM (Option TrivialStructureInfo) := do
  if isRuntimeBuiltinType declName then return none
  let .inductInfo _ ← getConstInfo declName | return none
  let some info? := infoExt.find? (← getEnv) declName
    | throwError "`{declName}` was not compiled; `compileDecls` must run on inductive types first"
  return info?

end Lean.Compiler.LCNF
