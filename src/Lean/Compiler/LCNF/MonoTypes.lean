/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.InferType
import Lean.Compiler.LCNF.Util
import Lean.Compiler.LCNF.BaseTypes
import Lean.Compiler.LCNF.CompilerM

namespace Lean.Compiler.LCNF

/--
Given a constructor, return a bitmask `m` s.t. `m[i]` is true if field `i` is
computationally relevant.
-/
def getRelevantCtorFields (ctorName : Name) : CoreM (Array Bool) := do
  let .ctorInfo info ← getConstInfo ctorName | unreachable!
  Meta.MetaM.run' do
    Meta.forallTelescopeReducing info.type fun xs _ => do
      let mut result := #[]
      for x in xs[info.numParams:] do
        let type ← Meta.inferType x
        result := result.push !(← Meta.isProp type <||> Meta.isTypeFormerType type)
      return result

/--
We say a structure has a trivial structure if it has not builtin support in the runtime,
it has only one constructor, and this constructor has only one relevant field.
-/
structure TrivialStructureInfo where
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
def hasTrivialStructure? (declName : Name) : CoreM (Option TrivialStructureInfo) := do
  if isRuntimeBultinType declName then return none
  let .inductInfo info ← getConstInfo declName | return none
  if info.isUnsafe || info.isRec then return none
  let [ctorName] := info.ctors | return none
  let mask ← getRelevantCtorFields ctorName
  let mut result := none
  for h : i in [:mask.size] do
    if mask[i] then
      if result.isSome then return none
      result := some { ctorName, fieldIdx := i, numParams := info.numParams }
  return result

def getParamTypes (type : Expr) : Array Expr :=
  go type #[]
where
  go (type : Expr) (r : Array Expr) :=
    match type with
    | .forallE _ d b _ => go b (r.push d)
    | _ => r

/--
Convert a LCNF type from the base phase to the mono phase.

LCNF types in the mono phase do not have dependencies,
and universe levels have been erased.

The type contains only `→` and constants.
-/
partial def toMonoType (type : Expr) : CoreM Expr := do
  let type := type.headBeta
  if type.isErased then
    return erasedExpr
  else if type.isErased then
    return erasedExpr
  else if isTypeFormerType type then
    return erasedExpr
  else match type with
    | .const ..        => visitApp type #[]
    | .app ..          => type.withApp visitApp
    | .forallE _ d b _ => mkArrow (← toMonoType d) (← toMonoType (b.instantiate1 erasedExpr))
    | _                => return erasedExpr
where
  visitApp (f : Expr) (args : Array Expr) : CoreM Expr := do
    match f with
    | .const declName us =>
      if declName == ``Decidable then
        return mkConst ``Bool
      if let some info ← hasTrivialStructure? declName then
        let ctorType ← getOtherDeclBaseType info.ctorName []
        toMonoType (getParamTypes (← instantiateForall ctorType args[:info.numParams]))[info.fieldIdx]!
      else
        let mut result := mkConst declName
        let mut type ← getOtherDeclBaseType declName us
        for arg in args do
          let .forallE _ d b _ := type.headBeta | unreachable!
          let arg := arg.headBeta
          if arg.isErased then
            result := mkApp result arg
          else if d.isErased || d matches .sort _ then
            result := mkApp result (← toMonoType arg)
          else
            result := mkApp result erasedExpr
          type := b.instantiate1 arg
        return result
    | _ => return erasedExpr

/--
State for the environment extension used to save the LCNF mono phase type for declarations
that do not have code associated with them.
Example: constructors, inductive types, foreign functions.
-/
structure MonoTypeExtState where
  /-- The LCNF type for the `mono` phase. -/
  mono : PHashMap Name Expr := {}
  deriving Inhabited

builtin_initialize monoTypeExt : EnvExtension MonoTypeExtState ←
  registerEnvExtension (pure {})

def getOtherDeclMonoType (declName : Name) : CoreM Expr := do
  match monoTypeExt.getState (← getEnv) |>.mono.find? declName with
  | some type => return type
  | none =>
    let type ← toMonoType (← getOtherDeclBaseType declName [])
    modifyEnv fun env => monoTypeExt.modifyState env fun s => { s with mono := s.mono.insert declName type }
    return type

end Lean.Compiler.LCNF
