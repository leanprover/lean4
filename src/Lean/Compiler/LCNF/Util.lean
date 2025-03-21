/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Data.FloatArray.Basic
import Lean.CoreM
import Lean.MonadEnv
import Lean.Util.Recognizers

namespace Lean.Compiler.LCNF
/--
Return `true` if `mdata` should be preserved.
Right now, we don't preserve any `MData`, but this may
change in the future when we add support for debugging information
-/
def isCompilerRelevantMData (_mdata : MData) : Bool :=
  false

/--
Return `true` if `e` is a `lcCast` application.
-/
def isLcCast? (e : Expr) : Option Expr :=
  if e.isAppOfArity ``lcCast 3 then
    some e.appArg!
  else
    none

/--
Store information about `casesOn` declarations.

We treat them uniformly in the code generator.
-/
structure CasesInfo where
  declName     : Name
  arity        : Nat
  numParams    : Nat
  discrPos     : Nat
  altsRange    : Std.Range
  altNumParams : Array Nat
  motivePos    : Nat

def CasesInfo.numAlts (c : CasesInfo) : Nat :=
  c.altNumParams.size

private def getCasesOnInductiveVal? (declName : Name) : CoreM (Option InductiveVal) := do
  unless isCasesOnRecursor (← getEnv) declName do return none
  let .inductInfo val ← getConstInfo declName.getPrefix | return none
  return some val

def getCasesInfo? (declName : Name) : CoreM (Option CasesInfo) := do
  let some val ← getCasesOnInductiveVal? declName | return none
  let numParams    := val.numParams
  let motivePos    := numParams
  let arity        := numParams + 1 /- motive -/ + val.numIndices + 1 /- major -/ + val.numCtors
  let discrPos     := numParams + 1 /- motive -/ + val.numIndices
  -- We view indices as discriminants
  let altsRange    := [discrPos + 1:arity]
  let altNumParams ← val.ctors.toArray.mapM fun ctor => do
    let .ctorInfo ctorVal ← getConstInfo ctor | unreachable!
    return ctorVal.numFields
  return some { declName, numParams, motivePos, arity, discrPos, altsRange, altNumParams }

def isCasesApp? (e : Expr) : CoreM (Option CasesInfo) := do
  let .const declName _ := e.getAppFn | return none
  if let some info ← getCasesInfo? declName then
    assert! info.arity == e.getAppNumArgs
    return some info
  else
    return none

def getCtorArity? (declName : Name) : CoreM (Option Nat) := do
  let .ctorInfo val ← getConstInfo declName | return none
  return val.numParams + val.numFields

/--
List of types that have builtin runtime support
-/
def builtinRuntimeTypes : List Name := [
  ``String,
  ``UInt8, ``UInt16, ``UInt32, ``UInt64, ``USize,
  ``Float, ``Float32,
  ``Thunk, ``Task,
  ``Array, ``ByteArray, ``FloatArray,
  ``Nat, ``Int
]

/--
Return `true` iff `declName` is the name of a type with builtin support in the runtime.
-/
def isRuntimeBultinType (declName : Name) : Bool :=
  builtinRuntimeTypes.contains declName

end Lean.Compiler.LCNF
