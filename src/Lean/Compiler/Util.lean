/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Compiler.CompilerM
import Lean.Meta.Match.MatcherInfo

namespace Lean.Compiler

/--
Return `true` if `mdata` should be preserved.
Right now, we don't preserve any `MData`, but this may
change in the future when we add support for debugging information
-/
def isCompilerRelevantMData (_mdata : MData) : Bool :=
  false

/--
Return `true` if `e` is a `lcProof` application.
Recall that we use `lcProof` to erase all nested proofs.
-/
def isLCProof (e : Expr) : Bool :=
  e.isAppOfArity ``lcProof 1

/--
Return `true` if `e` is a `lcUnreachable` application.
-/
def isLcUnreachable (e : Expr) : Bool :=
  e.isAppOfArity ``lcUnreachable 1

/--
Return `true` if `e` is a `lcCast` application.
-/
def isLcCast? (e : Expr) : Option Expr :=
  if e.isAppOfArity ``lcCast 3 then
    some e.appArg!
  else
    none

/-- Create `lcProof p` -/
def mkLcProof (p : Expr) :=
  mkApp (mkConst ``lcProof []) p

/-- Create `lcUnreachable type` -/
def mkLcUnreachable (type : Expr) : CompilerM Expr := do
  liftMetaM do
    let u ← Meta.getLevel type
    return .app (.const ``lcUnreachable [u]) type

/-- Create `lcCast expectedType e : expectedType` -/
def mkLcCast (e : Expr) (expectedType : Expr) : CompilerM Expr := do
  liftMetaM do
    let type ← Meta.inferType e
    let u ← Meta.getLevel type
    let v ← Meta.getLevel expectedType
    return mkApp3 (.const ``lcCast [u, v]) type expectedType e

/--
Store information about `matcher` and `casesOn` declarations.

We treat them uniformly in the code generator.
-/
structure CasesInfo where
  arity        : Nat
  discrsRange  : Std.Range
  altsRange    : Std.Range
  altNumParams : Array Nat
  motivePos    : Nat

private def getCasesOnInductiveVal? (declName : Name) : CoreM (Option InductiveVal) := do
  unless isCasesOnRecursor (← getEnv) declName do return none
  let .inductInfo val ← getConstInfo declName.getPrefix | return none
  return some val

private def getCasesOnInfo? (declName : Name) : CoreM (Option CasesInfo) := do
  let some val ← getCasesOnInductiveVal? declName | return none
  let motivePos    := val.numParams
  let arity        := val.numIndices + val.numParams + 1 /- motive -/ + 1 /- major -/ + val.numCtors
  let majorPos     := val.numIndices + val.numParams + 1 /- motive -/
  let discrsRange  := { start := majorPos, stop := majorPos + 1 }
  let altsRange    := { start := majorPos + 1, stop := arity }
  let altNumParams ← val.ctors.toArray.mapM fun ctor => do
    let .ctorInfo ctorVal ← getConstInfo ctor | unreachable!
    return ctorVal.numFields
  return some { motivePos, arity, discrsRange, altsRange, altNumParams }

def getCasesInfo? (declName : Name) : CoreM (Option CasesInfo) := do
  if let some matcherInfo ← Meta.getMatcherInfo? declName then
    return some {
      motivePos    := matcherInfo.getMotivePos
      arity        := matcherInfo.arity
      discrsRange  := matcherInfo.getDiscrRange
      altsRange    := matcherInfo.getAltRange
      altNumParams := matcherInfo.altNumParams
    }
  else
    getCasesOnInfo? declName

def isCasesApp? (e : Expr) : CoreM (Option CasesInfo) := do
  let .const declName _ := e.getAppFn | return none
  if let some info ← getCasesInfo? declName then
    assert! info.arity == e.getAppNumArgs
    return some info
  else
    return none

def updateMotive (casesInfo : CasesInfo) (args : Array Expr) (newResultingType : Expr) : MetaM (Array Expr) := do
  -- TODO: make it more robust, it is assuming the motive is eta-expanded
  args.modifyM casesInfo.motivePos fun motive => do
    Meta.lambdaTelescope motive fun xs _ => Meta.mkLambdaFVars xs newResultingType

def getCtorArity? (declName : Name) : CoreM (Option Nat) := do
  let .ctorInfo val ← getConstInfo declName | return none
  return val.numParams + val.numFields

/--
List of types that have builtin runtime support
-/
def builtinRuntimeTypes : List Name := [
  ``String,
  ``UInt8, ``UInt16, ``UInt32, ``UInt64, ``USize,
  ``Float,
  ``Thunk, ``Task,
  ``Array, ``ByteArray, ``FloatArray,
  ``Nat, ``Int
]

/--
Return `true` iff `declName` is the name of a type with builtin support in the runtime.
-/
def isRuntimeBultinType (declName : Name) : Bool :=
  builtinRuntimeTypes.contains declName

end Lean.Compiler
