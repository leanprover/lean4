/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Compiler.CompilerM

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


/-- Create `lcProof p` -/
def mkLcProof (p : Expr) :=
  mkApp (mkConst ``lcProof []) p

/-- Create `lcCast expectedType e : expectedType` -/
def mkLcCast (e : Expr) (expectedType : Expr) : CompilerM Expr := do
  liftMetaM do
    let type ← Meta.inferType e
    let u ← Meta.getLevel type
    let v ← Meta.getLevel expectedType
    return mkApp3 (.const ``lcCast [u, v]) type expectedType e

/-- Create `lcUnreachable type` -/
def mkLcUnreachable (type : Expr) : CompilerM Expr := do
  liftMetaM do
    let u ← Meta.getLevel type
    return .app (.const ``lcUnreachable [u]) type

structure CasesOnInfo where
  arity       : Nat
  majorPos    : Nat
  minorsRange : Std.Range
  ctors       : List Name

def getCasesOnInductiveVal? (declName : Name) : CoreM (Option InductiveVal) := do
  unless isCasesOnRecursor (← getEnv) declName do return none
  let .inductInfo val ← getConstInfo declName.getPrefix | return none
  return some val

def getCasesOnInfo? (declName : Name) : CoreM (Option CasesOnInfo) := do
  let some val ← getCasesOnInductiveVal? declName | return none
  let arity       := val.numIndices + val.numParams + 1 /- motive -/ + 1 /- major -/ + val.numCtors
  let majorPos    := val.numIndices + val.numParams + 1 /- motive -/
  let minorsRange := { start := majorPos + 1, stop := arity }
  return some { arity, majorPos, minorsRange, ctors := val.ctors }

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
