/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Init.Data.FloatArray.Basic
public import Lean.CoreM
public import Lean.Util.Recognizers
import Lean.Meta.Basic

public section

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

inductive CasesAltInfo where
  | ctor (ctorName : Name) (numFields : Nat) : CasesAltInfo
  | default (numHyps : Nat) : CasesAltInfo
deriving Inhabited

/--
Store information about `casesOn` declarations.

We treat them uniformly in the code generator.
-/
structure CasesInfo where
  declName     : Name
  indName      : Name
  arity        : Nat
  discrPos     : Nat
  altsRange    : Std.Rco Nat
  altNumParams : Array CasesAltInfo

def CasesInfo.numAlts (c : CasesInfo) : Nat :=
  c.altNumParams.size

private def getCasesOnInductiveVal? (declName : Name) : CoreM (Option InductiveVal) := do
  unless isCasesOnRecursor (← getEnv) declName do return none
  let .inductInfo val ← getConstInfo declName.getPrefix | return none
  return some val

def getCasesInfo? (declName : Name) : CoreM (Option CasesInfo) := do
  let some val ← getCasesOnInductiveVal? declName | return none
  let indName := val.name
  let numParams    := val.numParams
  let arity        := numParams + 1 /- motive -/ + val.numIndices + 1 /- major -/ + val.numCtors
  let discrPos     := numParams + 1 /- motive -/ + val.numIndices
  -- We view indices as discriminants
  let altsRange    := (discrPos + 1)...arity
  let altNumParams ← val.ctors.toArray.mapM fun ctor => do
    let .ctorInfo ctorVal ← getConstInfo ctor | unreachable!
    return .ctor ctor ctorVal.numFields
  return some { declName, indName, arity, discrPos, altsRange, altNumParams }

open Meta in
def getSparseCasesInfo? (declName : Name) : CoreM (Option CasesInfo) := do
  unless isSparseCasesOn (← getEnv) declName do return none
  -- We could store the information in the sparseCasesOnExt, but we might as well recompute it from
  -- the declaration type
  let info ← getConstVal declName
  MetaM.run' <|
    forallTelescope info.type fun xs r => do
      let arity := xs.size
      assert! r.isApp
      assert! r.appArg!.isFVar
      let some discrPos := xs.idxOf? r.appArg! | unreachable!
      let some indName := (← inferType xs[discrPos]!).getAppFn.constName? | unreachable!
      let altsRange := (discrPos + 1)...arity
      let altNumParams ← altsRange.toArray.mapM fun idx => do
        forallTelescope (← inferType xs[idx]!) fun ys mr => do
          assert! mr.isApp
          let motiveArg := mr.appArg!
          if motiveArg.isFVar then
            assert! motiveArg == xs[discrPos]!
            -- This is a catch-all case
            return .default ys.size
          else
            let some ctorName := motiveArg.getAppFn.constName? | unreachable!
            let ctorVal ← getConstInfoCtor ctorName
            return .ctor ctorName ctorVal.numFields
      return some { declName, indName, arity, discrPos, altsRange, altNumParams }


def getCtorArity? (declName : Name) : CoreM (Option Nat) := do
  let .ctorInfo val ← getConstInfo declName | return none
  return val.numParams + val.numFields

/--
List of types that have builtin runtime support
-/
def builtinRuntimeTypes : Array Name := #[
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
def isRuntimeBuiltinType (declName : Name) : Bool :=
  builtinRuntimeTypes.contains declName

end Lean.Compiler.LCNF
