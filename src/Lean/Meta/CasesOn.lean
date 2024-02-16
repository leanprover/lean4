/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.KAbstract
import Lean.Meta.Check
import Lean.Meta.AppBuilder

namespace Lean.Meta

structure CasesOnApp where
  declName     : Name
  us           : List Level
  params       : Array Expr
  motive       : Expr
  indices      : Array Expr
  major        : Expr
  alts         : Array Expr
  altNumParams : Array Nat
  remaining    : Array Expr
  /-- `true` if the `casesOn` can only eliminate into `Prop` -/
  propOnly     : Bool

/-- Return `some c` if `e` is a `casesOn` application. -/
def toCasesOnApp? (e : Expr) : MetaM (Option CasesOnApp) := do
  let f := e.getAppFn
  let .const declName us := f | return none
  unless isCasesOnRecursor (← getEnv) declName do return none
  let indName := declName.getPrefix
  let .inductInfo info ← getConstInfo indName | return none
  let args := e.getAppArgs
  unless args.size >= info.numParams + 1 /- motive -/ + info.numIndices + 1 /- major -/ + info.numCtors do return none
  let params    := args[:info.numParams]
  let motive    := args[info.numParams]!
  let indices   := args[info.numParams + 1 : info.numParams + 1 + info.numIndices]
  let major     := args[info.numParams + 1 + info.numIndices]!
  let alts      := args[info.numParams + 1 + info.numIndices + 1 : info.numParams + 1 + info.numIndices + 1 + info.numCtors]
  let remaining := args[info.numParams + 1 + info.numIndices + 1 + info.numCtors :]
  let propOnly  := info.levelParams.length == us.length
  let mut altNumParams := #[]
  for ctor in info.ctors do
    let .ctorInfo ctorInfo ← getConstInfo ctor | unreachable!
    altNumParams := altNumParams.push ctorInfo.numFields
  return some { declName, us, params, motive, indices, major, alts, remaining, propOnly, altNumParams }

/-- Often when `MatcherApps` are handled, applications of `CasesOn` should get the same treatment.
So `matchMatcherOrCasesOnApp?` generalizes `matchMatcherApp?` to also treat casesOn like matche.
-/
def matchMatcherOrCasesOnApp? (e : Expr) : MetaM (Option MatcherApp) := do
  if let some matcherApp ← matchMatcherApp? e then
    return some matcherApp
  if let some casesOnApp ← toCasesOnApp? e then
    return some {
      matcherName := casesOnApp.declName
      matcherLevels := casesOnApp.us.toArray
      uElimPos? := if casesOnApp.propOnly then none else some 0
      params := casesOnApp.params
      motive := casesOnApp.motive
      discrs := casesOnApp.indices.push casesOnApp.major
      alts := casesOnApp.alts
      remaining := casesOnApp.remaining
      altNumParams := casesOnApp.altNumParams
    }
  return none
end Lean.Meta
