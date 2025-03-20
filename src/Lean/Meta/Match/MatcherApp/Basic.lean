/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Match.MatcherInfo

namespace Lean.Meta

structure MatcherApp where
  matcherName   : Name
  matcherLevels : Array Level
  uElimPos?     : Option Nat
  discrInfos    : Array Match.DiscrInfo
  params        : Array Expr
  motive        : Expr
  discrs        : Array Expr
  altNumParams  : Array Nat
  alts          : Array Expr
  remaining     : Array Expr

/--
Recognizes if `e` is a matcher application, and destructs it into the `MatcherApp` data structure.

This can optionally also treat `casesOn` recursor applications as a special case
of matcher applications.
-/
def matchMatcherApp? [Monad m] [MonadEnv m] [MonadError m] (e : Expr) (alsoCasesOn := false) :
    m (Option MatcherApp) := do
  if let .const declName declLevels := e.getAppFn then
    if let some info ← getMatcherInfo? declName then
      let args := e.getAppArgs
      if args.size < info.arity then
        return none
      return some {
        matcherName   := declName
        matcherLevels := declLevels.toArray
        uElimPos?     := info.uElimPos?
        discrInfos    := info.discrInfos
        params        := args.extract 0 info.numParams
        motive        := args[info.getMotivePos]!
        discrs        := args[info.numParams + 1 : info.numParams + 1 + info.numDiscrs]
        altNumParams  := info.altNumParams
        alts          := args[info.numParams + 1 + info.numDiscrs : info.numParams + 1 + info.numDiscrs + info.numAlts]
        remaining     := args[info.numParams + 1 + info.numDiscrs + info.numAlts : args.size]
      }

    if alsoCasesOn && isCasesOnRecursor (← getEnv) declName then
      let indName := declName.getPrefix
      let .inductInfo info ← getConstInfo indName | return none
      let args := e.getAppArgs
      unless args.size >= info.numParams + 1 /- motive -/ + info.numIndices + 1 /- major -/ + info.numCtors do return none
      let params     := args[:info.numParams]
      let motive     := args[info.numParams]!
      let discrs     := args[info.numParams + 1 : info.numParams + 1 + info.numIndices + 1]
      let discrInfos := .replicate (info.numIndices + 1) {}
      let alts       := args[info.numParams + 1 + info.numIndices + 1 : info.numParams + 1 + info.numIndices + 1 + info.numCtors]
      let remaining  := args[info.numParams + 1 + info.numIndices + 1 + info.numCtors :]
      let uElimPos?  := if info.levelParams.length == declLevels.length then none else some 0
      let mut altNumParams := #[]
      for ctor in info.ctors do
        let .ctorInfo ctorInfo ← getConstInfo ctor | unreachable!
        altNumParams := altNumParams.push ctorInfo.numFields
      return some {
        matcherName   := declName
        matcherLevels := declLevels.toArray
        uElimPos?, discrInfos, params, motive, discrs, alts, remaining, altNumParams
      }

  return none

def MatcherApp.toExpr (matcherApp : MatcherApp) : Expr :=
  let result := mkAppN (mkConst matcherApp.matcherName matcherApp.matcherLevels.toList) matcherApp.params
  let result := mkApp result matcherApp.motive
  let result := mkAppN result matcherApp.discrs
  let result := mkAppN result matcherApp.alts
  mkAppN result matcherApp.remaining

end Lean.Meta
