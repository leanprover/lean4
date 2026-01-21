/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Meta.Match.MatcherInfo

public section

namespace Lean.Meta

structure MatcherApp extends Match.MatcherInfo where
  matcherName   : Name
  matcherLevels : Array Level
  params        : Array Expr
  motive        : Expr
  discrs        : Array Expr
  alts          : Array Expr
  remaining     : Array Expr
  deriving Inhabited

/--
Recognizes if `e` is a matcher application, and destructs it into the `MatcherApp` data structure.

This can optionally also treat `casesOn` recursor applications as a special case
of matcher applications.
-/
def matchMatcherApp? [Monad m] [MonadEnv m] [MonadError m] (e : Expr) (alsoCasesOn := false) :
    m (Option MatcherApp) := do
  unless e.isApp do return none
  if let .const declName declLevels := e.getAppFn then
    if let some info ← getMatcherInfo? declName then
      let args := e.getAppArgs
      if args.size < info.arity then
        return none
      return some {
        info with
        matcherName   := declName
        matcherLevels := declLevels.toArray
        params        := args.extract 0 info.numParams
        motive        := args[info.getMotivePos]!
        discrs        := args[(info.numParams + 1)...(info.numParams + 1 + info.numDiscrs)]
        alts          := args[(info.numParams + 1 + info.numDiscrs)...(info.numParams + 1 + info.numDiscrs + info.numAlts)]
        remaining     := args[(info.numParams + 1 + info.numDiscrs + info.numAlts)...args.size]
      }

    if alsoCasesOn && isCasesOnRecursor (← getEnv) declName then
      let indName := declName.getPrefix
      let .inductInfo info ← getConstInfo indName | return none
      let args := e.getAppArgs
      unless args.size >= info.numParams + 1 /- motive -/ + info.numIndices + 1 /- major -/ + info.numCtors do return none
      let params     := args[*...info.numParams]
      let motive     := args[info.numParams]!
      let discrs     := args[(info.numParams + 1)...(info.numParams + 1 + info.numIndices + 1)]
      let discrInfos := .replicate (info.numIndices + 1) {}
      let alts       := args[(info.numParams + 1 + info.numIndices + 1)...(info.numParams + 1 + info.numIndices + 1 + info.numCtors)]
      let remaining  := args[(info.numParams + 1 + info.numIndices + 1 + info.numCtors)...*]
      let uElimPos?  := if info.levelParams.length == declLevels.length then none else some 0
      let altInfos   ← info.ctors.toArray.mapM fun ctor => do
        let .ctorInfo ctorInfo ← getConstInfo ctor | panic! "expected constructor"
        return { numFields := ctorInfo.numFields, numOverlaps := 0, hasUnitThunk := false  : Match.AltParamInfo}
      return some {
        numParams := params.size
        numDiscrs := discrs.size
        matcherName   := declName
        matcherLevels := declLevels.toArray
        uElimPos?, discrInfos, params, motive, discrs, alts, remaining, altInfos
        overlaps := {} -- CasesOn constructor have no overlaps
      }

  return none

def MatcherApp.altNumParams (matcherApp : MatcherApp) := matcherApp.toMatcherInfo.altNumParams

def MatcherApp.toExpr (matcherApp : MatcherApp) : Expr :=
  let result := mkAppN (mkConst matcherApp.matcherName matcherApp.matcherLevels.toList) matcherApp.params
  let result := mkApp result matcherApp.motive
  let result := mkAppN result matcherApp.discrs
  let result := mkAppN result matcherApp.alts
  mkAppN result matcherApp.remaining

end Lean.Meta
