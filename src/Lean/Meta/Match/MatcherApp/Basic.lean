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
  unless e.isApp do return none
  if let .const declName declLevels := e.getAppFn then
    if let some info ← getMatcherInfo? declName (alsoCasesOn := alsoCasesOn) then
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
        discrs        := args[(info.numParams + 1)...(info.numParams + 1 + info.numDiscrs)]
        altNumParams  := info.altNumParams
        alts          := args[(info.numParams + 1 + info.numDiscrs)...(info.numParams + 1 + info.numDiscrs + info.numAlts)]
        remaining     := args[(info.numParams + 1 + info.numDiscrs + info.numAlts)...args.size]
      }

  return none

def MatcherApp.toMatcherInfo (matcherApp : MatcherApp) : MatcherInfo where
  uElimPos?     := matcherApp.uElimPos?
  discrInfos    := matcherApp.discrInfos
  numParams     := matcherApp.params.size
  numDiscrs     := matcherApp.discrs.size
  altNumParams  := matcherApp.altNumParams

def MatcherApp.toExpr (matcherApp : MatcherApp) : Expr :=
  let result := mkAppN (mkConst matcherApp.matcherName matcherApp.matcherLevels.toList) matcherApp.params
  let result := mkApp result matcherApp.motive
  let result := mkAppN result matcherApp.discrs
  let result := mkAppN result matcherApp.alts
  mkAppN result matcherApp.remaining

end Lean.Meta
