/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Basic

namespace Lean.Meta
namespace Match

/--
A "matcher" auxiliary declaration has the following structure:
- `numParams` parameters
- motive
- `numDiscrs` discriminators (aka major premises)
- `altNumParams.size` alternatives (aka minor premises) where alternative `i` has `altNumParams[i]` parameters
- `uElimPos?` is `some pos` when the matcher can eliminate in different universe levels, and
   `pos` is the position of the universe level parameter that specifies the elimination universe.
   It is `none` if the matcher only eliminates into `Prop`. -/
structure MatcherInfo where
  numParams : Nat
  numDiscrs : Nat
  altNumParams : Array Nat
  uElimPos? : Option Nat

def MatcherInfo.numAlts (info : MatcherInfo) : Nat :=
  info.altNumParams.size

def MatcherInfo.arity (info : MatcherInfo) : Nat :=
  info.numParams + 1 + info.numDiscrs + info.numAlts

def MatcherInfo.getMotivePos (info : MatcherInfo) : Nat :=
  info.numParams
namespace Extension

structure Entry where
  name : Name
  info : MatcherInfo

structure State where
  map : SMap Name MatcherInfo := {}

instance : Inhabited State := ⟨{}⟩

def State.addEntry (s : State) (e : Entry) : State := { s with map  := s.map.insert e.name e.info }
def State.switch (s : State) : State :=  { s with map := s.map.switch }

builtin_initialize extension : SimplePersistentEnvExtension Entry State ←
  registerSimplePersistentEnvExtension {
    name          := `matcher
    addEntryFn    := State.addEntry
    addImportedFn := fun es => (mkStateFromImportedEntries State.addEntry {} es).switch
  }

def addMatcherInfo (env : Environment) (matcherName : Name) (info : MatcherInfo) : Environment :=
  extension.addEntry env { name := matcherName, info := info }

def getMatcherInfo? (env : Environment) (declName : Name) : Option MatcherInfo :=
  (extension.getState env).map.find? declName

end Extension

def addMatcherInfo (matcherName : Name) (info : MatcherInfo) : MetaM Unit :=
  modifyEnv fun env => Extension.addMatcherInfo env matcherName info

end Match

export Match (MatcherInfo)

def getMatcherInfo? [Monad m] [MonadEnv m] (declName : Name) : m (Option MatcherInfo) :=
  return Match.Extension.getMatcherInfo? (← getEnv) declName

def isMatcher [Monad m] [MonadEnv m] (declName : Name) : m Bool :=
  return (← getMatcherInfo? declName).isSome

structure MatcherApp where
  matcherName   : Name
  matcherLevels : Array Level
  uElimPos?     : Option Nat
  params        : Array Expr
  motive        : Expr
  discrs        : Array Expr
  altNumParams  : Array Nat
  alts          : Array Expr
  remaining     : Array Expr

def matchMatcherApp? (e : Expr) : MetaM (Option MatcherApp) :=
  match e.getAppFn with
  | Expr.const declName declLevels _ => do
    let some info ← getMatcherInfo? declName | pure none
    let args := e.getAppArgs
    if args.size < info.arity then
      return none
    else
      return some {
        matcherName   := declName
        matcherLevels := declLevels.toArray
        uElimPos?     := info.uElimPos?
        params        := args.extract 0 info.numParams
        motive        := args[info.getMotivePos]
        discrs        := args[info.numParams + 1 : info.numParams + 1 + info.numDiscrs]
        altNumParams  := info.altNumParams
        alts          := args[info.numParams + 1 + info.numDiscrs : info.numParams + 1 + info.numDiscrs + info.numAlts]
        remaining     := args[info.numParams + 1 + info.numDiscrs + info.numAlts : args.size]
      }
  | _ => return none

def MatcherApp.toExpr (matcherApp : MatcherApp) : Expr :=
  let result := mkAppN (mkConst matcherApp.matcherName matcherApp.matcherLevels.toList) matcherApp.params
  let result := mkApp result matcherApp.motive
  let result := mkAppN result matcherApp.discrs
  let result := mkAppN result matcherApp.alts
  mkAppN result matcherApp.remaining

end Lean.Meta
