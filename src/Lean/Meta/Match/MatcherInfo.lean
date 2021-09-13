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

def MatcherInfo.getFirstDiscrPos (info : MatcherInfo) : Nat :=
  info.numParams + 1

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

def getMatcherInfoCore? (env : Environment) (declName : Name) : Option MatcherInfo :=
  Match.Extension.getMatcherInfo? env declName

def getMatcherInfo? [Monad m] [MonadEnv m] (declName : Name) : m (Option MatcherInfo) :=
  return getMatcherInfoCore? (← getEnv) declName

@[export lean_is_matcher]
def isMatcherCore (env : Environment) (declName : Name) : Bool :=
  getMatcherInfoCore? env declName |>.isSome

def isMatcher [Monad m] [MonadEnv m] (declName : Name) : m Bool :=
  return isMatcherCore (← getEnv) declName

def isMatcherAppCore? (env : Environment) (e : Expr) : Option MatcherInfo :=
  let fn := e.getAppFn
  if fn.isConst then
    if let some matcherInfo := getMatcherInfoCore? env fn.constName! then
      if e.getAppNumArgs ≥ matcherInfo.arity then some matcherInfo else none
    else
      none
  else
    none

def isMatcherAppCore (env : Environment) (e : Expr) : Bool :=
  isMatcherAppCore? env e |>.isSome

def isMatcherApp [Monad m] [MonadEnv m] (e : Expr) : m Bool :=
  return isMatcherAppCore (← getEnv) e

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

def matchMatcherApp? [Monad m] [MonadEnv m] (e : Expr) : m (Option MatcherApp) := do
  match e.getAppFn with
  | Expr.const declName declLevels _ =>
    match (← getMatcherInfo? declName) with
    | none => return none
    | some info =>
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
