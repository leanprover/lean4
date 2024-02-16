/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Basic

namespace Lean.Meta
namespace Match

structure DiscrInfo where
  /-- `some h` if the discriminant is annotated with `h:` -/
  hName? : Option Name := none
  deriving Inhabited

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
  numParams    : Nat
  numDiscrs    : Nat
  altNumParams : Array Nat
  uElimPos?    : Option Nat
  /--
    `discrInfos[i] = { hName? := some h }` if the i-th discriminant was annotated with `h :`.
  -/
  discrInfos   : Array DiscrInfo

def MatcherInfo.numAlts (info : MatcherInfo) : Nat :=
  info.altNumParams.size

def MatcherInfo.arity (info : MatcherInfo) : Nat :=
  info.numParams + 1 + info.numDiscrs + info.numAlts

def MatcherInfo.getFirstDiscrPos (info : MatcherInfo) : Nat :=
  info.numParams + 1

def MatcherInfo.getDiscrRange (info : MatcherInfo) : Std.Range :=
  { start := info.getFirstDiscrPos, stop := info.getFirstDiscrPos + info.numDiscrs }

def MatcherInfo.getFirstAltPos (info : MatcherInfo) : Nat :=
  info.numParams + 1 + info.numDiscrs

def MatcherInfo.getAltRange (info : MatcherInfo) : Std.Range :=
  { start := info.getFirstAltPos, stop := info.getFirstAltPos + info.numAlts }

def MatcherInfo.getMotivePos (info : MatcherInfo) : Nat :=
  info.numParams

def getNumEqsFromDiscrInfos (infos : Array DiscrInfo) : Nat := Id.run do
  let mut r := 0
  for info in infos do
    if info.hName?.isSome then
      r := r + 1
  return r

def MatcherInfo.getNumDiscrEqs (info : MatcherInfo) : Nat :=
  getNumEqsFromDiscrInfos info.discrInfos

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
      let discrInfos := Array.mkArray (info.numIndices + 1) {}
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
