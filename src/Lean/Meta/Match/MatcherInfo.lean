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
  [info.getFirstDiscrPos : info.getFirstDiscrPos + info.numDiscrs]

def MatcherInfo.getFirstAltPos (info : MatcherInfo) : Nat :=
  info.numParams + 1 + info.numDiscrs

def MatcherInfo.getAltRange (info : MatcherInfo) : Std.Range :=
  [info.getFirstAltPos : info.getFirstAltPos + info.numAlts]

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
    asyncMode     := .async
  }

def addMatcherInfo (env : Environment) (matcherName : Name) (info : MatcherInfo) : Environment :=
  let _ : Inhabited Environment := ⟨env⟩
  assert! env.asyncMayContain matcherName
  extension.addEntry env { name := matcherName, info := info }

def getMatcherInfo? (env : Environment) (declName : Name) : Option MatcherInfo :=
  (extension.findStateAsync env declName).map.find? declName

end Extension

def addMatcherInfo [Monad m] [MonadEnv m] (matcherName : Name) (info : MatcherInfo) : m Unit :=
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

end Lean.Meta
