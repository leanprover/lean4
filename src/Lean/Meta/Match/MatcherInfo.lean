/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Meta.Basic

public section

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

@[expose] def MatcherInfo.numAlts (info : MatcherInfo) : Nat :=
  info.altNumParams.size

def MatcherInfo.arity (info : MatcherInfo) : Nat :=
  info.numParams + 1 + info.numDiscrs + info.numAlts

def MatcherInfo.getFirstDiscrPos (info : MatcherInfo) : Nat :=
  info.numParams + 1

def MatcherInfo.getDiscrRange (info : MatcherInfo) : Std.Rco Nat :=
  info.getFirstDiscrPos...(info.getFirstDiscrPos + info.numDiscrs)

def MatcherInfo.getFirstAltPos (info : MatcherInfo) : Nat :=
  info.numParams + 1 + info.numDiscrs

def MatcherInfo.getAltRange (info : MatcherInfo) : Std.Rco Nat :=
  info.getFirstAltPos...(info.getFirstAltPos + info.numAlts)

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
    asyncMode     := .async .mainEnv
    exportEntriesFnEx? := some fun env _ entries _ =>
      -- Do not export info for private defs
      entries.filter (env.contains (skipRealize := false) ·.name) |>.toArray
  }

def addMatcherInfo (env : Environment) (matcherName : Name) (info : MatcherInfo) : Environment :=
  let _ : Inhabited Environment := ⟨env⟩
  extension.addEntry (asyncDecl := matcherName) env { name := matcherName, info := info }

def getMatcherInfo? (env : Environment) (declName : Name) : Option MatcherInfo := do
  -- avoid blocking on async decls whose names look nothing like matchers
  let .str _ s := declName.eraseMacroScopes | none
  guard <| s.startsWith "match_"
  (extension.getState (asyncDecl := declName) env).map.find? declName

end Extension

def addMatcherInfo [Monad m] [MonadEnv m] (matcherName : Name) (info : MatcherInfo) : m Unit :=
  modifyEnv fun env => Extension.addMatcherInfo env matcherName info

end Match

export Match (MatcherInfo)

def getMatcherInfoForCasesOn (env : Environment) (declName : Name) : Option MatcherInfo := do
  let indName := declName.getPrefix
  let cinfo ← env.findConstVal? declName
  let .inductInfo info ← env.find? indName | none
  let discrInfos := .replicate (info.numIndices + 1) {}
  let uElimPos?  := if info.levelParams.length == cinfo.levelParams.length then none else some 0
  let mut altNumParams := #[]
  for ctor in info.ctors do
    let .ctorInfo ctorInfo ← env.find? ctor | none
    altNumParams := altNumParams.push ctorInfo.numFields
  return {
    numParams := info.numParams
    numDiscrs := info.numIndices + 1
    uElimPos?, discrInfos,
    altNumParams
  }

def getMatcherInfoCore? (env : Environment) (declName : Name) (alsoCasesOn : Bool := false) : Option MatcherInfo :=
  if alsoCasesOn && isCasesOnRecursor env declName then
      getMatcherInfoForCasesOn env declName
  else
    Match.Extension.getMatcherInfo? env declName

def getMatcherInfo? [Monad m] [MonadEnv m] (declName : Name) (alsoCasesOn := false) : m (Option MatcherInfo) :=
  return getMatcherInfoCore? (← getEnv) declName (alsoCasesOn := alsoCasesOn)

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
