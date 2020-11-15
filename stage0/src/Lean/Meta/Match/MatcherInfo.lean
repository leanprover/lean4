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
structure MatcherInfo :=
  (numParams : Nat)
  (numDiscrs : Nat)
  (altNumParams : Array Nat)
  (uElimPos? : Option Nat)

def MatcherInfo.numAlts (matcherInfo : MatcherInfo) : Nat :=
  matcherInfo.altNumParams.size

namespace Extension

structure Entry :=
  (name : Name)
  (info : MatcherInfo)

structure State :=
  (map : SMap Name MatcherInfo := {})

instance : Inhabited State := ⟨{}⟩

def State.addEntry (s : State) (e : Entry) : State := { s with map  := s.map.insert e.name e.info }
def State.switch (s : State) : State :=  { s with map := s.map.switch }

builtin_initialize extension : SimplePersistentEnvExtension Entry State ←
  registerSimplePersistentEnvExtension {
    name          := `matcher,
    addEntryFn    := State.addEntry,
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

def getMatcherInfo? (declName : Name) : MetaM (Option MatcherInfo) := do
  let env ← getEnv
  pure $ Match.Extension.getMatcherInfo? env declName

def isMatcher (declName : Name) : MetaM Bool := do
  let info? ← getMatcherInfo? declName
  pure info?.isSome

structure MatcherApp :=
  (matcherName   : Name)
  (matcherLevels : Array Level)
  (uElimPos?     : Option Nat)
  (params        : Array Expr)
  (motive        : Expr)
  (discrs        : Array Expr)
  (altNumParams  : Array Nat)
  (alts          : Array Expr)
  (remaining     : Array Expr)

def matchMatcherApp? (e : Expr) : MetaM (Option MatcherApp) :=
  match e.getAppFn with
  | Expr.const declName declLevels _ => do
    let some info ← getMatcherInfo? declName | pure none
    let args := e.getAppArgs
    if args.size < info.numParams + 1 + info.numDiscrs + info.numAlts then pure none
    else
      pure $ some {
        matcherName   := declName,
        matcherLevels := declLevels.toArray,
        uElimPos?     := info.uElimPos?,
        params        := args.extract 0 info.numParams,
        motive        := args.get! info.numParams,
        discrs        := args.extract (info.numParams + 1) (info.numParams + 1 + info.numDiscrs),
        altNumParams  := info.altNumParams,
        alts          := args.extract (info.numParams + 1 + info.numDiscrs) (info.numParams + 1 + info.numDiscrs + info.numAlts),
        remaining     := args.extract (info.numParams + 1 + info.numDiscrs + info.numAlts) args.size
      }
  | _ => pure none

def MatcherApp.toExpr (matcherApp : MatcherApp) : Expr :=
  let result := mkAppN (mkConst matcherApp.matcherName matcherApp.matcherLevels.toList) matcherApp.params
  let result := mkApp result matcherApp.motive
  let result := mkAppN result matcherApp.discrs
  let result := mkAppN result matcherApp.alts
  mkAppN result matcherApp.remaining

end Lean.Meta
