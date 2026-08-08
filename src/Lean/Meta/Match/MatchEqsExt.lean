/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Meta.Match.Basic
public import Lean.Meta.Match.MatcherInfo
import Lean.Meta.Eqns

public section

namespace Lean.Meta.Match

structure MatchEqns where
  eqnNames             : Array Name
  splitterName         : Name
  splitterMatchInfo    : MatcherInfo
deriving Inhabited, Repr

def MatchEqns.size (e : MatchEqns) : Nat :=
  e.eqnNames.size

structure MatchEqnsExtState where
  map : PHashMap Name MatchEqns := {}
  eqns : PHashSet Name := {}
  deriving Inhabited

/- We generate the equations and splitter on demand, and do not save them on .olean files. -/
builtin_initialize matchEqnsExt : EnvExtension MatchEqnsExtState ←
  -- consulted during match-equation realization, which can happen inside a resolution search;
  -- a mere name mapping for realized equation theorems (monotone)
  -- Using `local` allows us to use the extension in `realizeConst` without specifying `replay?`.
  -- The resulting state can still be accessed on the generated declarations using `.asyncEnv`;
  -- see below. Covered: realized on demand, so reads never observe result-relevant absence,
  -- and registered equations are write-stability-guarded.
  registerEnvExtension (pure {}) (asyncMode := .local) (synthCovered := true)

def registerMatchEqns (matchDeclName : Name) (matchEqns : MatchEqns) : CoreM Unit := do
  modifyEnv fun env => matchEqnsExt.modifyState env fun { map, eqns } => {
    eqns := matchEqns.eqnNames.foldl (init := eqns) fun eqns eqn => eqns.insert eqn
    -- write-stability guard; see `MapDeclarationExtension.insert`. Re-registration with the
    -- same equations is idempotent.
    map :=
      match map.find? matchDeclName with
      | some prev =>
        if prev.eqnNames != matchEqns.eqnNames then
          panic! s!"match equations for `{matchDeclName}` are already registered"
        else
          map
      | none => map.insert matchDeclName matchEqns
  }

/-
Forward definition of `getEquationsForImpl`.
We want to use `getEquationsFor` in the simplifier,
getEquationsFor` depends on `mkEquationsFor` which uses the simplifier.
-/
set_option compiler.ignoreBorrowAnnotation true in
@[extern "lean_get_match_equations_for"]
opaque getEquationsFor (matchDeclName : Name) : MetaM MatchEqns

/-
Forward definition of `genMatchCongrEqnsImpl`.
-/
set_option compiler.ignoreBorrowAnnotation true in
@[extern "lean_get_congr_match_equations_for"]
opaque genMatchCongrEqns (matchDeclName : Name) : MetaM (Array Name)

/--
Returns `true` if `declName` is the name of a `match` equational theorem.
-/
def isMatchEqnTheorem (env : Environment) (declName : Name) : Bool := Id.run do
  -- avoid blocking on async decls whose names look nothing like matchers
  let .str _ s := declName.eraseMacroScopes | return false
  if !isEqnLikeSuffix s then
    return false
  (matchEqnsExt.getState (asyncMode := .async .asyncEnv) (asyncDecl := declName) env).eqns.contains declName

end Lean.Meta.Match
