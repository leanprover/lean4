/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Basic

namespace Lean.Meta.Match

structure MatchEqns where
  eqnNames             : Array Name
  splitterName         : Name
  splitterAltNumParams : Array Nat
  deriving Inhabited, Repr

def MatchEqns.size (e : MatchEqns) : Nat :=
  e.eqnNames.size

structure MatchEqnsExtState where
  map : PHashMap Name MatchEqns := {}
  deriving Inhabited

/- We generate the equations and splitter on demand, and do not save them on .olean files. -/
builtin_initialize matchEqnsExt : EnvExtension MatchEqnsExtState ←
  registerEnvExtension (pure {})

def registerMatchEqns (matchDeclName : Name) (matchEqns : MatchEqns) : CoreM Unit :=
  modifyEnv fun env => matchEqnsExt.modifyState env fun s => { s with map := s.map.insert matchDeclName matchEqns }

/-
  Forward definition. We want to use `getEquationsFor` in the simplifier,
 `getEquationsFor` depends on `mkEquationsfor` which uses the simplifier. -/
@[extern "lean_get_match_equations_for"]
opaque getEquationsFor (matchDeclName : Name) : MetaM MatchEqns

end Lean.Meta.Match
