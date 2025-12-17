/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/

module

prelude
public import Lean.Meta.Match.Match
public import Lean.Meta.Match.MatchEqsExt
import Lean.Meta.Tactic.Refl
import Lean.Meta.Tactic.Delta
import Lean.Meta.Tactic.SplitIf
import Lean.Meta.Tactic.CasesOnStuckLHS
import Lean.Meta.Match.SimpH
import Lean.Meta.Match.AltTelescopes
import Lean.Meta.Match.NamedPatterns
import Lean.Meta.SplitSparseCasesOn
import Lean.Meta.Tactic.Grind.Main
import Lean.Meta.Match.SolveOverlap

namespace Lean.Meta.Match

-- TODO: Turn this true once it works
-- Known problem so far: injectivity of `Int` constructors (test issue10775)
register_builtin_option debug.Meta.Match.MatchEqs.unrestrictedGrind : Bool := {
  defValue := true
  descr := "When proving match equations, run `grind` in the unrestricted configuration. \
    Useful to debug match equation failures that may be due to a too restrictive grind configuration."
}


private def getMatchEqsGrindParams : MetaM Grind.Params := do
  let config :=
    if debug.Meta.Match.MatchEqs.unrestrictedGrind.get (← getOptions) then
      {}
    else
      { ({} : Grind.NoopConfig) with
        ematch := 1000    -- We only have a fixed sets of theorem to ematch, declared below
        gen := 1000       -- Allow deep propagation of equalities
        etaStruct := true -- Needed for `x = (x' : Unit)`
      }
  let mut params ← Grind.mkParams config
  let s ← Grind.getEMatchTheorems
  let thms := s.find (.decl ``Nat.hasNotBit_eq)
  let thms := thms ++ s.find (.decl `Nat.ctorIdx_zero)
  let thms := thms ++ s.find (.decl `Nat.ctorIdx_succ)
  for thm in thms do
    params := { params with extra := params.extra.push thm }
  return params


/--
A trimmed down version of `grind` for use in `MatchEq`. Handles only

* equality propagation
* injectivity of constructors (homogeneous and heterogeneous),
* `Nat.hasNotBit` and `Nat.ctorIdx`
-/
public def grind (mvarId : MVarId) : MetaM Unit := do
  let result ← Grind.main mvarId (← getMatchEqsGrindParams)
  if result.hasFailed then
    trace[Meta.Match.matchEqs] "`grind` failed\n{← result.toMessageData}"
    throwError "grind failed"

end Lean.Meta.Match
