/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Lean.Meta.Tactic.Convert
import Lean.Elab.Tactic.Congr!

open Lean Meta Tactic Congr!

namespace Lean.Elab.Tactic

@[builtin_tactic «convert»] def evalConvert : Tactic := fun stx =>
  match stx with
  | `(tactic| convert $[$cfg:config]? $[←%$sym]? $term $[using $n]? $[with $ps?*]?) =>
    withMainContext do
      let config ← Congr!.elabConfig (mkOptionalNode cfg)
      let patterns := (Lean.Elab.Tactic.RCases.expandRIntroPats (ps?.getD #[])).toList
      let expectedType ← mkFreshExprMVar (mkSort (← getLevel (← getMainTarget)))
      let (e, gs) ←
        withCollectingNewGoalsFrom (allowNaturalHoles := true) (tagSuffix := `convert) do
          -- Allow typeclass inference failures since these will be inferred by unification
          -- or else become new goals
          withTheReader Term.Context (fun ctx => { ctx with ignoreTCFailures := true }) do
            let t ← elabTermEnsuringType (mayPostpone := true) term expectedType
            -- Process everything so that tactics get run, but again allow TC failures
            Term.synthesizeSyntheticMVars (mayPostpone := false) (ignoreStuckTC := true)
            -- Use a type hint to ensure we collect goals from the type too
            mkExpectedTypeHint t (← inferType t)
      liftMetaTactic fun g ↦
        return (← g.convert e sym.isSome (n.map (·.getNat)) config patterns) ++ gs
  | _                     => throwUnsupportedSyntax

end Lean.Elab.Tactic
