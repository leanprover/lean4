/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Lean.Elab.Tactic.BVDecide.Frontend.Normalize.Basic
import Lean.Meta.Tactic.AC.Main

/-!
This module contains the implementation of the associativity and commutativity normalisation pass
in the fixpoint pipeline.
-/

namespace Lean.Elab.Tactic.BVDecide
namespace Frontend.Normalize

open Lean.Meta

/--
Normalize with respect to Associativity and Commutativity.
-/
def acNormalizePass : Pass where
  name := `ac_nf
  run' goal := do
    let mut newGoal := goal
    for hyp in (← goal.getNondepPropHyps) do
      let result ← AC.acNfHypMeta newGoal hyp

      if let .some nextGoal := result then
        newGoal := nextGoal
      else
        return none

    return newGoal


end Frontend.Normalize
end Lean.Elab.Tactic.BVDecide
