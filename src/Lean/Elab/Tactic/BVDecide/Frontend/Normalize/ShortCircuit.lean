/-
Copyright (c) 2025 Tobias Grosser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Grosser
-/
module

prelude
public import Lean.Elab.Tactic.BVDecide.Frontend.Normalize.Basic
public import Std.Tactic.BVDecide.Normalize.BitVec

public section

/-!
This module contains the implementation of the short-circuiting pass, which is responsible for
applying short-circuit optimizations for `*`, e.g., translating `x1 * y == x2 * y` to
`!(!x1 == x2 && !x1 * y == x2 * y)`.
-/

namespace Lean.Elab.Tactic.BVDecide
namespace Frontend.Normalize

open Lean.Meta
open Std.Tactic.BVDecide.Normalize.BitVec

/--
Responsible for applying short-circuit optimizations for `*`, e.g.,
translating `x1 * y == x2 * y` to `!(!x1 == x2 && !x1 * y == x2 * y)`.
-/
def shortCircuitPass : Pass where
  name := `shortCircuitPass
  run' goal := do
    goal.withContext do
      let mut theorems : SimpTheoremsArray := #[]
      theorems ← theorems.addTheorem
        (Lean.Meta.Origin.decl `mul_beq_mul_short_circuit_left)
        (mkConst ``mul_beq_mul_short_circuit_left)
      theorems ← theorems.addTheorem
        (Lean.Meta.Origin.decl `mul_beq_mul_short_circuit_right)
        (mkConst ``mul_beq_mul_short_circuit_right)

      let simpCtx ← Simp.mkContext
        (config := {
          failIfUnchanged := false,
          zetaDelta := true,
          singlePass := true,
          maxSteps := (← PreProcessM.getConfig).maxSteps
        })
        (simpTheorems := theorems)
        (congrTheorems := (← getSimpCongrTheorems))

      let hyps ← getPropHyps
      let ⟨result?, _⟩ ← simpGoal goal
        (ctx := simpCtx)
        (simprocs := #[])
        (fvarIdsToSimp := hyps)
      let some (_, newGoal) := result? | return none
      return newGoal

end Frontend.Normalize
end Lean.Elab.Tactic.BVDecide
