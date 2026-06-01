/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Lean.Meta.Tactic.BVDecide.Normalize.Basic

/-!
This module contains the implementation of the rewriting pass in the fixpoint pipeline, applying
rules from the `bv_normalize` simp set.
-/

namespace Lean.Meta.Tactic.BVDecide
namespace Normalize

/--
Responsible for applying the Bitwuzla style rewrite rules.
-/
public def rewriteRulesPass : Pass where
  name := `rewriteRules
  run' goal := do
    let bvThms ← bvNormalizeExt.getTheorems
    let bvSimprocs ← bvNormalizeSimprocExt.getSimprocs
    let sevalThms ← getSEvalTheorems
    let sevalSimprocs ← Simp.getSEvalSimprocs
    let cfg ← PreProcessM.getConfig

    let simpCtx ← Simp.mkContext
      (config := {
        failIfUnchanged := false,
        zetaDelta := true,
        implicitDefEqProofs := false, -- leanprover/lean4/pull/7509
        maxSteps := cfg.maxSteps,
        instances := true
      })
      (simpTheorems := #[bvThms, sevalThms])
      (congrTheorems := (← getSimpCongrTheorems))

    let hyps ← getHyps goal
    if hyps.isEmpty then
      return goal
    else
      let ⟨result?, _⟩ ← simpGoal goal
        (ctx := simpCtx)
        (simprocs := #[bvSimprocs, sevalSimprocs])
        (fvarIdsToSimp := hyps)

      let some (_, newGoal) := result? | return none
      newGoal.withContext do
        (← getPropHyps).forM PreProcessM.rewriteFinished
      return newGoal
where
  getHyps (goal : MVarId) : PreProcessM (Array FVarId) := do
    goal.withContext do
      let hyps ← getPropHyps
      let filter hyp := do
        return !(← PreProcessM.checkRewritten hyp)
      hyps.filterM filter


end Normalize
end Lean.Meta.Tactic.BVDecide
