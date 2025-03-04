/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Std.Tactic.BVDecide.Normalize.Bool
import Lean.Elab.Tactic.BVDecide.Frontend.Normalize.Basic
import Lean.Meta.Tactic.Simp

/-!
This module contains the implementation of the embedded constraint substitution pass in the fixpoint
pipeline, substituting hypotheses of the form `h : x = true` in other hypotheses.
-/

namespace Lean.Elab.Tactic.BVDecide
namespace Frontend.Normalize

open Lean.Meta

/--
Substitute embedded constraints. That is look for hypotheses of the form `h : x = true` and use
them to substitute occurrences of `x` within other hypotheses. Additionally this drops all
redundant top level hypotheses.
-/
def embeddedConstraintPass : Pass where
  name := `embeddedConstraintSubsitution
  run' goal := do
    goal.withContext do
      let hyps ← getPropHyps
      let mut relevantHyps : SimpTheoremsArray := #[]
      let mut seen : Std.HashSet Expr := {}
      let mut duplicates : Array FVarId := #[]
      for hyp in hyps do
        let typ ← hyp.getType
        let_expr Eq _ lhs rhs := typ | continue
        let_expr Bool.true := rhs | continue
        if seen.contains lhs then
          duplicates := duplicates.push hyp
        else
          seen := seen.insert lhs
          let localDecl ← hyp.getDecl
          let proof := localDecl.toExpr
          relevantHyps ← relevantHyps.addTheorem (.fvar hyp) proof

      let goal ← goal.tryClearMany duplicates

      if relevantHyps.isEmpty then
        return goal

      let cfg ← PreProcessM.getConfig
      let targets ← goal.withContext getPropHyps
      let simpCtx ← Simp.mkContext
        (config := {
          failIfUnchanged := false,
          implicitDefEqProofs := false, -- leanprover/lean4/pull/7509
          maxSteps := cfg.maxSteps,
        })
        (simpTheorems := relevantHyps)
        (congrTheorems := (← getSimpCongrTheorems))
      let ⟨result?, _⟩ ← simpGoal goal (ctx := simpCtx) (fvarIdsToSimp := targets)
      let some (_, newGoal) := result? | return none
      return newGoal


end Frontend.Normalize
end Lean.Elab.Tactic.BVDecide
