/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Std.Tactic.BVDecide.Normalize.Bool
public import Lean.Meta.Tactic.BVDecide.Normalize.Basic

/-!
This module contains the implementation of the embedded constraint substitution pass in the fixpoint
pipeline, substituting hypotheses of the form `h : x = true` in other hypotheses.
-/

namespace Lean.Meta.Tactic.BVDecide
namespace Normalize

/--
Substitute embedded constraints. That is look for hypotheses of the form `h : x = true` and use
them to substitute occurrences of `x` within other hypotheses. Additionally this drops all
redundant top level hypotheses.
-/
public def embeddedConstraintPass : Pass where
  name := `embeddedConstraintSubstitution
  run' := do
    let goal ← PreProcessM.getGoal
    goal.withContext do
      let hyps ← PreProcessM.getHyps
      let mut relevantHyps : SimpTheoremsArray := #[]
      -- TODO: make me exprptr based
      let mut seen : Std.HashSet Expr := {}
      for h : idx in 0...hyps.size do
        let hyp := hyps[idx]
        let type := hyp.type
        let_expr Eq _ lhs rhs := type | continue
        let_expr Bool.true := rhs | continue
        if !seen.contains lhs then
          seen := seen.insert lhs
          relevantHyps ← relevantHyps.addTheorem (.other (.num .anonymous idx)) hyp.value

      if relevantHyps.isEmpty then
        return false

      let cfg ← PreProcessM.getConfig
      PreProcessM.mapIdxHyps fun idx hyp => do
        let relevantHyps := relevantHyps.eraseTheorem (.other (.num .anonymous idx))
        let simpCtx ← Simp.mkContext
          (config := {
            failIfUnchanged := false,
            implicitDefEqProofs := false, -- leanprover/lean4/pull/7509
            maxSteps := cfg.maxSteps,
            instances := true
          })
          (simpTheorems := relevantHyps)
          (congrTheorems := (← getSimpCongrTheorems))
        let (res, _) ← simp hyp.type simpCtx
        let some (value, type) ← applySimpResult goal hyp.value hyp.type res false | unreachable!
        return {
          name := hyp.name
          type := type
          value := value
        }

end Normalize
end Lean.Meta.Tactic.BVDecide
