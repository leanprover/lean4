/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Std.Tactic.BVDecide.Normalize.Bool
import Lean.Elab.Tactic.BVDecide.Frontend.Normalize.Basic
import Lean.Meta.Tactic.Assert

/-!
This module contains the implementation of the and flattening pass in the fixpoint pipeline, taking
hypotheses of the form `h : x && y = true` and splitting them into `h1 : x = true` and
`h2 : y = true` recursively.
-/

namespace Lean.Elab.Tactic.BVDecide
namespace Frontend.Normalize

open Lean.Meta

/--
Flatten out ands. That is look for hypotheses of the form `h : (x && y) = true` and replace them
with `h.left : x = true` and `h.right : y = true`. This can enable more fine grained substitutions
in embedded constraint substitution.
-/
partial def andFlatteningPass : Pass where
  name := `andFlattening
  run' goal := do
    goal.withContext do
      let hyps ← goal.getNondepPropHyps
      let mut newHyps := #[]
      let mut oldHyps := #[]
      for fvar in hyps do
        let hyp : Hypothesis := {
          userName := (← fvar.getDecl).userName
          type := ← fvar.getType
          value := mkFVar fvar
        }
        let sizeBefore := newHyps.size
        newHyps ← splitAnds hyp newHyps
        if newHyps.size > sizeBefore then
          oldHyps := oldHyps.push fvar
      if newHyps.size == 0 then
        return goal
      else
        let (_, goal) ← goal.assertHypotheses newHyps
        -- Given that we collected the hypotheses in the correct order above the invariant is given
        let goal ← goal.tryClearMany oldHyps
        return goal
where
  splitAnds (hyp : Hypothesis) (hyps : Array Hypothesis) (first : Bool := true) :
      MetaM (Array Hypothesis) := do
    match ← trySplit hyp with
    | some (left, right) =>
      let hyps ← splitAnds left hyps false
      splitAnds right hyps false
    | none =>
      if first then
        return hyps
      else
        return hyps.push hyp

  trySplit (hyp : Hypothesis) : MetaM (Option (Hypothesis × Hypothesis)) := do
    let typ := hyp.type
    let_expr Eq α eqLhs eqRhs := typ | return none
    let_expr Bool.and lhs rhs := eqLhs | return none
    let_expr Bool.true := eqRhs | return none
    let_expr Bool := α | return none
    let mkEqTrue (lhs : Expr) : Expr :=
      mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool) lhs (mkConst ``Bool.true)
    let leftHyp : Hypothesis := {
      userName := hyp.userName,
      type := mkEqTrue lhs,
      value := mkApp3 (mkConst ``Std.Tactic.BVDecide.Normalize.Bool.and_left) lhs rhs hyp.value
    }
    let rightHyp : Hypothesis := {
      userName := hyp.userName,
      type := mkEqTrue rhs,
      value := mkApp3 (mkConst ``Std.Tactic.BVDecide.Normalize.Bool.and_right) lhs rhs hyp.value
    }
    return some (leftHyp, rightHyp)


end Frontend.Normalize
end Lean.Elab.Tactic.BVDecide
