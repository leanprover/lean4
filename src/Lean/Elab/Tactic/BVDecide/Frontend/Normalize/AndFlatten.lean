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

structure AndFlattenState where
  hypsToDelete : Array FVarId := #[]
  hypsToAdd : Array Hypothesis := #[]
  cache : Std.HashSet Expr := {}

/--
Flatten out ands. That is look for hypotheses of the form `h : (x && y) = true` and replace them
with `h.left : x = true` and `h.right : y = true`. This can enable more fine grained substitutions
in embedded constraint substitution.
-/
partial def andFlatteningPass : Pass where
  name := `andFlattening
  run' goal := do
    let (_, { hypsToDelete, hypsToAdd, .. }) ← processGoal goal |>.run {}
    if hypsToAdd.isEmpty then
      return goal
    else
      let (_, goal) ← goal.assertHypotheses hypsToAdd
      -- Given that we collected the hypotheses in the correct order above the invariant is given
      let goal ← goal.tryClearMany hypsToDelete
      return goal
where
  processGoal (goal : MVarId) : StateRefT AndFlattenState MetaM Unit := do
    goal.withContext do
      let hyps ← goal.getNondepPropHyps
      hyps.forM processFVar

  processFVar (fvar : FVarId) : StateRefT AndFlattenState MetaM Unit := do
    let type ← fvar.getType
    if (← get).cache.contains type then
      modify (fun s => { s with hypsToDelete := s.hypsToDelete.push fvar })
    else
      let hyp := {
        userName := (← fvar.getDecl).userName
        type := type
        value := mkFVar fvar
      }
      let some (lhs, rhs) ← trySplit hyp | return ()
      modify (fun s => { s with hypsToDelete := s.hypsToDelete.push fvar })
      splitAnds [lhs, rhs]

  splitAnds (worklist : List Hypothesis) : StateRefT AndFlattenState MetaM Unit := do
    match worklist with
    | [] => return ()
    | hyp :: worklist =>
      match ← trySplit hyp with
      | some (left, right) => splitAnds <| left :: right :: worklist
      | none =>
        modify (fun s => { s with hypsToAdd := s.hypsToAdd.push hyp })
        splitAnds worklist

  trySplit (hyp : Hypothesis) :
      StateRefT AndFlattenState MetaM (Option (Hypothesis × Hypothesis)) := do
    let typ := hyp.type
    if (← get).cache.contains typ then
      return none
    else
      modify (fun s => { s with cache := s.cache.insert typ })
      let_expr Eq _ eqLhs eqRhs := typ | return none
      let_expr Bool.and lhs rhs := eqLhs | return none
      let_expr Bool.true := eqRhs | return none
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
