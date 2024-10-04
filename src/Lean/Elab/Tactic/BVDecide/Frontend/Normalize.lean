/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Lean.Meta.AppBuilder
import Lean.Elab.Tactic.Simp
import Lean.Elab.Tactic.FalseOrByContra
import Lean.Elab.Tactic.BVDecide.Frontend.Attr
import Std.Tactic.BVDecide.Normalize
import Std.Tactic.BVDecide.Syntax

/-!
This module contains the implementation of `bv_normalize` which is effectively a custom `bv_normalize`
simp set that is called like this: `simp only [seval, bv_normalize]`. The rules in `bv_normalize`
fulfill two goals:
1. Turn all hypothesis involving `Bool` and `BitVec` into the form `x = true` where `x` only consists
   of a operations on `Bool` and `BitVec`. In particular no `Prop` should be contained. This makes
   the reflection procedure further down the pipeline much easier to implement.
2. Apply simplification rules from the Bitwuzla SMT solver.
-/

namespace Lean.Elab.Tactic.BVDecide
namespace Frontend.Normalize

open Lean.Meta
open Std.Tactic.BVDecide.Normalize

builtin_simproc [bv_normalize] eqToBEq (((_ : Bool) = (_ : Bool))) := fun e => do
  let_expr Eq _ lhs rhs := e | return .continue
  match_expr rhs with
  | Bool.true => return .continue
  | _ =>
    let beqApp ← mkAppM ``BEq.beq #[lhs, rhs]
    let new := mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool) beqApp (mkConst ``Bool.true)
    let proof := mkApp2 (mkConst ``Bool.eq_to_beq) lhs rhs
    return .done { expr := new, proof? := some proof }

builtin_simproc [bv_normalize] andOnes ((_ : BitVec _) &&& (_ : BitVec _)) := fun e => do
  let_expr HAnd.hAnd _ _ _ _ lhs rhs := e | return .continue
  let some ⟨w, rhsValue⟩ ← getBitVecValue? rhs | return .continue
  if rhsValue == -1#w then
    let proof := mkApp2 (mkConst ``Std.Tactic.BVDecide.Normalize.BitVec.and_ones) (toExpr w) lhs
    return .visit { expr := lhs, proof? := some proof }
  else
    return .continue

builtin_simproc [bv_normalize] onesAnd ((_ : BitVec _) &&& (_ : BitVec _)) := fun e => do
  let_expr HAnd.hAnd _ _ _ _ lhs rhs := e | return .continue
  let some ⟨w, lhsValue⟩ ← getBitVecValue? lhs | return .continue
  if lhsValue == -1#w then
    let proof := mkApp2 (mkConst ``Std.Tactic.BVDecide.Normalize.BitVec.ones_and) (toExpr w) rhs
    return .visit { expr := rhs, proof? := some proof }
  else
    return .continue

builtin_simproc [bv_normalize] maxUlt (BitVec.ult (_ : BitVec _) (_ : BitVec _)) := fun e => do
  let_expr BitVec.ult _ lhs rhs := e | return .continue
  let some ⟨w, lhsValue⟩ ← getBitVecValue? lhs | return .continue
  if lhsValue == -1#w then
    let proof := mkApp2 (mkConst ``Std.Tactic.BVDecide.Normalize.BitVec.max_ult') (toExpr w) rhs
    return .visit { expr := toExpr Bool.false, proof? := some proof }
  else
    return .continue

/--
A pass in the normalization pipeline. Takes the current goal and produces a refined one or closes
the goal fully, indicated by returning `none`.
-/
abbrev Pass := MVarId → MetaM (Option MVarId)

namespace Pass

/--
Repeatedly run a list of `Pass` until they either close the goal or an iteration doesn't change
the goal anymore.
-/
partial def fixpointPipeline (passes : List Pass) (goal : MVarId) : MetaM (Option MVarId) := do
  let runPass (goal? : Option MVarId) (pass : Pass) : MetaM (Option MVarId) := do
    let some goal := goal? | return none
    pass goal

  let some newGoal := ← passes.foldlM (init := some goal) runPass | return none
  if goal != newGoal then
    trace[Meta.Tactic.bv] m!"Rerunning pipeline on:\n{newGoal}"
    fixpointPipeline passes newGoal
  else
    trace[Meta.Tactic.bv] "Pipeline reached a fixpoint"
    return newGoal

/--
Responsible for applying the Bitwuzla style rewrite rules.
-/
def rewriteRulesPass : Pass := fun goal => do
  let bvThms ← bvNormalizeExt.getTheorems
  let bvSimprocs ← bvNormalizeSimprocExt.getSimprocs
  let sevalThms ← getSEvalTheorems
  let sevalSimprocs ← Simp.getSEvalSimprocs

  let simpCtx : Simp.Context := {
    config := { failIfUnchanged := false, zetaDelta := true }
    simpTheorems := #[bvThms, sevalThms]
    congrTheorems := (← getSimpCongrTheorems)
  }

  let hyps ← goal.getNondepPropHyps
  let ⟨result?, _⟩ ← simpGoal goal
    (ctx := simpCtx)
    (simprocs := #[bvSimprocs, sevalSimprocs])
    (fvarIdsToSimp := hyps)
  let some (_, newGoal) := result? | return none
  return newGoal

/--
The normalization passes used by `bv_normalize` and thus `bv_decide`.
-/
def defaultPipeline : List Pass := [rewriteRulesPass]

end Pass

def bvNormalize (g : MVarId) : MetaM (Option MVarId) := do
  withTraceNode `bv (fun _ => return "Normalizing goal") do
    -- Contradiction proof
    let some g ← g.falseOrByContra | return none
    trace[Meta.Tactic.bv] m!"Running preprocessing pipeline on:\n{g}"
    Pass.fixpointPipeline Pass.defaultPipeline g

@[builtin_tactic Lean.Parser.Tactic.bvNormalize]
def evalBVNormalize : Tactic := fun
  | `(tactic| bv_normalize) => do
    let g ← getMainGoal
    match ← bvNormalize g with
    | some newGoal => setGoals [newGoal]
    | none => setGoals []
  | _ => throwUnsupportedSyntax

end Frontend.Normalize
end Lean.Elab.Tactic.BVDecide


