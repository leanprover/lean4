/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Lean.Meta.AppBuilder
import Lean.Meta.Tactic.AC.Main
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

-- A specialised version of BitVec.neg_eq_not_add so it doesn't trigger on -constant
builtin_simproc [bv_normalize] neg_eq_not_add (-(_ : BitVec _)) := fun e => do
  let_expr Neg.neg typ _ val := e | return .continue
  let_expr BitVec widthExpr := typ | return .continue
  let some w ← getNatValue? widthExpr | return .continue
  match ← getBitVecValue? val with
  | some _ => return .continue
  | none =>
    let proof := mkApp2 (mkConst ``BitVec.neg_eq_not_add) (toExpr w) val
    let expr ← mkAppM ``HAdd.hAdd #[← mkAppM ``Complement.complement #[val], (toExpr 1#w)]
    return .visit { expr := expr, proof? := some proof }

builtin_simproc [bv_normalize] bv_add_const ((_ : BitVec _) + ((_ : BitVec _) + (_ : BitVec _))) :=
  fun e => do
    let_expr HAdd.hAdd _ _ _ _ exp1 rhs := e | return .continue
    let_expr HAdd.hAdd _ _ _ _ exp2 exp3 := rhs | return .continue
    let some ⟨w, exp1Val⟩ ←  getBitVecValue? exp1 | return .continue
    let proofBuilder thm := mkApp4 (mkConst thm) (toExpr w) exp1 exp2 exp3
    match ← getBitVecValue? exp2 with
    | some ⟨w', exp2Val⟩ =>
      if h : w = w' then
        let newLhs := exp1Val + h ▸ exp2Val
        let expr ← mkAppM ``HAdd.hAdd #[toExpr newLhs, exp3]
        let proof := proofBuilder ``Std.Tactic.BVDecide.Normalize.BitVec.add_const_left
        return .visit { expr := expr, proof? := some proof }
      else
        return .continue
    | none =>
      let some ⟨w', exp3Val⟩ ← getBitVecValue? exp3 | return .continue
      if h : w = w' then
        let newLhs := exp1Val + h ▸ exp3Val
        let expr ← mkAppM ``HAdd.hAdd #[toExpr newLhs, exp2]
        let proof := proofBuilder ``Std.Tactic.BVDecide.Normalize.BitVec.add_const_right
        return .visit { expr := expr, proof? := some proof }
      else
        return .continue

builtin_simproc [bv_normalize] bv_add_const' (((_ : BitVec _) + (_ : BitVec _)) + (_ : BitVec _)) :=
  fun e => do
    let_expr HAdd.hAdd _ _ _ _ lhs exp3 := e | return .continue
    let_expr HAdd.hAdd _ _ _ _ exp1 exp2 := lhs | return .continue
    let some ⟨w, exp3Val⟩ ←  getBitVecValue? exp3 | return .continue
    let proofBuilder thm := mkApp4 (mkConst thm) (toExpr w) exp1 exp2 exp3
    match ← getBitVecValue? exp1 with
    | some ⟨w', exp1Val⟩ =>
      if h : w = w' then
        let newLhs := exp3Val + h ▸ exp1Val
        let expr ← mkAppM ``HAdd.hAdd #[toExpr newLhs, exp2]
        let proof := proofBuilder ``Std.Tactic.BVDecide.Normalize.BitVec.add_const_left'
        return .visit { expr := expr, proof? := some proof }
      else
        return .continue
    | none =>
      let some ⟨w', exp2Val⟩ ← getBitVecValue? exp2 | return .continue
      if h : w = w' then
        let newLhs := exp3Val + h ▸ exp2Val
        let expr ← mkAppM ``HAdd.hAdd #[toExpr newLhs, exp1]
        let proof := proofBuilder ``Std.Tactic.BVDecide.Normalize.BitVec.add_const_right'
        return .visit { expr := expr, proof? := some proof }
      else
        return .continue

attribute [builtin_bv_normalize_proc↓] reduceIte

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
Substitute embedded constraints. That is look for hypotheses of the form `h : x = true` and use
them to substitute occurences of `x` within other hypotheses
-/
def embeddedConstraintPass : Pass := fun goal =>
  goal.withContext do
    let hyps ← goal.getNondepPropHyps
    let relevanceFilter acc hyp := do
      let typ ← hyp.getType
      let_expr Eq α _ rhs := typ | return acc
      let_expr Bool := α | return acc
      let_expr Bool.true := rhs | return acc
      let localDecl ← hyp.getDecl
      let proof  := localDecl.toExpr
      acc.addTheorem (.fvar hyp) proof
    let relevantHyps : SimpTheoremsArray ← hyps.foldlM (init := #[]) relevanceFilter

    let simpCtx : Simp.Context := {
      config := { failIfUnchanged := false }
      simpTheorems := relevantHyps
      congrTheorems := (← getSimpCongrTheorems)
    }

    let ⟨result?, _⟩ ← simpGoal goal (ctx := simpCtx) (fvarIdsToSimp := hyps)
    let some (_, newGoal) := result? | return none
    return newGoal

/--
Normalize with respect to Associativity and Commutativity.
-/
def acNormalizePass : Pass := fun goal => do
  let mut newGoal := goal
  for hyp in (← goal.getNondepPropHyps) do
    let result ← Lean.Meta.AC.acNfHypMeta newGoal hyp

    if let .some nextGoal := result then
      newGoal := nextGoal
    else
      return none

  return newGoal

/--
The normalization passes used by `bv_normalize` and thus `bv_decide`.
-/
def defaultPipeline : List Pass := [rewriteRulesPass, embeddedConstraintPass]

def passPipeline : MetaM (List Pass) := do
  let opts ← getOptions

  let mut passPipeline := defaultPipeline

  if bv.ac_nf.get opts then
    passPipeline := passPipeline ++ [acNormalizePass]

  return passPipeline

end Pass

def bvNormalize (g : MVarId) : MetaM (Option MVarId) := do
  withTraceNode `bv (fun _ => return "Normalizing goal") do
    -- Contradiction proof
    let some g ← g.falseOrByContra | return none
    trace[Meta.Tactic.bv] m!"Running preprocessing pipeline on:\n{g}"
    Pass.fixpointPipeline (← Pass.passPipeline) g

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
