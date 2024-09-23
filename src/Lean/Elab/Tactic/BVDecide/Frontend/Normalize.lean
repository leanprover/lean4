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

structure Result where
  goal : Option MVarId := none
  stats : Simp.Stats := {}

def bvNormalize (g : MVarId) : MetaM Result := do
  withTraceNode `bv (fun _ => return "Normalizing goal") do
    -- Contradiction proof
    let some g ← g.falseOrByContra | return {}

    -- Normalization by simp
    let bvThms ← bvNormalizeExt.getTheorems
    let bvSimprocs ← bvNormalizeSimprocExt.getSimprocs
    let sevalThms ← getSEvalTheorems
    let sevalSimprocs ← Simp.getSEvalSimprocs

    let simpCtx : Simp.Context := {
      config := { failIfUnchanged := false, zetaDelta := true }
      simpTheorems := #[bvThms, sevalThms]
      congrTheorems := (← getSimpCongrTheorems)
    }

    let hyps ← g.getNondepPropHyps
    let ⟨result?, stats⟩ ← simpGoal g
      (ctx := simpCtx)
      (simprocs := #[bvSimprocs, sevalSimprocs])
      (fvarIdsToSimp := hyps)
    let some (_, g) := result? | return ⟨none, stats⟩
    return ⟨some g, stats⟩

@[builtin_tactic Lean.Parser.Tactic.bvNormalize]
def evalBVNormalize : Tactic := fun
  | `(tactic| bv_normalize) => do
    liftMetaFinishingTactic fun g => do
      discard <| bvNormalize g
  | _ => throwUnsupportedSyntax

end Frontend.Normalize
end Lean.Elab.Tactic.BVDecide


