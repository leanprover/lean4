/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Lean.Meta.Tactic.BVDecide.Reflect.Basic
import Lean.Meta.Tactic.BVDecide.Reflect.ReifiedBVLogical
import Lean.Meta.Tactic.BVDecide.Reflect.Reify
import Lean.Meta.Sym.InferType
import Lean.Meta.Sym.InstantiateMVarsS
import Std.Tactic.BVDecide.Reflect

/-!
This module is the main entry point for reifying `BitVec` problems with boolean substructure.
Given some proof `h : exp = true` where `exp` is a `BitVec` problem with boolean substructure, it
returns a `SatAtBVLogical`, containing the reified version as well as a proof that the reified
version must be equal to true.
-/

namespace Lean.Meta.Tactic.BVDecide

open Std.Tactic.BVDecide

namespace SatAtBVLogical

/--
Reify an `Expr` that is a proof of some boolean structure on top of predicates about `BitVec`s.
-/
public partial def of (hyp : Normalize.Hyp) : LemmaM (Option SatAtBVLogical) := do
  match_expr hyp.type with
  | Eq α lhsExpr rhsExpr =>
    let_expr Bool := α | return none
    let_expr Bool.true := rhsExpr | return none
    -- We now know that `h : lhsExpr = true`
    -- We attempt to reify lhsExpr into a BVLogicalExpr, then prove that evaluating
    -- this BVLogicalExpr must eval to true due to `h`
    let some bvLogical ← ReifiedBVLogical.of lhsExpr | return none
    let proof := do
      let evalLogic ← ReifiedBVLogical.mkEvalExpr bvLogical.expr
      -- this is evalLogic = lhsExpr
      let evalProof := (← bvLogical.evalsAtAtoms).getD (ReifiedBVLogical.mkRefl evalLogic)
      -- h is lhsExpr = true
      -- we prove evalLogic = true by evalLogic = lhsExpr = true
      return ReifiedBVLogical.mkTrans evalLogic lhsExpr (mkConst ``Bool.true) evalProof hyp.value
    return some ⟨bvLogical.bvExpr, proof, bvLogical.expr⟩
  | _ => return none

/--
Logical conjunction of two `ReifiedBVLogical`.
-/
public def and (x y : SatAtBVLogical) : M SatAtBVLogical := do
  let bvExpr := .gate .and x.bvExpr y.bvExpr
  let expr ← Sym.share <| mkApp4 (mkConst ``BoolExpr.gate) (mkConst ``BVPred) (mkConst ``Gate.and) x.expr y.expr
  let proof := do
    return mkApp5
      (mkConst ``BVLogicalExpr.sat_and)
      x.expr
      y.expr
      (← M.atomsAssignment)
      (← x.satAtAtoms)
      (← y.satAtAtoms)
  return ⟨bvExpr, proof, expr⟩

/-- Given a proof that `x.expr.Unsat`, produce a proof of `False`. -/
public def proveFalse (x : SatAtBVLogical) (h : Expr) : M Expr := do
  if (← get).atoms.isEmpty then
    throwError "Unable to identify any relevant atoms."
  else
    let atomsList ← M.atomsAssignment
    let evalExpr ← Sym.share <| mkApp2 (mkConst ``BVLogicalExpr.eval) atomsList x.expr
    return mkApp3
      (mkConst ``Std.Tactic.BVDecide.Reflect.Bool.false_of_eq_true_of_eq_false)
      evalExpr
      (← x.satAtAtoms)
      (.app h atomsList)


end SatAtBVLogical

end Lean.Meta.Tactic.BVDecide
