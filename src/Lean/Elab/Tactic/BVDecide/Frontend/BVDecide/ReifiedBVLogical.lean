/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Lean.Elab.Tactic.BVDecide.Frontend.BVDecide.ReifiedBVPred

/-!
Provides the logic for reifying `BitVec` problems with boolean substructure.
-/

namespace Lean.Elab.Tactic.BVDecide
namespace Frontend

open Std.Tactic.BVDecide
open Std.Tactic.BVDecide.Reflect.Bool

/--
A reified version of an `Expr` representing a `BVLogicalExpr`.
-/
structure ReifiedBVLogical where
  /--
  The reified expression.
  -/
  bvExpr : BVLogicalExpr
  /--
  A proof that `bvExpr.eval atomsAssignment = originalBVLogicalExpr`.
  -/
  evalsAtAtoms : M Expr
  /--
  A cache for `toExpr bvExpr`
  -/
  expr : Expr

namespace ReifiedBVLogical

def mkRefl (expr : Expr) : Expr :=
  mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) expr

def mkTrans (x y z : Expr) (hxy hyz : Expr) : Expr :=
  mkApp6 (mkConst ``Eq.trans [1]) (mkConst ``Bool) x y z hxy hyz

def mkEvalExpr (expr : Expr) : M Expr := do
  return mkApp2 (mkConst ``BVLogicalExpr.eval) (← M.atomsAssignment) expr

partial def of (t : Expr) : M (Option ReifiedBVLogical) := do
  match_expr t with
  | Bool.true =>
    let boolExpr := .const true
    let expr := mkApp2 (mkConst ``BoolExpr.const) (mkConst ``BVPred) (toExpr Bool.true)
    let proof := return mkRefl (mkConst ``Bool.true)
    return some ⟨boolExpr, proof, expr⟩
  | Bool.false =>
    let boolExpr := .const false
    let expr := mkApp2 (mkConst ``BoolExpr.const) (mkConst ``BVPred) (toExpr Bool.false)
    let proof := return mkRefl (mkConst ``Bool.false)
    return some ⟨boolExpr, proof, expr⟩
  | Bool.not subExpr =>
    let some sub ← of subExpr | return none
    let boolExpr := .not sub.bvExpr
    let expr := mkApp2 (mkConst ``BoolExpr.not) (mkConst ``BVPred) sub.expr
    let proof := do
      let subEvalExpr ← mkEvalExpr sub.expr
      let subProof ← sub.evalsAtAtoms
      return mkApp3 (mkConst ``Std.Tactic.BVDecide.Reflect.Bool.not_congr) subExpr subEvalExpr subProof
    return some ⟨boolExpr, proof, expr⟩
  | Bool.and lhsExpr rhsExpr => gateReflection lhsExpr rhsExpr .and ``Std.Tactic.BVDecide.Reflect.Bool.and_congr
  | Bool.xor lhsExpr rhsExpr => gateReflection lhsExpr rhsExpr .xor ``Std.Tactic.BVDecide.Reflect.Bool.xor_congr
  | BEq.beq α _ lhsExpr rhsExpr =>
    match_expr α with
    | Bool => gateReflection lhsExpr rhsExpr .beq ``Std.Tactic.BVDecide.Reflect.Bool.beq_congr
    | BitVec _ => goPred t
    | _ => return none
  | _ => goPred t
where
  gateReflection (lhsExpr rhsExpr : Expr) (gate : Gate) (congrThm : Name) :
      M (Option ReifiedBVLogical) := do
    let some lhs ← of lhsExpr | return none
    let some rhs ← of rhsExpr | return none
    let boolExpr := .gate  gate lhs.bvExpr rhs.bvExpr
    let expr :=
      mkApp4
        (mkConst ``BoolExpr.gate)
        (mkConst ``BVPred)
        (toExpr gate)
        lhs.expr
        rhs.expr
    let proof := do
      let lhsEvalExpr ← mkEvalExpr lhs.expr
      let rhsEvalExpr ← mkEvalExpr rhs.expr
      let lhsProof ← lhs.evalsAtAtoms
      let rhsProof ← rhs.evalsAtAtoms
      return mkApp6
        (mkConst congrThm)
        lhsExpr rhsExpr
        lhsEvalExpr rhsEvalExpr
        lhsProof rhsProof
    return some ⟨boolExpr, proof, expr⟩

  goPred (t : Expr) : M (Option ReifiedBVLogical) := do
    let some bvPred ← ReifiedBVPred.of t | return none
    let boolExpr := .literal bvPred.bvPred
    let expr := mkApp2 (mkConst ``BoolExpr.literal) (mkConst ``BVPred) bvPred.expr
    let proof := bvPred.evalsAtAtoms
    return some ⟨boolExpr, proof, expr⟩

end ReifiedBVLogical

end Frontend
end Lean.Elab.Tactic.BVDecide
