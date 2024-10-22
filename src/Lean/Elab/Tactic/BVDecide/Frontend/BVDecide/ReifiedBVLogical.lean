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

/--
Construct a `ReifiedBVLogical` from `ReifiedBVPred` by wrapping it as an atom.
-/
def ofPred  (bvPred : ReifiedBVPred) : M (Option ReifiedBVLogical) := do
  let boolExpr := .literal bvPred.bvPred
  let expr := mkApp2 (mkConst ``BoolExpr.literal) (mkConst ``BVPred) bvPred.expr
  let proof := bvPred.evalsAtAtoms
  return some ⟨boolExpr, proof, expr⟩

/--
Construct an uninterrpeted `Bool` atom from `t`.
-/
def boolAtom (t : Expr) : M (Option ReifiedBVLogical) := do
  let some pred ← ReifiedBVPred.boolAtom t | return none
  ofPred pred

/--
Reify an `Expr` that is a boolean expression containing predicates about `BitVec` as atoms.
Unless this function is called on something that is not a `Bool` it is always going to return `some`.
-/
partial def of (t : Expr) : M (Option ReifiedBVLogical) := do
  goOrAtom t
where
  /--
  Reify `t`, returns `none` if the reification procedure failed.
  -/
  go (t : Expr) : M (Option ReifiedBVLogical) := do
    match_expr t with
    | Bool.true =>
      let boolExpr := .const true
      let expr := mkApp2 (mkConst ``BoolExpr.const) (mkConst ``BVPred) (toExpr Bool.true)
      let proof := pure <| mkRefl (mkConst ``Bool.true)
      return some ⟨boolExpr, proof, expr⟩
    | Bool.false =>
      let boolExpr := .const false
      let expr := mkApp2 (mkConst ``BoolExpr.const) (mkConst ``BVPred) (toExpr Bool.false)
      let proof := pure <| mkRefl (mkConst ``Bool.false)
      return some ⟨boolExpr, proof, expr⟩
    | Bool.not subExpr =>
      let some sub ← goOrAtom subExpr | return none
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

  /--
  Reify `t` or abstract it as an atom.
  Unless this function is called on something that is not a `Bool` it is always going to return `some`.
  -/
  goOrAtom (t : Expr) : M (Option ReifiedBVLogical) := do
    match ← go t with
    | some boolExpr => return some boolExpr
    | none => boolAtom t

  gateReflection (lhsExpr rhsExpr : Expr) (gate : Gate) (congrThm : Name) :
      M (Option ReifiedBVLogical) := do
    let some lhs ← goOrAtom lhsExpr | return none
    let some rhs ← goOrAtom rhsExpr | return none
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
    let some pred ← ReifiedBVPred.of t | return none
    ofPred pred

end ReifiedBVLogical

end Frontend
end Lean.Elab.Tactic.BVDecide
