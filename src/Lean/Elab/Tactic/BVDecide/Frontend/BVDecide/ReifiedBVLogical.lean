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
open Lean.Meta

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
def ofPred (bvPred : ReifiedBVPred) : M ReifiedBVLogical := do
  let boolExpr := .literal bvPred.bvPred
  let expr := mkApp2 (mkConst ``BoolExpr.literal) (mkConst ``BVPred) bvPred.expr
  -- important: This must be the same proof as the bvPred one in order for the cache to be correct
  let proof := bvPred.evalsAtAtoms
  return ⟨boolExpr, bvPred.originalExpr, proof, expr⟩

/--
Construct an uninterrpeted `Bool` atom from `t`.
-/
def boolAtom (t : Expr) : M (Option ReifiedBVLogical) := do
  let some pred ← ReifiedBVPred.boolAtom t | return none
  ofPred pred

/--
Build a reified version of the constant `val`.
-/
def mkBoolConst (val : Bool) : M ReifiedBVLogical := do
  let boolExpr := .const val
  let expr := mkApp2 (mkConst ``BoolExpr.const) (mkConst ``BVPred) (toExpr val)
  -- This is safe because this proof always holds definitionally.
  let proof := pure none
  return ⟨boolExpr, toExpr val, proof, expr⟩

/--
Construct the reified version of applying the gate in `gate` to `lhs` and `rhs`.
This function assumes that `lhsExpr` and `rhsExpr` are the corresponding expressions to `lhs`
and `rhs`.
-/
def mkGate (lhs rhs : ReifiedBVLogical) (lhsExpr rhsExpr : Expr) (gate : Gate) (origExpr : Expr) :
    M ReifiedBVLogical := do
  let congrThm := congrThmOfGate gate
  let boolExpr := .gate gate lhs.bvExpr rhs.bvExpr
  let expr :=
    mkApp4
      (mkConst ``BoolExpr.gate)
      (mkConst ``BVPred)
      (toExpr gate)
      lhs.expr
      rhs.expr
  let proof := do
    let lhsEvalExpr ← ReifiedBVLogical.mkEvalExpr lhs.expr
    let rhsEvalExpr ← ReifiedBVLogical.mkEvalExpr rhs.expr
    let lhsProof? ← lhs.evalsAtAtoms
    let rhsProof? ← rhs.evalsAtAtoms
    let some (lhsProof, rhsProof) :=
      M.simplifyBinaryProof
        ReifiedBVLogical.mkRefl
        lhsEvalExpr lhsProof?
        rhsEvalExpr rhsProof? | return none
    return mkApp6
      (mkConst congrThm)
      lhsExpr rhsExpr
      lhsEvalExpr rhsEvalExpr
      lhsProof rhsProof
  return ⟨boolExpr, origExpr, proof, expr⟩
where
  congrThmOfGate (gate : Gate) : Name :=
    match gate with
    | .and => ``Std.Tactic.BVDecide.Reflect.Bool.and_congr
    | .xor => ``Std.Tactic.BVDecide.Reflect.Bool.xor_congr
    | .beq => ``Std.Tactic.BVDecide.Reflect.Bool.beq_congr
    | .or => ``Std.Tactic.BVDecide.Reflect.Bool.or_congr

/--
Construct the reified version of `Bool.not subExpr`.
This function assumes that `subExpr` is the expression corresponding to `sub`.
-/
def mkNot (sub : ReifiedBVLogical) (subExpr : Expr) (origExpr : Expr) : M ReifiedBVLogical := do
  let boolExpr := .not sub.bvExpr
  let expr := mkApp2 (mkConst ``BoolExpr.not) (mkConst ``BVPred) sub.expr
  let proof := do
    -- This is safe as `not_congr` holds definitionally if the arguments are defeq.
    let some subProof ← sub.evalsAtAtoms | return none
    let subEvalExpr ← ReifiedBVLogical.mkEvalExpr sub.expr
    return mkApp3 (mkConst ``Std.Tactic.BVDecide.Reflect.Bool.not_congr) subExpr subEvalExpr subProof
  return ⟨boolExpr, origExpr, proof, expr⟩

/--
Construct the reified version of `if discrExpr then lhsExpr else rhsExpr`.
This function assumes that `discrExpr`, lhsExpr` and `rhsExpr` are the corresponding expressions to
`discr`, `lhs` and `rhs`.
-/
def mkIte (discr lhs rhs : ReifiedBVLogical) (discrExpr lhsExpr rhsExpr : Expr) (origExpr : Expr) :
    M ReifiedBVLogical := do
  let boolExpr := .ite discr.bvExpr lhs.bvExpr rhs.bvExpr
  let expr :=
    mkApp4
      (mkConst ``BoolExpr.ite)
      (mkConst ``BVPred)
      discr.expr
      lhs.expr
      rhs.expr
  let proof := do
    let discrEvalExpr ← ReifiedBVLogical.mkEvalExpr discr.expr
    let lhsEvalExpr ← ReifiedBVLogical.mkEvalExpr lhs.expr
    let rhsEvalExpr ← ReifiedBVLogical.mkEvalExpr rhs.expr
    let discrProof? ← discr.evalsAtAtoms
    let lhsProof? ← lhs.evalsAtAtoms
    let rhsProof? ← rhs.evalsAtAtoms
    let some (discrProof, lhsProof, rhsProof) :=
      M.simplifyTernaryProof
        ReifiedBVLogical.mkRefl
        discrEvalExpr discrProof?
        lhsEvalExpr lhsProof?
        rhsEvalExpr rhsProof? | return none
    return mkApp9
      (mkConst ``Std.Tactic.BVDecide.Reflect.Bool.cond_congr)
      discrExpr lhsExpr rhsExpr
      discrEvalExpr lhsEvalExpr rhsEvalExpr
      discrProof lhsProof rhsProof
  return ⟨boolExpr, origExpr, proof, expr⟩

end ReifiedBVLogical

end Frontend
end Lean.Elab.Tactic.BVDecide
