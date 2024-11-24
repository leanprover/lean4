/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Lean.Elab.Tactic.BVDecide.Frontend.BVDecide.ReifiedBVExpr

/-!
Provides the logic for reifying predicates on `BitVec`.
-/

namespace Lean.Elab.Tactic.BVDecide
namespace Frontend

open Std.Tactic.BVDecide
open Lean.Meta

namespace ReifiedBVPred

/--
Construct an uninterpreted `Bool` atom from `t`.
-/
def boolAtom (t : Expr) : M (Option ReifiedBVPred) := do
  /-
  Idea: we have t : Bool here, let's construct:
    BitVec.ofBool t : BitVec 1
  as an atom. Then construct the BVPred corresponding to
    BitVec.getLsb (BitVec.ofBool t) 0 : Bool
  We can prove that this is equivalent to `t`. This allows us to have boolean variables in BVPred.
  -/
  let ty ← inferType t
  let_expr Bool := ty | return none
  let atom ← ReifiedBVExpr.mkAtom (mkApp (mkConst ``BitVec.ofBool) t) 1 false
  let bvExpr : BVPred := .getLsbD atom.bvExpr 0
  let expr := mkApp3 (mkConst ``BVPred.getLsbD) (toExpr 1) atom.expr (toExpr 0)
  let proof := do
    let atomEval ← ReifiedBVExpr.mkEvalExpr atom.width atom.expr
    let atomProof ← atom.evalsAtAtoms
    return mkApp3
      (mkConst ``Std.Tactic.BVDecide.Reflect.BitVec.ofBool_congr)
      t
      atomEval
      atomProof
  return some ⟨bvExpr, proof, expr⟩

/--
Construct the reified version of applying the predicate in `pred` to `lhs` and `rhs`.
This function assumes that `lhsExpr` and `rhsExpr` are the corresponding expressions to `lhs`
and `rhs`.
-/
def mkBinPred (lhs rhs : ReifiedBVExpr) (lhsExpr rhsExpr : Expr) (pred : BVBinPred) :
    M (Option ReifiedBVPred) := do
  if h : lhs.width = rhs.width then
    let congrThm := congrThmofBinPred pred
    let bvExpr : BVPred := .bin (w := lhs.width) lhs.bvExpr pred (h ▸ rhs.bvExpr)
    let expr :=
      mkApp4
        (mkConst ``BVPred.bin)
        (toExpr lhs.width)
        lhs.expr
        (toExpr pred)
        rhs.expr
    let proof := do
      let lhsEval ← ReifiedBVExpr.mkEvalExpr lhs.width lhs.expr
      let lhsProof ← lhs.evalsAtAtoms
      let rhsEval ← ReifiedBVExpr.mkEvalExpr rhs.width rhs.expr
      let rhsProof ← rhs.evalsAtAtoms
      return mkApp7
        (mkConst congrThm)
        (toExpr lhs.width)
        lhsExpr rhsExpr lhsEval rhsEval
        lhsProof
        rhsProof
    return some ⟨bvExpr, proof, expr⟩
  else
    return none
where
  congrThmofBinPred (pred : BVBinPred) : Name :=
    match pred with
    | .eq => ``Std.Tactic.BVDecide.Reflect.BitVec.beq_congr
    | .ult => ``Std.Tactic.BVDecide.Reflect.BitVec.ult_congr

/--
Construct the reified version of `BitVec.getLsbD subExpr idx`.
This function assumes that `subExpr` is the expression corresponding to `sub`.
-/
def mkGetLsbD (sub : ReifiedBVExpr) (subExpr : Expr) (idx : Nat) : M ReifiedBVPred := do
  let bvExpr : BVPred := .getLsbD sub.bvExpr idx
  let idxExpr := toExpr idx
  let expr := mkApp3 (mkConst ``BVPred.getLsbD) (toExpr sub.width) sub.expr idxExpr
  let proof := do
    let subEval ← ReifiedBVExpr.mkEvalExpr sub.width sub.expr
    let subProof ← sub.evalsAtAtoms
    return mkApp5
      (mkConst ``Std.Tactic.BVDecide.Reflect.BitVec.getLsbD_congr)
      idxExpr
      (toExpr sub.width)
      subExpr
      subEval
      subProof
  return ⟨bvExpr, proof, expr⟩

end ReifiedBVPred

end Frontend
end Lean.Elab.Tactic.BVDecide
