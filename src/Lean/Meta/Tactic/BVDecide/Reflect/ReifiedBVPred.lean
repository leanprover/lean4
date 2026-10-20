/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Lean.Meta.Tactic.BVDecide.Reflect.Basic
import Lean.Meta.Tactic.BVDecide.Reflect.ReifiedBVExpr
import Lean.Meta.Sym.InferType

/-!
Provides the logic for reifying predicates on `BitVec`.
-/

namespace Lean.Meta.Tactic.BVDecide

open Std.Tactic.BVDecide

namespace ReifiedBVPred
/--
Construct the reified version of applying the predicate in `pred` to `lhs` and `rhs`.
This function assumes that `lhsExpr` and `rhsExpr` are the corresponding expressions to `lhs`
and `rhs`.
-/
public def mkBinPred (lhs rhs : ReifiedBVExpr) (lhsExpr rhsExpr : Expr) (pred : BVBinPred)
    (origExpr : Expr) : ReifyM (Option ReifiedBVPred) := do
  if h : lhs.width = rhs.width then
    let congrThm := congrThmOfBinPred pred
    let bvExpr : BVPred := .bin (w := lhs.width) lhs.bvExpr pred (h ▸ rhs.bvExpr)
    let expr ← Sym.share <| mkApp4 (mkConst ``BVPred.bin) (toExpr lhs.width) lhs.expr (toExpr pred) rhs.expr
    let proof := do
      let lhsEval ← ReifiedBVExpr.mkEvalExpr lhs.width lhs.expr
      let rhsEval ← ReifiedBVExpr.mkEvalExpr rhs.width rhs.expr
      let lhsProof? ← lhs.evalsAtAtoms
      let rhsProof? ← rhs.evalsAtAtoms
      let some (lhsProof, rhsProof) :=
        ReifyM.simplifyBinaryProof
          (ReifiedBVExpr.mkBVRefl lhs.width)
          lhsEval lhsProof?
          rhsEval rhsProof? | return none
      return mkApp7
        (mkConst congrThm)
        (toExpr lhs.width)
        lhsExpr rhsExpr lhsEval rhsEval
        lhsProof
        rhsProof
    return some ⟨bvExpr, origExpr, proof, expr⟩
  else
    return none
where
  congrThmOfBinPred (pred : BVBinPred) : Name :=
    match pred with
    | .eq => ``Std.Tactic.BVDecide.Reflect.BitVec.beq_congr
    | .ult => ``Std.Tactic.BVDecide.Reflect.BitVec.ult_congr

/--
Construct the reified version of `BitVec.getLsbD subExpr idx`.
This function assumes that `subExpr` is the expression corresponding to `sub`.
-/
public def mkGetLsbD (sub : ReifiedBVExpr) (subExpr : Expr) (idx : Nat) (origExpr : Expr) :
    ReifyM ReifiedBVPred := do
  let bvExpr : BVPred := .getLsbD sub.bvExpr idx
  let idxExpr := toExpr idx
  let expr ← Sym.share <| mkApp3 (mkConst ``BVPred.getLsbD) (toExpr sub.width) sub.expr idxExpr
  let proof := do
    -- This is safe as `getLsbD_congr` holds definitionally if the arguments are defeq.
    let some subProof ← sub.evalsAtAtoms | return none
    let subEval ← ReifiedBVExpr.mkEvalExpr sub.width sub.expr
    return mkApp5
      (mkConst ``Std.Tactic.BVDecide.Reflect.BitVec.getLsbD_congr)
      idxExpr
      (toExpr sub.width)
      subExpr
      subEval
      subProof
  return ⟨bvExpr, origExpr, proof, expr⟩

end ReifiedBVPred

end Lean.Meta.Tactic.BVDecide
