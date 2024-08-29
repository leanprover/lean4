/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Eq
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Ult
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.GetLsbD
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Expr

/-!
This module contains the implementation of a bitblaster for predicates over `BitVec` expressions
(`BVPred`).
-/

namespace Std.Tactic.BVDecide

open Std.Sat

namespace BVPred

def bitblast (aig : AIG BVBit) (pred : BVPred) : AIG.Entrypoint BVBit :=
  match pred with
  | .bin lhs op rhs =>
    let res := lhs.bitblast aig
    let aig := res.aig
    let lhsRefs := res.vec
    let res := rhs.bitblast aig
    let aig := res.aig
    let rhsRefs := res.vec
    let lhsRefs := lhsRefs.cast <| AIG.LawfulVecOperator.le_size (f := BVExpr.bitblast) ..
    match op with
    | .eq => mkEq aig ⟨lhsRefs, rhsRefs⟩
    | .ult => mkUlt aig ⟨lhsRefs, rhsRefs⟩
  | .getLsbD expr idx =>
    /-
    Note: This blasts the entire expression up to `w` despite only needing it up to `idx`.
    However the vast majority of operations are interested in all bits so the API is currently
    not designed to support this use case.
    -/
    let res := expr.bitblast aig
    let aig := res.aig
    let refs := res.vec
    blastGetLsbD aig ⟨refs, idx⟩

instance : AIG.LawfulOperator BVBit (fun _ => BVPred) bitblast where
  le_size := by
    intro aig pred
    unfold bitblast
    cases pred with
    | bin lhs op rhs =>
      cases op with
      | eq =>
        apply AIG.LawfulOperator.le_size_of_le_aig_size (f := mkEq)
        apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := BVExpr.bitblast)
        apply AIG.LawfulVecOperator.le_size (f := BVExpr.bitblast)
      | ult =>
        apply AIG.LawfulOperator.le_size_of_le_aig_size (f := mkUlt)
        apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := BVExpr.bitblast)
        apply AIG.LawfulVecOperator.le_size (f := BVExpr.bitblast)
    | getLsbD expr idx =>
      apply AIG.LawfulOperator.le_size_of_le_aig_size (f := blastGetLsbD)
      apply AIG.LawfulVecOperator.le_size (f := BVExpr.bitblast)
  decl_eq := by
    intro aig pred idx h1 h2
    cases pred with
    | bin lhs op rhs =>
      cases op with
      | eq =>
        simp only [bitblast]
        rw [AIG.LawfulOperator.decl_eq (f := mkEq)]
        rw [AIG.LawfulVecOperator.decl_eq (f := BVExpr.bitblast)]
        rw [AIG.LawfulVecOperator.decl_eq (f := BVExpr.bitblast)]
        · apply AIG.LawfulVecOperator.lt_size_of_lt_aig_size (f := BVExpr.bitblast)
          assumption
        · apply AIG.LawfulVecOperator.lt_size_of_lt_aig_size (f := BVExpr.bitblast)
          apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := BVExpr.bitblast)
          assumption
      | ult =>
        simp only [bitblast]
        rw [AIG.LawfulOperator.decl_eq (f := mkUlt)]
        rw [AIG.LawfulVecOperator.decl_eq (f := BVExpr.bitblast)]
        rw [AIG.LawfulVecOperator.decl_eq (f := BVExpr.bitblast)]
        · apply AIG.LawfulVecOperator.lt_size_of_lt_aig_size (f := BVExpr.bitblast)
          assumption
        · apply AIG.LawfulVecOperator.lt_size_of_lt_aig_size (f := BVExpr.bitblast)
          apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := BVExpr.bitblast)
          assumption
    | getLsbD expr idx =>
      simp only [bitblast]
      rw [AIG.LawfulOperator.decl_eq (f := blastGetLsbD)]
      rw [AIG.LawfulVecOperator.decl_eq (f := BVExpr.bitblast)]
      apply AIG.LawfulVecOperator.lt_size_of_lt_aig_size (f := BVExpr.bitblast)
      assumption

end BVPred

end Std.Tactic.BVDecide
