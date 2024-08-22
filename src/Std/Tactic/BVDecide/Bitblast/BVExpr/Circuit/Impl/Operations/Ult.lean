/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Carry
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Not

/-!
This module contains the implementation of a bitblaster for `BitVec.ult`. The implementation
makes use of the reduction provided by `BitVec.ult_eq_not_carry`.
-/

namespace Std.Tactic.BVDecide

open Std.Sat

namespace BVPred

variable [Hashable α] [DecidableEq α]

def mkUlt (aig : AIG α) (pair : AIG.BinaryRefVec aig w) : AIG.Entrypoint α :=
  let ⟨lhsRefs, rhsRefs⟩ := pair
  let res := BVExpr.bitblast.blastNot aig rhsRefs
  let aig := res.aig
  let rhsNotRefs := res.vec
  let res := aig.mkConstCached true
  let aig := res.aig
  let trueRef := res.ref
  let lhsRefs := lhsRefs.cast <| by
    apply AIG.LawfulOperator.le_size_of_le_aig_size (f := AIG.mkConstCached)
    apply AIG.LawfulVecOperator.le_size (f := BVExpr.bitblast.blastNot)
  let rhsNotRefs := rhsNotRefs.cast <| AIG.LawfulOperator.le_size (f := AIG.mkConstCached) ..
  let res := BVExpr.bitblast.mkOverflowBit aig ⟨_, ⟨lhsRefs, rhsNotRefs⟩, trueRef⟩
  let aig := res.aig
  let overflowRef := res.ref
  aig.mkNotCached overflowRef

instance {w : Nat} : AIG.LawfulOperator α (AIG.BinaryRefVec · w) mkUlt where
  le_size := by
    intros
    unfold mkUlt
    dsimp only
    apply AIG.LawfulOperator.le_size_of_le_aig_size (f := AIG.mkNotCached)
    apply AIG.LawfulOperator.le_size_of_le_aig_size (f := BVExpr.bitblast.mkOverflowBit)
    apply AIG.LawfulOperator.le_size_of_le_aig_size (f := AIG.mkConstCached)
    apply AIG.LawfulVecOperator.le_size (f := BVExpr.bitblast.blastNot)
  decl_eq := by
    intros
    unfold mkUlt
    dsimp only
    rw [AIG.LawfulOperator.decl_eq (f := AIG.mkNotCached)]
    rw [AIG.LawfulOperator.decl_eq (f := BVExpr.bitblast.mkOverflowBit)]
    rw [AIG.LawfulOperator.decl_eq (f := AIG.mkConstCached)]
    rw [AIG.LawfulVecOperator.decl_eq (f := BVExpr.bitblast.blastNot)]
    · apply AIG.LawfulVecOperator.lt_size_of_lt_aig_size (f := BVExpr.bitblast.blastNot)
      assumption
    · apply AIG.LawfulOperator.lt_size_of_lt_aig_size (f := AIG.mkConstCached)
      apply AIG.LawfulVecOperator.lt_size_of_lt_aig_size (f := BVExpr.bitblast.blastNot)
      assumption
    · apply AIG.LawfulOperator.lt_size_of_lt_aig_size (f := BVExpr.bitblast.mkOverflowBit)
      apply AIG.LawfulOperator.lt_size_of_lt_aig_size (f := AIG.mkConstCached)
      apply AIG.LawfulVecOperator.lt_size_of_lt_aig_size (f := BVExpr.bitblast.blastNot)
      assumption

end BVPred

end Std.Tactic.BVDecide
