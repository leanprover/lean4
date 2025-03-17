/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Std.Tactic.BVDecide.Bitblast.BVExpr.Basic
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Udiv

/-!
This module contains the implementation of a bitblaster for `BitVec.umod`. The implemented
circuit is a shift subtractor.
-/

namespace Std.Tactic.BVDecide

open Std.Sat

namespace BVExpr
namespace bitblast

variable [Hashable α] [DecidableEq α]

def blastUmod (aig : AIG α) (input : AIG.BinaryRefVec aig w) : AIG.RefVecEntry α w :=
  let res := blastConst aig 0#w
  let aig := res.aig
  let zero := res.vec
  let input := input.cast <| AIG.LawfulVecOperator.le_size (f := blastConst) ..

  let res := aig.mkConstCached false
  let aig := res.aig
  let falseRef := res.ref
  have := AIG.LawfulOperator.le_size (f := AIG.mkConstCached) ..
  let zero := zero.cast this
  let input := input.cast this

  let res := aig.mkConstCached true
  let aig := res.aig
  let trueRef := res.ref
  have := AIG.LawfulOperator.le_size (f := AIG.mkConstCached) ..
  let falseRef := falseRef.cast this
  let zero := zero.cast this
  let input := input.cast this

  let ⟨lhs, rhs⟩ := input

  let res := BVPred.mkEq aig ⟨rhs, zero⟩
  let aig := res.aig
  let discr := res.ref
  have := AIG.LawfulOperator.le_size (f := BVPred.mkEq) ..
  let falseRef := falseRef.cast this
  let trueRef := trueRef.cast this
  let zero := zero.cast this
  let lhs := lhs.cast this
  let rhs := rhs.cast this

  let res := blastUdiv.go aig w falseRef trueRef lhs rhs w 0 zero zero
  let aig := res.aig
  let modRes := res.r
  have := blastUdiv.go_le_size ..
  let discr := discr.cast this
  let lhs := lhs.cast this

  AIG.RefVec.ite aig ⟨discr, lhs, modRes⟩

instance : AIG.LawfulVecOperator α AIG.BinaryRefVec blastUmod where
  le_size := by
    intros
    unfold blastUmod
    apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := AIG.RefVec.ite)
    refine Nat.le_trans ?_ (by apply blastUdiv.go_le_size)
    apply AIG.LawfulOperator.le_size_of_le_aig_size (f := BVPred.mkEq)
    apply AIG.LawfulOperator.le_size_of_le_aig_size (f := AIG.mkConstCached)
    apply AIG.LawfulOperator.le_size_of_le_aig_size (f := AIG.mkConstCached)
    apply AIG.LawfulVecOperator.le_size (f := blastConst)
  decl_eq := by
    intros
    unfold blastUmod
    rw [AIG.LawfulVecOperator.decl_eq (f := AIG.RefVec.ite)]
    rw [blastUdiv.go_decl_eq]
    rw [AIG.LawfulOperator.decl_eq (f := BVPred.mkEq)]
    rw [AIG.LawfulOperator.decl_eq (f := AIG.mkConstCached)]
    rw [AIG.LawfulOperator.decl_eq (f := AIG.mkConstCached)]
    rw [AIG.LawfulVecOperator.decl_eq (f := blastConst)]
    · apply AIG.LawfulVecOperator.lt_size_of_lt_aig_size (f := blastConst)
      assumption
    · apply AIG.LawfulOperator.lt_size_of_lt_aig_size (f := AIG.mkConstCached)
      apply AIG.LawfulVecOperator.lt_size_of_lt_aig_size (f := blastConst)
      assumption
    · apply AIG.LawfulOperator.lt_size_of_lt_aig_size (f := AIG.mkConstCached)
      apply AIG.LawfulOperator.lt_size_of_lt_aig_size (f := AIG.mkConstCached)
      apply AIG.LawfulVecOperator.lt_size_of_lt_aig_size (f := blastConst)
      assumption
    · apply AIG.LawfulOperator.lt_size_of_lt_aig_size (f := BVPred.mkEq)
      apply AIG.LawfulOperator.lt_size_of_lt_aig_size (f := AIG.mkConstCached)
      apply AIG.LawfulOperator.lt_size_of_lt_aig_size (f := AIG.mkConstCached)
      apply AIG.LawfulVecOperator.lt_size_of_lt_aig_size (f := blastConst)
      assumption
    · refine Nat.le_trans ?_ (by apply blastUdiv.go_le_size)
      apply AIG.LawfulOperator.lt_size_of_lt_aig_size (f := BVPred.mkEq)
      apply AIG.LawfulOperator.lt_size_of_lt_aig_size (f := AIG.mkConstCached)
      apply AIG.LawfulOperator.lt_size_of_lt_aig_size (f := AIG.mkConstCached)
      apply AIG.LawfulVecOperator.lt_size_of_lt_aig_size (f := blastConst)
      assumption

end bitblast
end BVExpr

end Std.Tactic.BVDecide
