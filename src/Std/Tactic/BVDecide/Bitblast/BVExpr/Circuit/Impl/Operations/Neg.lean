/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Std.Tactic.BVDecide.Bitblast.BVExpr.Basic
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Add
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Not
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Const

/-!
This module contains the implementation of a bitblaster for `BitVec.neg`.
-/

namespace Std.Tactic.BVDecide

open Std.Sat

namespace BVExpr
namespace bitblast

variable [Hashable α] [DecidableEq α]

def blastNeg (aig : AIG α) (input : AIG.RefVec aig w) : AIG.RefVecEntry α w :=
  let res := blastNot aig input
  let aig := res.aig
  let notInput := res.vec

  let res := blastConst aig 1#w
  let aig := res.aig
  let one := res.vec
  let notInput := notInput.cast <| AIG.LawfulVecOperator.le_size (f := blastConst) ..

  blastAdd aig ⟨notInput, one⟩

instance : AIG.LawfulVecOperator α AIG.RefVec blastNeg where
  le_size := by
    intros
    unfold blastNeg
    dsimp only
    apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := blastAdd)
    apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := blastConst)
    apply AIG.LawfulVecOperator.le_size (f := blastNot)
  decl_eq := by
    intros
    unfold blastNeg
    dsimp only
    rw [AIG.LawfulVecOperator.decl_eq (f := blastAdd)]
    rw [AIG.LawfulVecOperator.decl_eq (f := blastConst)]
    rw [AIG.LawfulVecOperator.decl_eq (f := blastNot)]
    · apply AIG.LawfulVecOperator.lt_size_of_lt_aig_size (f := blastNot)
      assumption
    · apply AIG.LawfulVecOperator.lt_size_of_lt_aig_size (f := blastConst)
      apply AIG.LawfulVecOperator.lt_size_of_lt_aig_size (f := blastNot)
      assumption

end bitblast
end BVExpr

end Std.Tactic.BVDecide
