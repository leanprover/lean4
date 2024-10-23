/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Std.Tactic.BVDecide.Bitblast.BVExpr.Basic
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Neg

/-!
This module contains the implementation of a bitblaster for `BitVec.sub`.
-/

namespace Std.Tactic.BVDecide

open Std.Sat

namespace BVExpr
namespace bitblast

variable [Hashable α] [DecidableEq α]

def blastSub (aig : AIG α) (input : AIG.BinaryRefVec aig w) : AIG.RefVecEntry α w :=
  let ⟨lhs, rhs⟩ := input
  let res := blastNeg aig rhs
  let aig := res.aig
  let negRhs := res.vec
  let lhs := lhs.cast <| AIG.LawfulVecOperator.le_size (f := blastNeg) ..

  blastAdd aig ⟨lhs, negRhs⟩

instance : AIG.LawfulVecOperator α AIG.BinaryRefVec blastSub where
  le_size := by
    intros
    unfold blastSub
    apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := blastAdd)
    apply AIG.LawfulVecOperator.le_size (f := blastNeg)
  decl_eq := by
    intros
    unfold blastSub
    rw [AIG.LawfulVecOperator.decl_eq (f := blastAdd)]
    rw [AIG.LawfulVecOperator.decl_eq (f := blastNeg)]
    apply AIG.LawfulVecOperator.lt_size_of_lt_aig_size (f := blastNeg)
    assumption
  

end bitblast
end BVExpr

end Std.Tactic.BVDecide
