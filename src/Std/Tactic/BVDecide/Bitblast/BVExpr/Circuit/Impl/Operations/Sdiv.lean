/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Std.Sat.AIG.If
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Neg
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Udiv

/-!
This module contains the implementation of a bitblaster for `BitVec.sdiv`. The implemented
circuit is the reduction to udiv.
-/

namespace Std.Tactic.BVDecide

open Std.Sat

namespace BVExpr
namespace bitblast

variable [Hashable α] [DecidableEq α]

def blastSdiv (aig : AIG α) (input : AIG.BinaryRefVec aig w) : AIG.RefVecEntry α w :=
  if h : w = 0 then
    ⟨aig, h ▸ AIG.RefVec.empty⟩
  else
    let ⟨lhs, rhs⟩ := input
    let res := blastNeg aig lhs
    let aig := res.aig
    let negLhs := res.vec
    have := AIG.LawfulVecOperator.le_size (f := blastNeg) ..
    let lhs := lhs.cast this
    let rhs := rhs.cast this
    let res := blastNeg aig rhs
    let aig := res.aig
    let negRhs := res.vec
    have := AIG.LawfulVecOperator.le_size (f := blastNeg) ..
    let lhs := lhs.cast this
    let rhs := rhs.cast this
    let negLhs := negLhs.cast this

    let res := blastUdiv aig ⟨lhs, rhs⟩
    let aig := res.aig
    let lposRpos := res.vec
    have := AIG.LawfulVecOperator.le_size (f := blastUdiv) ..
    let lhs := lhs.cast this
    let rhs := rhs.cast this
    let negRhs := negRhs.cast this
    let negLhs := negLhs.cast this

    let res := blastUdiv aig ⟨lhs, negRhs⟩
    let aig := res.aig
    let ldivnr := res.vec
    let res := blastNeg aig ldivnr
    let aig := res.aig
    let lposRneg := res.vec
    have := by
      apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := blastNeg)
      apply AIG.LawfulVecOperator.le_size (f := blastUdiv)
    let lhs := lhs.cast this
    let rhs := rhs.cast this
    let negRhs := negRhs.cast this
    let negLhs := negLhs.cast this
    let lposRpos := lposRpos.cast this

    let res := blastUdiv aig ⟨negLhs, rhs⟩
    let aig := res.aig
    let nldivr := res.vec
    let res := blastNeg aig nldivr
    let aig := res.aig
    let lnegRpos := res.vec
    have := by
      apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := blastNeg)
      apply AIG.LawfulVecOperator.le_size (f := blastUdiv)
    let lhs := lhs.cast this
    let rhs := rhs.cast this
    let negRhs := negRhs.cast this
    let negLhs := negLhs.cast this
    let lposRpos := lposRpos.cast this
    let lposRneg := lposRneg.cast this

    let res := blastUdiv aig ⟨negLhs, negRhs⟩
    let aig := res.aig
    let lnegRneg := res.vec
    have := AIG.LawfulVecOperator.le_size (f := blastUdiv) ..
    let lhs := lhs.cast this
    let rhs := rhs.cast this
    let lposRpos := lposRpos.cast this
    let lposRneg := lposRneg.cast this
    let lnegRpos := lnegRpos.cast this

    let res := AIG.RefVec.ite aig ⟨rhs.get (w - 1) (by omega), lposRneg, lposRpos⟩
    let aig := res.aig
    let lposHalf := res.vec
    have := AIG.LawfulVecOperator.le_size (f := AIG.RefVec.ite) ..
    let lhs := lhs.cast this
    let rhs := rhs.cast this
    let lnegRneg := lnegRneg.cast this
    let lnegRpos := lnegRpos.cast this

    let res := AIG.RefVec.ite aig ⟨rhs.get (w - 1) (by omega), lnegRneg, lnegRpos⟩
    let aig := res.aig
    let lnegHalf := res.vec
    have := AIG.LawfulVecOperator.le_size (f := AIG.RefVec.ite) ..
    let lhs := lhs.cast this
    let lposHalf := lposHalf.cast this

    AIG.RefVec.ite aig ⟨lhs.get (w - 1) (by omega), lnegHalf, lposHalf⟩

instance : AIG.LawfulVecOperator α AIG.BinaryRefVec blastSdiv where
  le_size := sorry
  decl_eq := sorry

end bitblast
end BVExpr

end Std.Tactic.BVDecide
