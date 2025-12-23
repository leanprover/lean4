/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Neg
import Init.Grind

@[expose] public section

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

@[grind! .]
theorem blastSub_le_size (aig : AIG α) (input : aig.BinaryRefVec w) :
    aig.decls.size ≤ (blastSub aig input).aig.decls.size := by
  intros
  unfold blastSub
  grind

@[grind =]
theorem blastSub_decl_eq (aig : AIG α) (input : aig.BinaryRefVec w) (idx : Nat)
   (h1 : idx < aig.decls.size) (h2 : idx < (blastSub aig input).aig.decls.size) :
   (blastSub aig input).aig.decls[idx] = aig.decls[idx] := by
  intros
  unfold blastSub
  grind

instance : AIG.LawfulVecOperator α AIG.BinaryRefVec blastSub where
  le_size := blastSub_le_size
  decl_eq := blastSub_decl_eq

end bitblast
end BVExpr

end Std.Tactic.BVDecide
