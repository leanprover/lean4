/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Add
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Not
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Const
import Init.Grind

@[expose] public section

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

  let one := blastConst aig 1#w

  blastAdd aig ⟨notInput, one⟩

@[grind! .]
theorem blastNeg_le_size (aig : AIG α) (input : aig.RefVec w) :
    aig.decls.size ≤ (blastNeg aig input).aig.decls.size := by
  intros
  unfold blastNeg
  grind

@[grind =]
theorem blastNeg_decl_eq (aig : AIG α) (input : aig.RefVec w) (idx : Nat)
    (h1 : idx < aig.decls.size) (h2 : idx < (blastNeg aig input).aig.decls.size) :
    (blastNeg aig input).aig.decls[idx] = aig.decls[idx] := by
  intros
  unfold blastNeg
  grind

instance : AIG.LawfulVecOperator α AIG.RefVec blastNeg where
  le_size := blastNeg_le_size
  decl_eq := blastNeg_decl_eq

end bitblast
end BVExpr

end Std.Tactic.BVDecide
