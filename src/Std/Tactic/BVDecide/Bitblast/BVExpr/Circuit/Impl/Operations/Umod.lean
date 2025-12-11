/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Udiv
import Init.Grind

@[expose] public section

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
  let zero := blastConst aig 0#w
  let ⟨lhs, rhs⟩ := input

  let res := BVPred.mkEq aig ⟨rhs, zero⟩
  let aig := res.aig
  let discr := res.ref
  have := AIG.LawfulOperator.le_size (f := BVPred.mkEq) ..
  let zero := zero.cast this
  let lhs := lhs.cast this
  let rhs := rhs.cast this

  let res := blastUdiv.go aig w lhs rhs w 0 zero zero
  let aig := res.aig
  let modRes := res.r
  have := blastUdiv.go_le_size ..
  let discr := discr.cast this
  let lhs := lhs.cast this

  AIG.RefVec.ite aig ⟨discr, lhs, modRes⟩

@[grind! .]
theorem blastUmod_le_size (aig : AIG α) (input : aig.BinaryRefVec w) :
    aig.decls.size ≤ (blastUmod aig input).aig.decls.size := by
  intros
  unfold blastUmod
  grind

@[grind =]
theorem blastUmod_decl_eq (aig : AIG α) (input : aig.BinaryRefVec w) (idx : Nat)
    (h1 : idx < aig.decls.size) (h2 : idx < (blastUmod aig input).aig.decls.size) :
    (blastUmod aig input).aig.decls[idx] = aig.decls[idx] := by
  intros
  unfold blastUmod
  grind

instance : AIG.LawfulVecOperator α AIG.BinaryRefVec blastUmod where
  le_size := blastUmod_le_size
  decl_eq := blastUmod_decl_eq

end bitblast
end BVExpr

end Std.Tactic.BVDecide
