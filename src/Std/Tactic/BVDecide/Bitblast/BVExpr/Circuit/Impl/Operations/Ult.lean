/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Carry
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Not
import Init.Grind

@[expose] public section

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
  let trueRef := aig.mkConstCached true
  let aig := res.aig
  let lhsRefs := lhsRefs.cast <| by
    apply AIG.LawfulVecOperator.le_size (f := BVExpr.bitblast.blastNot)
  let res := BVExpr.bitblast.mkOverflowBit aig ⟨_, ⟨lhsRefs, rhsNotRefs⟩, trueRef⟩
  let aig := res.aig
  let overflowRef := res.ref
  aig.mkNotCached overflowRef

@[grind! .]
theorem mkUlt_le_size (aig : AIG α) (input : aig.BinaryRefVec w) :
    aig.decls.size ≤ (mkUlt aig input).aig.decls.size := by
  intros
  unfold mkUlt
  grind

@[grind =]
theorem mkUlt_decl_eq (aig : AIG α) (input : aig.BinaryRefVec w) (idx : Nat)
    (h1 : idx < aig.decls.size) (h2 : idx < (mkUlt aig input).aig.decls.size) :
    (mkUlt aig input).aig.decls[idx] = aig.decls[idx] := by
  intros
  unfold mkUlt
  grind

instance {w : Nat} : AIG.LawfulOperator α (AIG.BinaryRefVec · w) mkUlt where
  le_size := mkUlt_le_size
  decl_eq := mkUlt_decl_eq

end BVPred

end Std.Tactic.BVDecide
