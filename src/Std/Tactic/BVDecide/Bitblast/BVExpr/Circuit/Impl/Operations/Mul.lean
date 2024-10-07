/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Std.Tactic.BVDecide.Bitblast.BVExpr.Basic
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Add
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.ShiftLeft
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Const

/-!
This module contains the implementation of a bitblaster for `BitVec.mul`. The implemented
circuit mirrors the behavior of `BitVec.mulRec`.

Note that the implementation performs a symbolic branch over the bits of the right hand side.
Thus if the right hand side is (partially) known through constant propagation etc. the symbolic
branches will be (partially) constant folded away by the AIG optimizer. The preprocessing of
`blastMul` ensures that the value with more known bits always end up on the right hand side for
this reason.
-/

namespace Std.Tactic.BVDecide

open Std.Sat

namespace BVExpr
namespace bitblast

def blastMul (aig : AIG BVBit) (input : AIG.BinaryRefVec aig w) : AIG.RefVecEntry BVBit w :=
  if input.lhs.countKnown < input.rhs.countKnown then
    blast aig input
  else
    let ⟨lhs, rhs⟩ := input
    blast aig ⟨rhs, lhs⟩
where
  blast (aig : AIG BVBit) (input : AIG.BinaryRefVec aig w) : AIG.RefVecEntry BVBit w :=
    if h : w = 0 then
      ⟨aig, h ▸ .empty⟩
    else
      have : 0 < w := by omega
      let res := blastConst aig 0
      let aig := res.aig
      let zero := res.vec
      have := AIG.LawfulVecOperator.le_size (f := blastConst) ..
      let input := input.cast this
      let ⟨lhs, rhs⟩ := input
      let res := AIG.RefVec.ite aig ⟨rhs.get 0 (by assumption), lhs, zero⟩
      let aig := res.aig
      let acc := res.vec
      have := AIG.LawfulVecOperator.le_size (f := AIG.RefVec.ite) ..
      let lhs := lhs.cast this
      let rhs := rhs.cast this
      go aig lhs rhs 1 acc

  go (aig : AIG BVBit) (lhs rhs : AIG.RefVec aig w) (curr : Nat)
      (acc : AIG.RefVec aig w) :
      AIG.RefVecEntry BVBit w :=
    if h : curr < w then
      let res := blastShiftLeftConst aig ⟨lhs, curr⟩
      let aig := res.aig
      let shifted := res.vec
      have := by apply AIG.LawfulVecOperator.le_size (f := blastShiftLeftConst)
      let lhs := lhs.cast this
      let rhs := rhs.cast this
      let acc := acc.cast this
      let res := blastAdd aig ⟨acc, shifted⟩
      let aig := res.aig
      let added := res.vec
      have := by apply AIG.LawfulVecOperator.le_size (f := blastAdd)
      let lhs := lhs.cast this
      let rhs := rhs.cast this
      let acc := acc.cast this
      let res := AIG.RefVec.ite aig ⟨rhs.get curr h, added, acc⟩
      let aig := res.aig
      let acc := res.vec
      have := by apply AIG.LawfulVecOperator.le_size (f := AIG.RefVec.ite)
      let lhs := lhs.cast this
      let rhs := rhs.cast this
      go aig lhs rhs (curr + 1) acc
    else
      ⟨aig, acc⟩

namespace blastMul

theorem go_le_size {w : Nat} (aig : AIG BVBit) (curr : Nat) (acc : AIG.RefVec aig w)
    (lhs rhs : AIG.RefVec aig w) :
    aig.decls.size ≤ (go aig lhs rhs curr acc).aig.decls.size := by
  unfold go
  split
  · dsimp only
    refine Nat.le_trans ?_ (by apply go_le_size)
    apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := AIG.RefVec.ite)
    apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := blastAdd)
    apply AIG.LawfulVecOperator.le_size (f := blastShiftLeftConst)
  · simp

theorem go_decl_eq {w : Nat} (aig : AIG BVBit) (curr : Nat) (acc : AIG.RefVec aig w)
    (lhs rhs : AIG.RefVec aig w) :
    ∀ (idx : Nat) (h1) (h2),
       (go aig lhs rhs curr acc).aig.decls[idx]'h2 = aig.decls[idx]'h1 := by
  generalize hgo : go aig lhs rhs curr acc = res
  unfold go at hgo
  split at hgo
  · dsimp only at hgo
    rw [← hgo]
    intro idx h1 h2
    rw [go_decl_eq]
    rw [AIG.LawfulVecOperator.decl_eq (f := AIG.RefVec.ite)]
    rw [AIG.LawfulVecOperator.decl_eq (f := blastAdd)]
    rw [AIG.LawfulVecOperator.decl_eq (f := blastShiftLeftConst)]
    · apply AIG.LawfulVecOperator.lt_size_of_lt_aig_size (f := blastShiftLeftConst)
      assumption
    · apply AIG.LawfulVecOperator.lt_size_of_lt_aig_size (f := blastAdd)
      apply AIG.LawfulVecOperator.lt_size_of_lt_aig_size (f := blastShiftLeftConst)
      assumption
    · apply AIG.LawfulVecOperator.lt_size_of_lt_aig_size (f := AIG.RefVec.ite)
      apply AIG.LawfulVecOperator.lt_size_of_lt_aig_size (f := blastAdd)
      apply AIG.LawfulVecOperator.lt_size_of_lt_aig_size (f := blastShiftLeftConst)
      assumption
  · simp [← hgo]

instance : AIG.LawfulVecOperator BVBit AIG.BinaryRefVec blast where
  le_size := by
    intros
    unfold blast
    split
    · simp
    · dsimp only
      refine Nat.le_trans ?_ (by apply blastMul.go_le_size)
      apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := AIG.RefVec.ite)
      apply AIG.LawfulVecOperator.le_size (f := blastConst)
  decl_eq := by
    intros
    unfold blast
    split
    · simp
    · dsimp only
      rw [blastMul.go_decl_eq]
      rw [AIG.LawfulVecOperator.decl_eq (f := AIG.RefVec.ite)]
      rw [AIG.LawfulVecOperator.decl_eq (f := blastConst)]
      · apply AIG.LawfulVecOperator.lt_size_of_lt_aig_size (f := blastConst)
        assumption
      · apply AIG.LawfulVecOperator.lt_size_of_lt_aig_size (f := AIG.RefVec.ite)
        apply AIG.LawfulVecOperator.lt_size_of_lt_aig_size (f := blastConst)
        assumption

end blastMul

instance : AIG.LawfulVecOperator BVBit AIG.BinaryRefVec blastMul where
  le_size := by
    intros
    unfold blastMul
    split <;> apply AIG.LawfulVecOperator.le_size (f := blastMul.blast)
  decl_eq := by
    intros
    unfold blastMul
    split <;> rw [AIG.LawfulVecOperator.decl_eq (f := blastMul.blast)]

end bitblast
end BVExpr

end Std.Tactic.BVDecide
