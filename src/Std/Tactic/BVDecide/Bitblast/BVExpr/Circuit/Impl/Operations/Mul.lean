/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Add
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.ShiftLeft
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Const
import Init.Grind

@[expose] public section

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

variable [Hashable α] [DecidableEq α]

namespace BVExpr
namespace bitblast

def blastMul (aig : AIG α) (input : AIG.BinaryRefVec aig w) : AIG.RefVecEntry α w :=
  if input.lhs.countKnown < input.rhs.countKnown then
    blast aig input
  else
    let ⟨lhs, rhs⟩ := input
    blast aig ⟨rhs, lhs⟩
where
  blast (aig : AIG α) (input : AIG.BinaryRefVec aig w) : AIG.RefVecEntry α w :=
    if h : w = 0 then
      ⟨aig, h ▸ .empty⟩
    else
      have : 0 < w := by omega
      let zero := blastConst aig 0
      let ⟨lhs, rhs⟩ := input
      let res := AIG.RefVec.ite aig ⟨rhs.get 0 (by assumption), lhs, zero⟩
      let aig := res.aig
      let acc := res.vec
      have := AIG.LawfulVecOperator.le_size (f := AIG.RefVec.ite) ..
      let lhs := lhs.cast this
      let rhs := rhs.cast this
      go aig lhs rhs 1 acc

  go (aig : AIG α) (lhs rhs : AIG.RefVec aig w) (curr : Nat) (acc : AIG.RefVec aig w) :
      AIG.RefVecEntry α w :=
    if h : curr < w then
      -- If the rhs is false we can skip this iteration as we would add zero
      if aig.isConstant (rhs.get curr h) false then
        go aig lhs rhs (curr + 1) acc
      else
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

@[grind! .]
theorem go_le_size {w : Nat} (aig : AIG α) (curr : Nat) (acc : AIG.RefVec aig w)
    (lhs rhs : AIG.RefVec aig w) :
    aig.decls.size ≤ (go aig lhs rhs curr acc).aig.decls.size := by
  unfold go
  split
  · split
    · apply go_le_size
    · dsimp only
      refine Nat.le_trans ?_ (by apply go_le_size)
      grind
  · simp

@[grind =]
theorem go_decl_eq {w : Nat} (aig : AIG α) (curr : Nat) (acc : AIG.RefVec aig w)
    (lhs rhs : AIG.RefVec aig w) :
    ∀ (idx : Nat) (h1) (h2),
       (go aig lhs rhs curr acc).aig.decls[idx]'h2 = aig.decls[idx]'h1 := by
  generalize hgo : go aig lhs rhs curr acc = res
  unfold go at hgo
  split at hgo
  · split at hgo
    · rw [← hgo]
      intro idx h1 h2
      rw [go_decl_eq]
    · dsimp only at hgo
      rw [← hgo]
      intro idx h1 h2
      rw [go_decl_eq]
      all_goals grind
  · simp [← hgo]

instance : AIG.LawfulVecOperator α AIG.BinaryRefVec blast where
  le_size := by
    intros
    unfold blast
    grind
  decl_eq := by
    intros
    unfold blast
    grind

end blastMul

@[grind! .]
theorem blastMul_le_size (aig : AIG α) (input : aig.BinaryRefVec w) :
    aig.decls.size ≤ (blastMul aig input).aig.decls.size := by
  intros
  unfold blastMul
  split <;> apply AIG.LawfulVecOperator.le_size (f := blastMul.blast)

@[grind =]
theorem blastMul_decl_eq (aig : AIG α) (input : aig.BinaryRefVec w) (idx : Nat)
    (h1 : idx < aig.decls.size) (h2 : idx < (blastMul aig input).aig.decls.size) :
    (blastMul aig input).aig.decls[idx] = aig.decls[idx] := by
  intros
  unfold blastMul
  split <;> rw [AIG.LawfulVecOperator.decl_eq (f := blastMul.blast)]

instance inst : AIG.LawfulVecOperator α AIG.BinaryRefVec blastMul where
  le_size := blastMul_le_size
  decl_eq := blastMul_decl_eq

end bitblast
end BVExpr

end Std.Tactic.BVDecide
