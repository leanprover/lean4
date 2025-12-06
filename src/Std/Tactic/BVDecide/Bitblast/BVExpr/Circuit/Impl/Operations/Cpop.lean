/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luisa Cicolini, Siddharth Bhat, Henrik Böving
-/
module

prelude
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Const
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Sub
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Eq
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Extract
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.ZeroExtend
public import Std.Sat.AIG.If

@[expose] public section

/-!
This module contains the implementation of a bitblaster for `BitVec.cpop`.
-/

namespace Std.Tactic.BVDecide

open Std.Sat

variable [Hashable α] [DecidableEq α]

namespace BVExpr
namespace bitblast

/-- We extract a single bit in position `start` and extend it to haev width `w`-/
def blastExtractAndExtend (aig : AIG α) (x : AIG.RefVec aig w) (start : Nat) : AIG.RefVecEntry α w :=
  -- extract 1 bit starting from start
  let targetExtract : ExtractTarget aig 1 := {vec := x, start := start}
  let res := blastExtract aig targetExtract
  let aig := res.aig
  let extract := res.vec
  -- zero-extend the extracted portion to have
  let targetExtend : AIG.ExtendTarget aig w := {vec := extract, w := 1}
  let res := blastZeroExtend aig targetExtend
  let aig := res.aig
  let extend := res.vec
  ⟨aig, extend⟩

theorem extractAndExtend_le_size (aig : AIG α) (x : AIG.RefVec aig w) (start : Nat) :
    aig.decls.size ≤ (blastExtractAndExtend aig x start).aig.decls.size := by
  unfold blastExtractAndExtend
  dsimp only
  apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := blastZeroExtend)
  apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := blastExtract)
  omega

theorem extractAndExtend_decl_eq (aig : AIG α) (x : AIG.RefVec aig w) (start : Nat):
    ∀ (idx : Nat) (h1) (h2),
        (blastExtractAndExtend aig x start).aig.decls[idx]'h2 = aig.decls[idx]'h1 := by
  generalize hres : blastExtractAndExtend aig x start = res
  unfold blastExtractAndExtend at hres
  dsimp only at hres
  rw [← hres]
  intros
  rw [AIG.LawfulVecOperator.decl_eq (f := blastZeroExtend)]
  rw [AIG.LawfulVecOperator.decl_eq (f := blastExtract)]
  (expose_names; exact h1)

/-- We extract one bit at a time from the initial vector and zero-extend them to width `w`,
  appending the result to `acc` which eventually will have size `w * w`-/
def blastExtractAndExtendPopulate (aig : AIG α) (idx : Nat) (x : AIG.RefVec aig w)
    (acc : AIG.RefVec aig (w * idx)) (hlt : idx ≤ w)
  : AIG.RefVecEntry α (w * w) :=
  if hidx : idx < w then
    let res := blastExtractAndExtend aig x idx
    let aigRes := res.aig
    let bv := res.vec
    have := extractAndExtend_le_size aig x idx
    let acc := acc.cast (aig2 := aigRes) this
    let x := x.cast (aig2 := aigRes) this
    let acc := acc.append bv
    have hcast : w * (idx + 1) = w * idx + w := by simp [Nat.mul_add]
    have acc := hcast▸acc
    blastExtractAndExtendPopulate (aigRes) (idx + 1) (x := x) (acc := acc) (by omega)
  else
    have : idx = w := by omega
    have hcast : w * idx = w * w := by rw [this]
    ⟨aig, hcast▸acc⟩

theorem extractAndExtendPopulate_le_size (aig : AIG α) (idx : Nat) (x : AIG.RefVec aig w) (acc : AIG.RefVec aig (w * idx)) (hlt : idx ≤ w):
    aig.decls.size ≤ (blastExtractAndExtendPopulate aig idx x acc hlt).aig.decls.size := by
  unfold blastExtractAndExtendPopulate
  dsimp only
  split
  · apply Nat.le_trans ?_ (by apply extractAndExtendPopulate_le_size)
    apply extractAndExtend_le_size
  · simp

theorem extractAndExtendPopulate_decl_eq  (aig : AIG α) (idx' : Nat) (x : AIG.RefVec aig w) (acc : AIG.RefVec aig (w * idx')) (hlt : idx' ≤ w):
    ∀ (idx : Nat) (h1) (h2),
        (blastExtractAndExtendPopulate aig idx' x acc hlt).aig.decls[idx]'h2 = aig.decls[idx]'h1 := by
  generalize hres : blastExtractAndExtendPopulate aig idx' x acc hlt = res
  unfold blastExtractAndExtendPopulate at hres
  dsimp only at hres
  split at hres
  · rw [← hres]
    intros
    rw [extractAndExtendPopulate_decl_eq, extractAndExtend_decl_eq]
    apply AIG.LawfulVecOperator.lt_size_of_lt_aig_size (f := blastZeroExtend)
    apply AIG.LawfulVecOperator.lt_size_of_lt_aig_size (f := blastExtract)
    omega
  · simp [← hres]

/-- Given a vector of references belonging to the same AIG `oldParSum`, we create a node to add the
  `curr`-th couple of elements and push the add node to `newParSum` -/
def blastAddVec (aig : AIG α)
  (iter_num : Nat)
  (old_layer : AIG.RefVec aig (old_length * w))
  (new_layer : AIG.RefVec aig (iter_num * w))
  (hold : 2 * (iter_num - 1) < old_length) :
   AIG.RefVecEntry α (((old_length + 1) / 2) * w) :=
  if  hlen : 0 < old_length - (iter_num * 2) then
    -- rhs
    let op2 := if h : 2 * iter_num + 1 < old_length then
                let targetExtract : ExtractTarget aig w := {vec := old_layer, start := (2 * iter_num + 1) * w}
                let res := blastExtract aig targetExtract
                let aig := res.aig
                have := AIG.LawfulVecOperator.le_size (f := blastExtract) (input := targetExtract)
                let old_layer := old_layer.cast this
                let new_layer := new_layer.cast this
                res.vec
              else blastConst aig (w := w) 0
    -- lhs
    let targetExtract : ExtractTarget aig w := {vec := old_layer, start := 2 * iter_num * w}
    let res := blastExtract aig targetExtract
    let aig := res.aig
    let op1 := res.vec
    have := AIG.LawfulVecOperator.le_size (f := blastExtract) ..
    let old_layer := old_layer.cast (aig2 := aig) this
    let new_layer := new_layer.cast (aig2 := aig) this
    let op2 := op2.cast (aig2 := aig) this
    -- add
    let res := blastAdd aig ⟨op1, op2⟩
    let aig := res.aig
    let add := res.vec
    have := AIG.LawfulVecOperator.le_size (f := blastAdd) ..
    let old_layer := old_layer.cast this
    let new_layer := new_layer.cast this
    let op1 := op1.cast this
    let op2 := op2.cast this
    have hcast : w + iter_num * w = (iter_num + 1) * w:= by simp [Nat.add_mul]; omega
    let new_layer' := hcast▸(add.append new_layer)
    blastAddVec aig (iter_num + 1) old_layer (hcast▸new_layer') (by omega)
  else
    have : old_length - iter_num * 2 = 0 := by omega
    have hcast: iter_num = ((old_length) + 1) / 2 := by omega
    ⟨aig, hcast▸new_layer⟩

theorem addVec_le_size (aig : AIG α) (old_length iter_num: Nat)
      (old_layer : AIG.RefVec aig (old_length * w)) (new_layer : AIG.RefVec aig (iter_num * w))
      (hold : 2 * (iter_num - 1) < old_length) :
    aig.decls.size ≤ (blastAddVec aig iter_num old_layer new_layer hold).aig.decls.size := by
  unfold blastAddVec
  dsimp only
  split
  · simp
    <;> (refine Nat.le_trans ?_ (by apply addVec_le_size); apply AIG.LawfulVecOperator.le_size)
  · simp

theorem addVec_decl_eq (aig : AIG α) (old_length iter_num: Nat)
      (old_layer : AIG.RefVec aig (old_length * w)) (new_layer : AIG.RefVec aig (iter_num * w))
      (hold : 2 * (iter_num - 1) < old_length) :
    ∀ (idx : Nat) (h1) (h2),
        (blastAddVec aig iter_num old_layer new_layer hold).aig.decls[idx]'h1 = aig.decls[idx]'h2 := by
  generalize hres : blastAddVec aig iter_num old_layer new_layer hold = res
  unfold blastAddVec at hres
  dsimp only at hres
  split at hres
  · simp at hres
    · rw [← hres]
      intros
      rw [addVec_decl_eq]
      · apply AIG.LawfulVecOperator.decl_eq (f := blastAdd)
      · apply AIG.LawfulVecOperator.lt_size_of_lt_aig_size (f := blastAdd)
        assumption
  · simp [← hres]

/-- We first extend all the single bits in the input BitVec w to have width `w`, then compute
the parallel prefix sum given these bits.-/
def blastCpop (aig : AIG α) (x : AIG.RefVec aig w) : AIG.RefVecEntry α w :=
  if hw : 1 < w then
    -- init
    let initAcc := blastConst (aig := aig) (w := 0) (val := 0)
    let res := blastExtractAndExtendPopulate aig 0 x initAcc (by omega)
    let aig := res.aig
    let extendedBits := res.vec
    have := extractAndExtendPopulate_le_size
    let x := x.cast (aig2 := res.aig) (by apply this)
    go aig w extendedBits (by omega)
  else
    if hw' : 0 < w then
      ⟨aig, x⟩
    else
      let zero := blastConst aig (w := w) 0
      ⟨aig, zero⟩
where
  go (aig : AIG α) (l_length : Nat) (l : AIG.RefVec aig (l_length * w)) (h : 0 < l_length) : AIG.RefVecEntry α w :=
  if hlt : 1 < l_length  then
    have hcastZero : 0 = 0 / 2 * w := by omega
    let initAcc := blastConst (aig := aig) (w := 0) (val := 0)
    let res := blastAddVec aig 0 l (hcastZero▸initAcc) (by omega)
    let aig := res.aig
    let new_layer := res.vec
    go (aig := aig) (l_length := (l_length + 1)/2) (l := new_layer) (by omega)
  else
    have hcast : l_length * w = w := by simp [show l_length = 1 by omega]
    ⟨aig, hcast▸l⟩

theorem blastCpop.go_le_size (aig : AIG α) (l_length : Nat) (l : AIG.RefVec aig (l_length * w))
      (hlen : 0 < l_length) :
    aig.decls.size ≤ (go aig l_length l hlen).aig.decls.size := by
  unfold go
  dsimp only
  split
  · refine Nat.le_trans ?_ (by apply go_le_size)
    apply addVec_le_size
  · simp

theorem blastCpop.go_le_size' (aig : AIG α) (input : aig.RefVec w) (h : 1 < w) :
    let initAcc := blastConst (aig := aig) (w := 0) (val := 0)
  aig.decls.size ≤
    (go (blastExtractAndExtendPopulate aig 0 input initAcc (by omega)).aig w
        (blastExtractAndExtendPopulate aig 0 input initAcc (by omega)).vec
        (by omega)).aig.decls.size:= by
  unfold go
  dsimp only
  split
  · refine Nat.le_trans ?_ (by apply go_le_size)
    refine Nat.le_trans ?_ (by apply addVec_le_size)
    apply extractAndExtendPopulate_le_size
  · omega

theorem blastCpop.go_decl_eq {w : Nat} (l_length : Nat) (aig : AIG α) (l : AIG.RefVec aig (l_length * w))
      (hlen : 0 < l_length)  : ∀ (idx : Nat) h1 h2,
    (go aig l_length l hlen).aig.decls[idx]'h1 =
    aig.decls[idx]'h2 := by
  generalize hgo : go aig l_length l hlen = res
  unfold go at hgo
  dsimp only at hgo
  split at hgo
  · rw [← hgo]
    intros idx hidx hidx'
    rw [go_decl_eq]
    · apply addVec_decl_eq
    · let initAcc := blastConst (aig := aig) (w := 0) (val := 0)
      have hcast : 0 = 0/2*w := by omega
      have := addVec_le_size aig l_length 0 l (hcast▸initAcc) (by omega)
      exact Nat.lt_of_lt_of_le hidx' this
  · simp [← hgo]

instance : AIG.LawfulVecOperator α AIG.RefVec blastCpop where
  le_size := by
    intros
    unfold blastCpop
    split
    · apply blastCpop.go_le_size'
      omega
    · split <;> simp
  decl_eq := by
    intros
    unfold blastCpop
    dsimp only
    expose_names
    split
    · let initAcc := blastConst (aig := aig) (w := 0) (val := 0)
      have := extractAndExtendPopulate_le_size (idx := 0) aig input initAcc (by omega)
      rw [blastCpop.go_decl_eq]
      apply extractAndExtendPopulate_decl_eq (idx' := 0) aig input
      exact Nat.lt_of_lt_of_le h1 this
    · split <;> simp

end bitblast
end BVExpr

end Std.Tactic.BVDecide
