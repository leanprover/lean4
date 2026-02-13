/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luisa Cicolini
-/
module

prelude
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Const
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Sub
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Extract
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Append
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.ZeroExtend
public import Std.Sat.AIG.If

import Init.Omega

@[expose] public section

/-!
This module contains the implementation of a bitblaster for `BitVec.hAdd`.
-/

namespace Std.Tactic.BVDecide

open Std.Sat

variable [Hashable α] [DecidableEq α]

namespace BVExpr
namespace bitblast

/-- We extract a single bit in position `start` and extend it to haev width `w`-/
def blastExtractAndExtendBit (aig : AIG α) (x : AIG.RefVec aig w) (start : Nat) : AIG.RefVecEntry α w :=
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

theorem extractAndExtendBit_le_size (aig : AIG α) (x : AIG.RefVec aig w) (start : Nat) :
    aig.decls.size ≤ (blastExtractAndExtendBit aig x start).aig.decls.size := by
  unfold blastExtractAndExtendBit
  dsimp only
  apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := blastZeroExtend)
  apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := blastExtract)
  omega

theorem extractAndExtendBit_decl_eq (aig : AIG α) (x : AIG.RefVec aig w) (start : Nat):
    ∀ (idx : Nat) (h1) (h2),
      (blastExtractAndExtendBit aig x start).aig.decls[idx]'h2 = aig.decls[idx]'h1 := by
  generalize hres : blastExtractAndExtendBit aig x start = res
  unfold blastExtractAndExtendBit at hres
  dsimp only at hres
  rw [← hres]
  intros _ h1 _
  rw [AIG.LawfulVecOperator.decl_eq (f := blastZeroExtend),
    AIG.LawfulVecOperator.decl_eq (f := blastExtract)]
  exact h1

/-- We extract one bit at a time from the initial vector and zero-extend them to width `w`,
  appending the result to `acc` which eventually will have size `w * w`-/
def blastextractAndExtend (aig : AIG α) (idx : Nat) (x : AIG.RefVec aig w)
    (acc : AIG.RefVec aig (w * idx)) (hlt : idx ≤ w) : AIG.RefVecEntry α (w * w) :=
  if hidx : idx < w then
    let res := blastExtractAndExtendBit aig x idx
    let aigRes := res.aig
    let bv := res.vec
    have := extractAndExtendBit_le_size aig x idx
    let acc := acc.cast (aig2 := aigRes) this
    let x := x.cast (aig2 := aigRes) this
    let acc := acc.append bv
    have hcast : w * (idx + 1) = w * idx + w := by simp [Nat.mul_add]
    have acc := hcast▸acc
    blastextractAndExtend (aigRes) (idx + 1) (x := x) (acc := acc) (by omega)
  else
    have : idx = w := by omega
    have hcast : w * idx = w * w := by rw [this]
    ⟨aig, hcast▸acc⟩

theorem extractAndExtend_le_size (aig : AIG α) (idx : Nat) (x : AIG.RefVec aig w)
    (acc : AIG.RefVec aig (w * idx)) (hlt : idx ≤ w) :
    aig.decls.size ≤ (blastextractAndExtend aig idx x acc hlt).aig.decls.size := by
  unfold blastextractAndExtend
  dsimp only
  split
  · apply Nat.le_trans ?_ (by apply extractAndExtend_le_size)
    apply extractAndExtendBit_le_size
  · simp

theorem extractAndExtend_decl_eq (aig : AIG α) (idx' : Nat) (x : AIG.RefVec aig w)
    (acc : AIG.RefVec aig (w * idx')) (hlt : idx' ≤ w) :
    ∀ (idx : Nat) (h1) (h2),
      (blastextractAndExtend aig idx' x acc hlt).aig.decls[idx]'h2 = aig.decls[idx]'h1 := by
  generalize hres : blastextractAndExtend aig idx' x acc hlt = res
  unfold blastextractAndExtend at hres
  dsimp only at hres
  split at hres
  · rw [← hres]
    intros
    rw [extractAndExtend_decl_eq, extractAndExtendBit_decl_eq]
    apply AIG.LawfulVecOperator.lt_size_of_lt_aig_size (f := blastZeroExtend)
    apply AIG.LawfulVecOperator.lt_size_of_lt_aig_size (f := blastExtract)
    omega
  · simp [← hres]

/-- Given a vector of references belonging to the same AIG `oldParSum`,
  we create a node to add the `curr`-th couple of elements and push the add node to `newParSum` -/
def blastCpopLayer (aig : AIG α) (iter_num : Nat)
  (old_layer : AIG.RefVec aig (old_length * w)) (new_layer : AIG.RefVec aig (iter_num * w))
  (hold : 2 * (iter_num - 1) < old_length) : AIG.RefVecEntry α ((old_length + 1)/2 * w) :=
  if  hlen : 0 < old_length - (iter_num * 2) then
    -- lhs
    let targetExtract : ExtractTarget aig w := {vec := old_layer, start := 2 * iter_num * w}
    let res := blastExtract aig targetExtract
    let aig := res.aig
    let op1 : aig.RefVec w := res.vec
    have := AIG.LawfulVecOperator.le_size (f := blastExtract) ..
    let old_layer := old_layer.cast (aig2 := aig) this
    let new_layer := new_layer.cast (aig2 := aig) this
    -- rhs
    let targetExtract : ExtractTarget aig w := {vec := old_layer, start := (2 * iter_num + 1) * w}
    let res := blastExtract aig targetExtract
    let aig := res.aig
    let op2 : aig.RefVec w := res.vec
    have := AIG.LawfulVecOperator.le_size (f := blastExtract) (input := targetExtract)
    let old_layer := old_layer.cast this
    let new_layer := new_layer.cast this
    let op1 := op1.cast (aig2 := aig) this
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
    let targetAppend : AppendTarget aig ((iter_num + 1) * w ) :=
        {lhs := add, rhs := new_layer, h := by omega}
    let res := blastAppend (aig := aig) (target:= targetAppend)
    let aig := res.aig
    let new_layer' := res.vec
    have := AIG.LawfulVecOperator.le_size (f := blastAppend) ..
    let old_layer := old_layer.cast this
    blastCpopLayer aig (iter_num + 1) old_layer new_layer' (by omega)
  else
    have h : iter_num = (old_length + 1) / 2 := by omega
    ⟨aig, h ▸ new_layer⟩
termination_by old_length - iter_num * 2

theorem blastCpopLayer_le_size (aig : AIG α) (iter_num: Nat) (old_layer : AIG.RefVec aig (old_length * w))
    (new_layer : AIG.RefVec aig (iter_num * w)) (hold : 2 * (iter_num - 1) < old_length) :
    aig.decls.size ≤ (blastCpopLayer aig iter_num old_layer new_layer hold).aig.decls.size := by
  unfold blastCpopLayer
  dsimp only
  split
  · simp
    <;> (refine Nat.le_trans ?_ (by apply blastCpopLayer_le_size); apply AIG.LawfulVecOperator.le_size)
  · simp

theorem blastCpopLayer_decl_eq (aig : AIG α) (iter_num: Nat) (old_layer : AIG.RefVec aig (old_length * w))
    (new_layer : AIG.RefVec aig (iter_num * w)) (hold : 2 * (iter_num - 1) < old_length) :
    ∀ (idx : Nat) h1 h2,
      (blastCpopLayer aig iter_num old_layer new_layer hold).aig.decls[idx]'h1 = aig.decls[idx]'h2 := by
  generalize hres : blastCpopLayer aig iter_num old_layer new_layer hold= res
  unfold blastCpopLayer at hres
  dsimp only at hres
  split at hres
  · simp at hres
    · rw [← hres]
      intros
      rw [blastCpopLayer_decl_eq]
      · apply AIG.LawfulVecOperator.decl_eq (f := blastAdd)
      · apply AIG.LawfulVecOperator.lt_size_of_lt_aig_size (f := blastAdd)
        assumption
  · simp [← hres]

def blastCpopTree (aig : AIG α) (l : AIG.RefVec aig (l_length * w)) (h : 0 < l_length) :
    AIG.RefVecEntry α w :=
  if hlt : 1 < l_length  then
    have hcastZero : 0 = 0 / 2 * w := by omega
    let initAcc := blastConst (aig := aig) (w := 0) (val := 0)
    let res := blastCpopLayer aig 0 l (hcastZero▸initAcc) (by omega)
    let aig := res.aig
    let new_layer := res.vec
    blastCpopTree (aig := aig) (l := new_layer) (by omega)
  else
    have hcast : l_length * w = w := by simp [show l_length = 1 by omega]
    ⟨aig, hcast▸l⟩
termination_by l_length

theorem blastCpopTree_le_size (aig : AIG α) (old_layer : AIG.RefVec aig (old_length * w))
    (h : 0 < old_length) :
    aig.decls.size ≤ (blastCpopTree aig old_layer h).aig.decls.size := by
  unfold blastCpopTree
  dsimp only
  split
  · simp only [BitVec.ofNat_eq_ofNat, Nat.reduceDiv]
    apply Nat.le_trans _ (by apply blastCpopTree_le_size)
    apply blastCpopLayer_le_size
  · simp

theorem blastCpopTree_decl_eq (aig : AIG α) (old_layer : AIG.RefVec aig (old_length * w))
    (h : 0 < old_length) :
    ∀ (idx : Nat) h1 h2,
      (blastCpopTree aig old_layer h).aig.decls[idx]'h1 = aig.decls[idx]'h2 := by
  generalize hres : blastCpopTree aig old_layer h = res
  unfold blastCpopTree at hres
  dsimp only at hres
  split at hres
  · simp at hres
    · rw [← hres]
      intros i h1 h2
      rw [blastCpopTree_decl_eq]
      · apply blastCpopLayer_decl_eq
      · apply Nat.lt_of_lt_of_le h2
        apply blastCpopLayer_le_size
  · simp [← hres]

/-- We first extend all the single bits in the input BitVec w to have width `w`, then compute
the parallel prefix sum given these bits.-/
def blastCpop (aig : AIG α) (x : AIG.RefVec aig w) : AIG.RefVecEntry α w :=
  if hw : 1 < w then
    -- init
    let initAcc := blastConst (aig := aig) (w := 0) (val := 0)
    let res := blastextractAndExtend aig 0 x initAcc (by omega)
    let aig := res.aig
    let extendedBits := res.vec
    have := extractAndExtend_le_size
    let x := x.cast (aig2 := res.aig) (by apply this)
    blastCpopTree aig extendedBits (by omega)
  else
    if hw' : 0 < w then
      ⟨aig, x⟩
    else
      let zero := blastConst aig (w := w) 0
      ⟨aig, zero⟩

theorem blastCpop_le_size (aig : AIG α) (input : AIG.RefVec aig w) :
    aig.decls.size ≤ (blastCpop aig input).aig.decls.size := by
  unfold blastCpop
  split
  · let initAcc := blastConst (aig := aig) (w := 0) (val := 0)
    let res := blastextractAndExtend aig 0 input initAcc (by omega)
    have hext := extractAndExtend_le_size aig 0 input initAcc (by omega)
    have htree := blastCpopTree_le_size (aig := res.aig) (old_layer := res.vec) (by omega)
    apply Nat.le_trans hext htree
  · split
    · simp
    · simp

theorem blastCpop_decl_eq (aig : AIG α) (input : AIG.RefVec aig w) :
    ∀ (idx : Nat) h1 h2, (blastCpop aig input).aig.decls[idx]'h1 = aig.decls[idx]'h2 := by
  unfold blastCpop
  split
  · simp only [BitVec.ofNat_eq_ofNat, Lean.Elab.WF.paramLet]
    intros idx hidx hidx'
    let initAcc := blastConst (aig := aig) (w := 0) (val := 0)
    let res := blastextractAndExtend aig 0 input initAcc (by omega)
    have hext := extractAndExtend_decl_eq aig 0 input initAcc (by omega) (idx := idx)
    have htree := blastCpopTree_decl_eq (aig := res.aig) (old_layer := res.vec) (by omega) (idx := idx)
    simp only [BitVec.ofNat_eq_ofNat, res, initAcc] at htree hext
    rw [htree (by omega) (by apply Nat.lt_of_lt_of_le hidx' (by apply extractAndExtend_le_size)),
      hext (by omega) (by apply Nat.lt_of_lt_of_le hidx' (by apply extractAndExtend_le_size))]
  · split
    · simp
    · simp

instance : AIG.LawfulVecOperator α AIG.RefVec blastCpop where
  le_size := by
    intros
    unfold blastCpop
    apply blastCpop_le_size
  decl_eq := by
    intros
    unfold blastCpop
    apply blastCpop_decl_eq

end bitblast
end BVExpr

end Std.Tactic.BVDecide
