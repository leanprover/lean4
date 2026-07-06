/-
Copyright (c) 2026 University of Cambridge. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luisa Cicolini, Siddharth Bhat, Henrik Böving
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
This module contains the implementation of a bitblaster for `BitVec.cpop`.
-/

namespace Std.Tactic.BVDecide

open Std.Sat

variable [Hashable α] [DecidableEq α]

namespace BVExpr
namespace bitblast

structure ExtractAndExtendBitTarget (aig : AIG α) (w : Nat) where
  start : Nat
  x : AIG.RefVec aig w

/-- Extract a single bit in position `start` in `target` and extend it to have width `w`-/
def blastExtractAndExtendBit (aig : AIG α) (target : ExtractAndExtendBitTarget aig w) :
    AIG.RefVecEntry α w :=
  -- extract 1 bit starting from start
  let ⟨start, x⟩ := target
  let res := blastExtract aig ⟨x, start⟩
  let aig := res.aig
  let extract := res.vec
  -- zero-extend the extracted portion to have
  let res := blastZeroExtend aig (newWidth := w) ⟨1, extract⟩
  let aig := res.aig
  let extend := res.vec
  ⟨aig, extend⟩

instance : AIG.LawfulVecOperator α ExtractAndExtendBitTarget blastExtractAndExtendBit where
  le_size := by
    intros
    unfold blastExtractAndExtendBit
    dsimp only
    apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := blastZeroExtend)
    apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := blastExtract)
    omega
  decl_eq := by
    intros
    unfold blastExtractAndExtendBit
    dsimp only
    rw [AIG.LawfulVecOperator.decl_eq (f := blastZeroExtend),
      AIG.LawfulVecOperator.decl_eq (f := blastExtract)]
    apply AIG.LawfulVecOperator.lt_size_of_lt_aig_size
    omega

structure blastExtractAndExtendTarget (aig : AIG α) (outWidth : Nat) where
  {w : Nat}
  x : AIG.RefVec aig w
  h : outWidth = w * w

/-- Extract one bit at a time from the initial vector, zero-extend it to width `w`,
  and append it the result to `acc`, which eventually will have size `outWidth = w * w`-/
def blastExtractAndExtend (aig : AIG α) (target : blastExtractAndExtendTarget aig outWidth) :
    AIG.RefVecEntry α outWidth :=
  let ⟨x, h⟩ := target
  let initAcc := blastConst (aig := aig) (w := 0) (val := 0)
  go 0 x initAcc (by omega) h
where
  go {aig : AIG α} {w : Nat} (idx : Nat) (x : AIG.RefVec aig w) (acc : AIG.RefVec aig (w * idx))
      (h : idx ≤ w) (h' : outWidth = w * w) :=
    if hidx : idx < w then
      let res := blastExtractAndExtendBit aig ⟨idx, x⟩
      have := AIG.LawfulVecOperator.le_size (f := blastExtractAndExtendBit) ..
      let aig := res.aig
      let bv := res.vec
      let acc := acc.cast this
      let x := x.cast this
      let acc := acc.append bv
      have hcast : w * (idx + 1) = w * idx + w := by simp [Nat.mul_add]
      have acc := hcast ▸ acc
      go (idx + 1) (x := x) (acc := acc) (by omega) h'
    else
      have hcast : w * idx = outWidth := by
        simp only [show idx = w by omega, h']
      ⟨aig, hcast ▸ acc⟩
termination_by w - idx

theorem blastExtractAndExtend.go_le_size (aig : AIG α) (idx : Nat) (x : AIG.RefVec aig w)
    (acc : AIG.RefVec aig (w * idx)) (h : idx ≤ w) (h' : outWidth = w * w) :
    aig.decls.size ≤ (go idx x acc h h').aig.decls.size := by
  unfold go
  dsimp only
  split
  · apply Nat.le_trans ?_ (by apply blastExtractAndExtend.go_le_size)
    apply AIG.LawfulVecOperator.le_size (f := blastExtractAndExtendBit)
  · simp
termination_by w - idx

theorem blastExtractAndExtend.go_decl_eq (aig : AIG α) (idx' : Nat) (x : AIG.RefVec aig w)
    (acc : AIG.RefVec aig (w * idx')) (h : idx' ≤ w) (h' : outWidth = w * w) :
    ∀ (idx : Nat) (h1) (h2),
      (go idx' x acc h h').aig.decls[idx]'h2 = aig.decls[idx]'h1 := by
  generalize hres : go idx' x acc h h' = res
  unfold go at hres
  dsimp only at hres
  split at hres
  · rw [← hres]
    intros
    rw [blastExtractAndExtend.go_decl_eq, AIG.LawfulVecOperator.decl_eq (f := blastExtractAndExtendBit)]
    apply AIG.LawfulVecOperator.lt_size_of_lt_aig_size (f := blastZeroExtend)
    apply AIG.LawfulVecOperator.lt_size_of_lt_aig_size (f := blastExtract)
    omega
  · simp [← hres]
termination_by w - idx'

instance : AIG.LawfulVecOperator α blastExtractAndExtendTarget blastExtractAndExtend where
  le_size := by
    intros
    unfold blastExtractAndExtend
    dsimp only
    apply blastExtractAndExtend.go_le_size
  decl_eq := by
    intros
    unfold blastExtractAndExtend
    apply blastExtractAndExtend.go_decl_eq

structure blastCpopLayerTarget (aig : AIG α) (outWidth : Nat) where
  {w len : Nat}
  oldLayer : AIG.RefVec aig (len * w)
  h : outWidth = (len + 1) / 2 * w
  hlen : 0 < len

/-- Given a vector of references `oldLayer`, add the `iterNum`-th couple of elements and
  append the result of the addition to `newLayer` -/
def blastCpopLayer (aig : AIG α) (target : blastCpopLayerTarget aig outWidth) :
    AIG.RefVecEntry α outWidth :=
  let ⟨oldLayer, h, hlen⟩ := target
  let initAcc := blastConst aig (w := 0 * _) (val := 0)
  go 0 oldLayer initAcc
    (by simp only [Nat.zero_le, Nat.sub_eq_zero_of_le, Nat.mul_zero, hlen]) h
where
  go {aig : AIG α} {w len : Nat} (iterNum : Nat)
    (oldLayer : AIG.RefVec aig (len * w)) (newLayer : AIG.RefVec aig (iterNum * w))
    (hold : 2 * (iterNum - 1) < len) (hout : outWidth = (len + 1) / 2 * w) :=
  if  hlen : 0 < len - (iterNum * 2) then
    -- lhs
    let res := blastExtract aig ⟨oldLayer, 2 * iterNum * w⟩
    let aig := res.aig
    let op1 : aig.RefVec w := res.vec
    have := AIG.LawfulVecOperator.le_size (f := blastExtract) ..
    let oldLayer := oldLayer.cast this
    let newLayer := newLayer.cast this
    -- rhs
    let res := blastExtract aig ⟨oldLayer, (2 * iterNum + 1) * w⟩
    let aig := res.aig
    let op2 : aig.RefVec w := res.vec
    have := AIG.LawfulVecOperator.le_size (f := blastExtract) ..
    let oldLayer := oldLayer.cast this
    let newLayer := newLayer.cast this
    let op1 := op1.cast this
    -- add
    let res := blastAdd aig ⟨op1, op2⟩
    let aig := res.aig
    let add := res.vec
    have := AIG.LawfulVecOperator.le_size (f := blastAdd) ..
    let oldLayer := oldLayer.cast this
    let newLayer := newLayer.cast this
    let res := blastAppend (aig := aig) ⟨add, newLayer, by simp [Nat.add_mul]⟩
    let aig := res.aig
    let newLayer := res.vec
    have := AIG.LawfulVecOperator.le_size (f := blastAppend) ..
    let oldLayer := oldLayer.cast this
    go (iterNum + 1) oldLayer newLayer (by omega) hout
  else
    have hcast : iterNum * w = outWidth := by
      simp [show iterNum = (len + 1)/ 2 by omega, hout]
    ⟨aig, hcast ▸ newLayer⟩
termination_by len - iterNum * 2

theorem blastCpopLayer.go_le_size (aig : AIG α) (iterNum: Nat) (oldLayer : AIG.RefVec aig (len * w))
    (newLayer : AIG.RefVec aig (iterNum * w)) (hold : 2 * (iterNum - 1) < len) (hout : outWidth = (len + 1) / 2 * w) :
    aig.decls.size ≤ (go iterNum oldLayer newLayer hold hout).aig.decls.size := by
  unfold go
  dsimp only
  split
  · simp only [AIG.RefVec.cast_cast]
    <;> (refine Nat.le_trans ?_ (by apply blastCpopLayer.go_le_size); apply AIG.LawfulVecOperator.le_size)
  · simp
termination_by len - iterNum * 2

theorem blastCpopLayer.go_decl_eq (aig : AIG α) (iterNum: Nat) (oldLayer : AIG.RefVec aig (len * w))
    (newLayer : AIG.RefVec aig (iterNum * w)) (hold : 2 * (iterNum - 1) < len) (hout : outWidth = (len + 1) / 2 * w) :
    ∀ (idx : Nat) h1 h2,
      (go iterNum oldLayer newLayer hold hout).aig.decls[idx]'h1 = aig.decls[idx]'h2 := by
  generalize hres : go iterNum oldLayer newLayer hold hout = res
  unfold go at hres
  dsimp only at hres
  split at hres
  · simp at hres
    · rw [← hres]
      intros
      rw [blastCpopLayer.go_decl_eq]
      · apply AIG.LawfulVecOperator.decl_eq (f := blastAdd)
      · apply AIG.LawfulVecOperator.lt_size_of_lt_aig_size (f := blastAdd)
        assumption
  · simp [← hres]
termination_by len - iterNum * 2

instance : AIG.LawfulVecOperator α blastCpopLayerTarget blastCpopLayer where
  le_size := by
    intros
    unfold blastCpopLayer
    dsimp only
    apply blastCpopLayer.go_le_size
  decl_eq := by
    intros
    unfold blastCpopLayer
    dsimp only
    apply blastCpopLayer.go_decl_eq

structure blastCpopTreeTarget (aig : AIG α) (w : Nat) where
  {len : Nat}
  x : AIG.RefVec aig (len * w)
  h : 0 < len

/--
  Construct a parallel-prefix-sum circuit, invoking `blastCpopLayer` for
  each layer, until a single addition node is left.
-/
def blastCpopTree (aig : AIG α) (target : blastCpopTreeTarget aig w) :
    AIG.RefVecEntry α w :=
  let ⟨x, h⟩ := target
  go x h
where
  go {aig : AIG α} {len : Nat} (x : AIG.RefVec aig (len * w)) (h : 0 < len) :=
    if hlt : 1 < len  then
      let res := blastCpopLayer aig ⟨x, by simp, h⟩ (outWidth := (len + 1) / 2 * w)
      go res.vec (by omega)
    else
      have hcast : len * w = w := by simp [show len = 1 by omega]
      ⟨aig, hcast ▸ x⟩
  termination_by len

theorem blastCpopTree.go_le_size (aig : AIG α) (oldLayer : AIG.RefVec aig (len * w))
    (h : 0 < len) :
    aig.decls.size ≤ (go oldLayer h).aig.decls.size := by
  unfold go
  dsimp only
  split
  · apply Nat.le_trans _ (by apply blastCpopTree.go_le_size)
    apply blastCpopLayer.go_le_size
  · simp
termination_by len

theorem blastCpopTree.go_decl_eq (aig : AIG α) (oldLayer : AIG.RefVec aig (len * w))
      (h : 0 < len) :
    ∀ (idx : Nat) h1 h2,
      (go oldLayer h).aig.decls[idx]'h1 = aig.decls[idx]'h2 := by
  generalize hres : go oldLayer h = res
  unfold go at hres
  dsimp only at hres
  split at hres
  · rw [← hres]
    intros i h1 h2
    rw [blastCpopTree.go_decl_eq]
    · apply blastCpopLayer.go_decl_eq
    · apply Nat.lt_of_lt_of_le h2
      apply blastCpopLayer.go_le_size
  · simp [← hres]
termination_by len

instance : AIG.LawfulVecOperator α blastCpopTreeTarget blastCpopTree where
  le_size := by
    intros
    unfold blastCpopTree
    apply blastCpopTree.go_le_size
  decl_eq := by
    intros
    unfold blastCpopTree
    apply blastCpopTree.go_decl_eq

/-- Extend all the  bits in the input BitVec w `x` to have width `w`,
  then construct the parallel-prefix-sum circuit. -/
def blastCpop (aig : AIG α) (x : AIG.RefVec aig w) : AIG.RefVecEntry α w :=
  if hw : 1 < w then
    let res := blastExtractAndExtend aig (outWidth := w * w) ⟨x, by rfl⟩
    let aig := res.aig
    let extendedBits := res.vec
    blastCpopTree aig ⟨extendedBits, by omega⟩
  else if hw' : 0 < w then
    ⟨aig, x⟩
  else
    let zero := blastConst aig (w := w) 0
    ⟨aig, zero⟩

theorem blastCpop_le_size (aig : AIG α) (input : AIG.RefVec aig w) :
    aig.decls.size ≤ (blastCpop aig input).aig.decls.size := by
  unfold blastCpop
  split
  · let initAcc := blastConst (aig := aig) (w := 0) (val := 0)
    dsimp only
    let res := blastExtractAndExtend aig (outWidth := w * w) ⟨input, by omega⟩
    have hext := blastExtractAndExtend.go_le_size aig 0 (outWidth := w * w)
      (x := input) (by omega) (acc := initAcc)
    have := blastCpopTree.go_le_size (aig := res.aig) (oldLayer := res.vec) (by omega)
    exact Nat.le_trans (hext rfl) this
  · split
    · simp
    · simp

theorem blastCpop_decl_eq (aig : AIG α) (input : AIG.RefVec aig w) :
    ∀ (idx : Nat) h1 h2, (blastCpop aig input).aig.decls[idx]'h1 = aig.decls[idx]'h2 := by
  unfold blastCpop
  split
  · simp only [Lean.Elab.WF.paramLet]
    intros idx hidx hidx'
    unfold blastCpopTree blastExtractAndExtend
    dsimp only
    rw [blastCpopTree.go_decl_eq]
    · rw [blastExtractAndExtend.go_decl_eq]
    · apply Nat.lt_of_lt_of_le hidx' (by apply blastExtractAndExtend.go_le_size)
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
