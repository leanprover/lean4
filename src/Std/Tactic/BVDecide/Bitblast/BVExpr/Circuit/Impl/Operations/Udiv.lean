/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Std.Tactic.BVDecide.Bitblast.BVExpr.Basic
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Sub
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Eq
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Ult
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.ZeroExtend
import Std.Sat.AIG.If

/-!
This module contains the implementation of a bitblaster for `BitVec.udiv`. The implemented
circuit is a shift subtractor.
-/

namespace Std.Tactic.BVDecide

open Std.Sat

namespace BVExpr
namespace bitblast

variable [Hashable α] [DecidableEq α]

namespace blastUdiv

structure ShiftConcatInput (aig : AIG α) (len : Nat) where
  lhs : AIG.RefVec aig len
  bit : AIG.Ref aig

def blastShiftConcat (aig : AIG α) (input : ShiftConcatInput aig w) : AIG.RefVecEntry α w :=
  let ⟨lhs, bit⟩ := input
  let bit := AIG.RefVec.empty.push bit
  let new := bit.append lhs
  blastZeroExtend aig ⟨_, new⟩

instance : AIG.LawfulVecOperator α ShiftConcatInput blastShiftConcat where
  le_size := by
    intros
    unfold blastShiftConcat
    dsimp only
    apply AIG.LawfulVecOperator.le_size (f := blastZeroExtend)
  decl_eq := by
    intros
    unfold blastShiftConcat
    dsimp only
    rw [AIG.LawfulVecOperator.decl_eq (f := blastZeroExtend)]

structure BlastDivSubtractShiftOutput (old : AIG α) (w : Nat) where
  aig : AIG α
  wn : Nat
  wr : Nat
  q : AIG.RefVec aig w
  r : AIG.RefVec aig w
  hle : old.decls.size ≤ aig.decls.size

def blastDivSubtractShift (aig : AIG α) (falseRef trueRef : AIG.Ref aig) (n d : AIG.RefVec aig w) (wn wr : Nat)
    (q r : AIG.RefVec aig w) : BlastDivSubtractShiftOutput aig w :=
  let wn := wn - 1
  let wr := wr + 1
  let res := blastUdiv.blastShiftConcat aig ⟨r, n.getD wn falseRef⟩
  let aig := res.aig
  let r' := res.vec
  have := AIG.LawfulVecOperator.le_size (f := blastUdiv.blastShiftConcat) ..
  let falseRef := falseRef.cast this
  let trueRef := trueRef.cast this
  let d := d.cast this
  let q := q.cast this

  let res := blastUdiv.blastShiftConcat aig ⟨q, falseRef⟩
  let aig := res.aig
  let posQ := res.vec
  have := AIG.LawfulVecOperator.le_size (f := blastUdiv.blastShiftConcat) ..
  let trueRef := trueRef.cast this
  let d := d.cast this
  let q := q.cast this
  let r' := r'.cast this

  let res := blastUdiv.blastShiftConcat aig ⟨q, trueRef⟩
  let aig := res.aig
  let negQ := res.vec
  have := AIG.LawfulVecOperator.le_size (f := blastUdiv.blastShiftConcat) ..
  let d := d.cast this
  let r' := r'.cast this
  let posQ := posQ.cast this

  let res := blastSub aig ⟨r', d⟩
  let aig := res.aig
  let negR := res.vec
  have := AIG.LawfulVecOperator.le_size (f := blastSub) ..
  let d := d.cast this
  let r' := r'.cast this
  let posQ := posQ.cast this
  let negQ := negQ.cast this

  let posR := r'

  let res := BVPred.mkUlt aig ⟨r', d⟩
  let aig := res.aig
  let discr := res.ref
  have := AIG.LawfulOperator.le_size (f := BVPred.mkUlt) ..
  let posQ := posQ.cast this
  let negQ := negQ.cast this
  let posR := posR.cast this
  let negR := negR.cast this

  let res := AIG.RefVec.ite aig ⟨discr, posQ, negQ⟩
  let aig := res.aig
  let nextQ := res.vec
  have := AIG.LawfulVecOperator.le_size (f := AIG.RefVec.ite) ..
  let posR := posR.cast this
  let negR := negR.cast this
  let discr := discr.cast this

  let res := AIG.RefVec.ite aig ⟨discr, posR, negR⟩
  let aig := res.aig
  let nextR := res.vec
  have := AIG.LawfulVecOperator.le_size (f := AIG.RefVec.ite) ..
  let nextQ := nextQ.cast this
  have := by
    apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := AIG.RefVec.ite)
    apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := AIG.RefVec.ite)
    apply AIG.LawfulOperator.le_size_of_le_aig_size (f := BVPred.mkUlt)
    apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := blastSub)
    apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := blastShiftConcat)
    apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := blastShiftConcat)
    apply AIG.LawfulVecOperator.le_size (f := blastShiftConcat)
  ⟨aig, wn, wr, nextQ, nextR, this⟩

theorem blastDivSubtractShift_le_size (aig : AIG α) (falseRef trueRef : AIG.Ref aig)
     (n d : AIG.RefVec aig w) (wn wr : Nat) (q r : AIG.RefVec aig w) :
    aig.decls.size ≤ (blastDivSubtractShift aig falseRef trueRef n d wn wr q r).aig.decls.size := by
  unfold blastDivSubtractShift
  dsimp only
  apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := AIG.RefVec.ite)
  apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := AIG.RefVec.ite)
  apply AIG.LawfulOperator.le_size_of_le_aig_size (f := BVPred.mkUlt)
  apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := blastSub)
  apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := blastUdiv.blastShiftConcat)
  apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := blastUdiv.blastShiftConcat)
  apply AIG.LawfulVecOperator.le_size (f := blastUdiv.blastShiftConcat)

theorem blastDivSubtractShift_decl_eq (aig : AIG α) (falseRef trueRef : AIG.Ref aig)
     (n d : AIG.RefVec aig w) (wn wr : Nat) (q r : AIG.RefVec aig w) :
    ∀ (idx : Nat) (h1) (h2),
        (blastDivSubtractShift aig falseRef trueRef n d wn wr q r).aig.decls[idx]'h2 = aig.decls[idx]'h1 := by
  generalize hres : blastDivSubtractShift aig falseRef trueRef n d wn wr q r = res
  unfold blastDivSubtractShift at hres
  dsimp only at hres
  rw [← hres]
  intros
  rw [AIG.LawfulVecOperator.decl_eq (f := AIG.RefVec.ite)]
  rw [AIG.LawfulVecOperator.decl_eq (f := AIG.RefVec.ite)]
  rw [AIG.LawfulOperator.decl_eq (f := BVPred.mkUlt)]
  rw [AIG.LawfulVecOperator.decl_eq (f := blastSub)]
  rw [AIG.LawfulVecOperator.decl_eq (f := blastUdiv.blastShiftConcat)]
  rw [AIG.LawfulVecOperator.decl_eq (f := blastUdiv.blastShiftConcat)]
  rw [AIG.LawfulVecOperator.decl_eq (f := blastUdiv.blastShiftConcat)]
  · apply AIG.LawfulVecOperator.lt_size_of_lt_aig_size (f := blastUdiv.blastShiftConcat)
    assumption
  · apply AIG.LawfulVecOperator.lt_size_of_lt_aig_size (f := blastUdiv.blastShiftConcat)
    apply AIG.LawfulVecOperator.lt_size_of_lt_aig_size (f := blastUdiv.blastShiftConcat)
    assumption
  · apply AIG.LawfulVecOperator.lt_size_of_lt_aig_size (f := blastUdiv.blastShiftConcat)
    apply AIG.LawfulVecOperator.lt_size_of_lt_aig_size (f := blastUdiv.blastShiftConcat)
    apply AIG.LawfulVecOperator.lt_size_of_lt_aig_size (f := blastUdiv.blastShiftConcat)
    assumption
  · apply AIG.LawfulVecOperator.lt_size_of_lt_aig_size (f := blastSub)
    apply AIG.LawfulVecOperator.lt_size_of_lt_aig_size (f := blastUdiv.blastShiftConcat)
    apply AIG.LawfulVecOperator.lt_size_of_lt_aig_size (f := blastUdiv.blastShiftConcat)
    apply AIG.LawfulVecOperator.lt_size_of_lt_aig_size (f := blastUdiv.blastShiftConcat)
    assumption
  · apply AIG.LawfulOperator.lt_size_of_lt_aig_size (f := BVPred.mkUlt)
    apply AIG.LawfulVecOperator.lt_size_of_lt_aig_size (f := blastSub)
    apply AIG.LawfulVecOperator.lt_size_of_lt_aig_size (f := blastUdiv.blastShiftConcat)
    apply AIG.LawfulVecOperator.lt_size_of_lt_aig_size (f := blastUdiv.blastShiftConcat)
    apply AIG.LawfulVecOperator.lt_size_of_lt_aig_size (f := blastUdiv.blastShiftConcat)
    assumption
  · apply AIG.LawfulVecOperator.lt_size_of_lt_aig_size (f := AIG.RefVec.ite)
    apply AIG.LawfulOperator.lt_size_of_lt_aig_size (f := BVPred.mkUlt)
    apply AIG.LawfulVecOperator.lt_size_of_lt_aig_size (f := blastSub)
    apply AIG.LawfulVecOperator.lt_size_of_lt_aig_size (f := blastUdiv.blastShiftConcat)
    apply AIG.LawfulVecOperator.lt_size_of_lt_aig_size (f := blastUdiv.blastShiftConcat)
    apply AIG.LawfulVecOperator.lt_size_of_lt_aig_size (f := blastUdiv.blastShiftConcat)
    assumption

structure BlastUdivOutput (old : AIG α) (w : Nat) where
  aig : AIG α
  q : AIG.RefVec aig w
  r : AIG.RefVec aig w
  hle : old.decls.size ≤ aig.decls.size

def go (aig : AIG α) (curr : Nat) (falseRef trueRef : AIG.Ref aig) (n d : AIG.RefVec aig w)
    (wn wr : Nat) (q r : AIG.RefVec aig w) : BlastUdivOutput aig w :=
  match curr with
  | 0 => ⟨aig, q, r, by omega⟩
  | curr + 1 =>
    let res := blastDivSubtractShift aig falseRef trueRef n d wn wr q r
    let aig := res.aig
    let wn := res.wn
    let wr := res.wr
    let q := res.q
    let r := res.r
    have := res.hle
    let falseRef := falseRef.cast this
    let trueRef := trueRef.cast this
    let n := n.cast this
    let d := d.cast this
    let res := go aig curr falseRef trueRef n d wn wr q r
    let aig := res.aig
    let q := res.q
    let r := res.r
    have := by
      refine Nat.le_trans ?_ res.hle
      apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := AIG.RefVec.ite)
      apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := AIG.RefVec.ite)
      apply AIG.LawfulOperator.le_size_of_le_aig_size (f := BVPred.mkUlt)
      apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := blastSub)
      apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := blastShiftConcat)
      apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := blastShiftConcat)
      apply AIG.LawfulVecOperator.le_size (f := blastShiftConcat)
    ⟨aig, q, r, this⟩

theorem go_le_size (aig : AIG α) (curr : Nat) (falseRef trueRef : AIG.Ref aig)
    (n d : AIG.RefVec aig w) (wn wr : Nat) (q r : AIG.RefVec aig w) :
    aig.decls.size ≤ (go aig curr falseRef trueRef n d wn wr q r).aig.decls.size := by
  unfold go
  dsimp only
  split
  · simp
  · refine Nat.le_trans ?_ (by apply go_le_size)
    apply blastUdiv.blastDivSubtractShift_le_size

theorem go_decl_eq (aig : AIG α) (curr : Nat) (falseRef trueRef : AIG.Ref aig)
     (n d : AIG.RefVec aig w) (wn wr : Nat) (q r : AIG.RefVec aig w) :
    ∀ (idx : Nat) (h1) (h2),
        (go aig curr falseRef trueRef n d wn wr q r).aig.decls[idx]'h2 = aig.decls[idx]'h1 := by
  generalize hgo : go aig curr falseRef trueRef n d wn wr q r = res
  unfold go at hgo
  dsimp only at hgo
  split at hgo
  · simp [← hgo]
  · rw [← hgo]
    intro idx h1 h2
    rw [go_decl_eq]
    rw [blastDivSubtractShift_decl_eq]
    apply Nat.lt_of_lt_of_le
    · exact h1
    · apply blastDivSubtractShift_le_size

end blastUdiv

def blastUdiv (aig : AIG α) (input : AIG.BinaryRefVec aig w) : AIG.RefVecEntry α w :=
  let res := blastConst aig 0#w
  let aig := res.aig
  let zero := res.vec
  let input := input.cast <| AIG.LawfulVecOperator.le_size (f := blastConst) ..

  let res := aig.mkConstCached false
  let aig := res.aig
  let falseRef := res.ref
  have := AIG.LawfulOperator.le_size (f := AIG.mkConstCached) ..
  let zero := zero.cast this
  let input := input.cast this

  let res := aig.mkConstCached true
  let aig := res.aig
  let trueRef := res.ref
  have := AIG.LawfulOperator.le_size (f := AIG.mkConstCached) ..
  let falseRef := falseRef.cast this
  let zero := zero.cast this
  let input := input.cast this

  let ⟨lhs, rhs⟩ := input

  let res := BVPred.mkEq aig ⟨rhs, zero⟩
  let aig := res.aig
  let discr := res.ref
  have := AIG.LawfulOperator.le_size (f := BVPred.mkEq) ..
  let falseRef := falseRef.cast this
  let trueRef := trueRef.cast this
  let zero := zero.cast this
  let lhs := lhs.cast this
  let rhs := rhs.cast this

  let res := blastUdiv.go aig w falseRef trueRef lhs rhs w 0 zero zero
  let aig := res.aig
  let divRes := res.q
  have := blastUdiv.go_le_size ..
  let zero := zero.cast this
  let discr := discr.cast this

  AIG.RefVec.ite aig ⟨discr, zero, divRes⟩

instance : AIG.LawfulVecOperator α AIG.BinaryRefVec blastUdiv where
  le_size := by
    intros
    unfold blastUdiv
    apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := AIG.RefVec.ite)
    refine Nat.le_trans ?_ (by apply blastUdiv.go_le_size)
    apply AIG.LawfulOperator.le_size_of_le_aig_size (f := BVPred.mkEq)
    apply AIG.LawfulOperator.le_size_of_le_aig_size (f := AIG.mkConstCached)
    apply AIG.LawfulOperator.le_size_of_le_aig_size (f := AIG.mkConstCached)
    apply AIG.LawfulVecOperator.le_size (f := blastConst)
  decl_eq := by
    intros
    unfold blastUdiv
    rw [AIG.LawfulVecOperator.decl_eq (f := AIG.RefVec.ite)]
    rw [blastUdiv.go_decl_eq]
    rw [AIG.LawfulOperator.decl_eq (f := BVPred.mkEq)]
    rw [AIG.LawfulOperator.decl_eq (f := AIG.mkConstCached)]
    rw [AIG.LawfulOperator.decl_eq (f := AIG.mkConstCached)]
    rw [AIG.LawfulVecOperator.decl_eq (f := blastConst)]
    · apply AIG.LawfulVecOperator.lt_size_of_lt_aig_size (f := blastConst)
      assumption
    · apply AIG.LawfulOperator.lt_size_of_lt_aig_size (f := AIG.mkConstCached)
      apply AIG.LawfulVecOperator.lt_size_of_lt_aig_size (f := blastConst)
      assumption
    · apply AIG.LawfulOperator.lt_size_of_lt_aig_size (f := AIG.mkConstCached)
      apply AIG.LawfulOperator.lt_size_of_lt_aig_size (f := AIG.mkConstCached)
      apply AIG.LawfulVecOperator.lt_size_of_lt_aig_size (f := blastConst)
      assumption
    · apply AIG.LawfulOperator.lt_size_of_lt_aig_size (f := BVPred.mkEq)
      apply AIG.LawfulOperator.lt_size_of_lt_aig_size (f := AIG.mkConstCached)
      apply AIG.LawfulOperator.lt_size_of_lt_aig_size (f := AIG.mkConstCached)
      apply AIG.LawfulVecOperator.lt_size_of_lt_aig_size (f := blastConst)
      assumption
    · refine Nat.le_trans ?_ (by apply blastUdiv.go_le_size)
      apply AIG.LawfulOperator.lt_size_of_lt_aig_size (f := BVPred.mkEq)
      apply AIG.LawfulOperator.lt_size_of_lt_aig_size (f := AIG.mkConstCached)
      apply AIG.LawfulOperator.lt_size_of_lt_aig_size (f := AIG.mkConstCached)
      apply AIG.LawfulVecOperator.lt_size_of_lt_aig_size (f := blastConst)
      assumption

end bitblast
end BVExpr


end Std.Tactic.BVDecide
