/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Sub
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Eq
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Ult
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.ZeroExtend
public import Std.Sat.AIG.If
import Init.Grind

public section

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
  let bit := AIG.RefVec.emptyWithCapacity (w + 1) |>.push bit
  let new := bit.append lhs
  blastZeroExtend aig ⟨1 + w, new⟩

@[grind! .]
theorem blastShiftConcat_le_size (aig : AIG α) (input : ShiftConcatInput aig w) :
    aig.decls.size ≤ (blastShiftConcat aig input).aig.decls.size := by
  intros
  unfold blastShiftConcat
  grind

@[grind =]
theorem blastShiftConcat_decl_eq (aig : AIG α) (input : ShiftConcatInput aig w) (idx : Nat)
    (h1 : idx < aig.decls.size) (h2 : idx < (blastShiftConcat aig input).aig.decls.size) :
    (blastShiftConcat aig input).aig.decls[idx] = aig.decls[idx] := by
  intros
  unfold blastShiftConcat
  grind

instance inst : AIG.LawfulVecOperator α ShiftConcatInput blastShiftConcat where
  le_size := blastShiftConcat_le_size
  decl_eq := blastShiftConcat_decl_eq

structure BlastDivSubtractShiftOutput (old : AIG α) (w : Nat) where
  aig : AIG α
  wn : Nat
  wr : Nat
  q : AIG.RefVec aig w
  r : AIG.RefVec aig w
  hle : old.decls.size ≤ aig.decls.size

def blastDivSubtractShift (aig : AIG α) (n d : AIG.RefVec aig w) (wn wr : Nat)
    (q r : AIG.RefVec aig w) : BlastDivSubtractShiftOutput aig w :=
  let wn := wn - 1
  let wr := wr + 1
  let falseRef := aig.mkConstCached false
  let res := blastUdiv.blastShiftConcat aig ⟨r, n.getD wn falseRef⟩
  let aig := res.aig
  let r' := res.vec
  have := AIG.LawfulVecOperator.le_size (f := blastUdiv.blastShiftConcat) ..
  let d := d.cast this
  let q := q.cast this

  let falseRef := aig.mkConstCached false
  let res := blastUdiv.blastShiftConcat aig ⟨q, falseRef⟩
  let aig := res.aig
  let posQ := res.vec
  have := AIG.LawfulVecOperator.le_size (f := blastUdiv.blastShiftConcat) ..
  let d := d.cast this
  let q := q.cast this
  let r' := r'.cast this

  let trueRef := aig.mkConstCached true
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
  ⟨aig, wn, wr, nextQ, nextR, by grind⟩

theorem blastDivSubtractShift_le_size (aig : AIG α)
     (n d : AIG.RefVec aig w) (wn wr : Nat) (q r : AIG.RefVec aig w) :
    aig.decls.size ≤ (blastDivSubtractShift aig n d wn wr q r).aig.decls.size := by
  unfold blastDivSubtractShift
  grind

theorem blastDivSubtractShift_decl_eq (aig : AIG α) (n d : AIG.RefVec aig w) (wn wr : Nat)
    (q r : AIG.RefVec aig w) :
    ∀ (idx : Nat) (h1) (h2),
        (blastDivSubtractShift aig n d wn wr q r).aig.decls[idx]'h2 = aig.decls[idx]'h1 := by
  generalize hres : blastDivSubtractShift aig n d wn wr q r = res
  unfold blastDivSubtractShift at hres
  dsimp only at hres
  rw [← hres]
  grind

structure BlastUdivOutput (old : AIG α) (w : Nat) where
  aig : AIG α
  q : AIG.RefVec aig w
  r : AIG.RefVec aig w
  hle : old.decls.size ≤ aig.decls.size

def go (aig : AIG α) (curr : Nat) (n d : AIG.RefVec aig w)
    (wn wr : Nat) (q r : AIG.RefVec aig w) : BlastUdivOutput aig w :=
  match curr with
  | 0 => ⟨aig, q, r, by omega⟩
  | curr + 1 =>
    let res := blastDivSubtractShift aig n d wn wr q r
    let aig := res.aig
    let wn := res.wn
    let wr := res.wr
    let q := res.q
    let r := res.r
    have := res.hle
    let n := n.cast this
    let d := d.cast this
    let res := go aig curr n d wn wr q r
    let aig := res.aig
    let q := res.q
    let r := res.r
    have := by
      refine Nat.le_trans ?_ res.hle
      clear aig q r res
      grind
    ⟨aig, q, r, this⟩

@[grind! .]
theorem go_le_size (aig : AIG α) (curr : Nat) (n d : AIG.RefVec aig w) (wn wr : Nat)
    (q r : AIG.RefVec aig w) :
    aig.decls.size ≤ (go aig curr n d wn wr q r).aig.decls.size := by
  unfold go
  dsimp only
  split
  · simp
  · refine Nat.le_trans ?_ (by apply go_le_size)
    apply blastUdiv.blastDivSubtractShift_le_size

@[grind =]
theorem go_decl_eq (aig : AIG α) (curr : Nat) (n d : AIG.RefVec aig w) (wn wr : Nat)
    (q r : AIG.RefVec aig w) :
    ∀ (idx : Nat) (h1) (h2),
        (go aig curr n d wn wr q r).aig.decls[idx]'h2 = aig.decls[idx]'h1 := by
  generalize hgo : go aig curr n d wn wr q r = res
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
  let divRes := res.q
  have := blastUdiv.go_le_size ..
  let zero := zero.cast this
  let discr := discr.cast this

  AIG.RefVec.ite aig ⟨discr, zero, divRes⟩

@[grind! .]
theorem blastUdiv_le_size (aig : AIG α) (input : aig.BinaryRefVec w) :
    aig.decls.size ≤ (blastUdiv aig input).aig.decls.size := by
  intros
  unfold blastUdiv
  grind
  
@[grind =]
theorem blastUdiv_decl_eq (aig : AIG α) (input : aig.BinaryRefVec w) (idx : Nat)
    (h1 : idx < aig.decls.size) (h2 : idx < (blastUdiv aig input).aig.decls.size) :
    (blastUdiv aig input).aig.decls[idx] = aig.decls[idx] := by
  intros
  unfold blastUdiv
  grind

instance : AIG.LawfulVecOperator α AIG.BinaryRefVec blastUdiv where
  le_size := blastUdiv_le_size
  decl_eq := blastUdiv_decl_eq

end bitblast
end BVExpr


end Std.Tactic.BVDecide
