/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Udiv
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Umod

/-!
This module contains the verification of the `BitVec.umod` bitblaster from `Impl.Operations.Umod`.
-/

namespace Std.Tactic.BVDecide

open Std.Sat
open Std.Sat.AIG

namespace BVExpr
namespace bitblast

variable [Hashable α] [DecidableEq α]

namespace blastUmod

open blastUdiv

theorem denote_go_eq_divRec_r (aig : AIG α) (assign : α → Bool) (curr : Nat) (lhs rhs rbv qbv : BitVec w)
    (falseRef trueRef : AIG.Ref aig) (n d q r : AIG.RefVec aig w) (wn wr : Nat)
    (hleft : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, n.get idx hidx, assign⟧ = lhs.getLsbD idx)
    (hright : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, d.get idx hidx, assign⟧ = rhs.getLsbD idx)
    (hq : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, q.get idx hidx, assign⟧ = qbv.getLsbD idx)
    (hr : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, r.get idx hidx, assign⟧ = rbv.getLsbD idx)
    (hfalse : ⟦aig, falseRef, assign⟧ = false)
    (htrue : ⟦aig, trueRef, assign⟧ = true)
      :
    ∀ (idx : Nat) (hidx : idx < w),
      ⟦
        (go aig curr falseRef trueRef n d wn wr q r).aig,
        (go aig curr falseRef trueRef n d wn wr q r).r.get idx hidx,
        assign
      ⟧
        =
      (BitVec.divRec curr { n := lhs, d := rhs} { wn, wr, q := qbv, r := rbv }).r.getLsbD idx := by
  induction curr generalizing aig wn wr q r qbv rbv with
  | zero =>
    intro idx hidx
    simp [go, hr]
  | succ curr ih =>
    intro idx hidx
    rw [go, BitVec.divRec_succ, BitVec.divSubtractShift]
    split
    · next hdiscr =>
      rw [ih]
      · rfl
      · intro idx hidx
        rw [blastDivSubtractShift_denote_mem_prefix]
        · simp [hleft]
        · simp [Ref.hgate]
      · intro idx hidx
        rw [blastDivSubtractShift_denote_mem_prefix]
        · simp [hright]
        · simp [Ref.hgate]
      · intro idx hidx
        rw [denote_blastDivSubtractShift_q (rbv := rbv) (qbv := qbv) (lhs := lhs) (rhs := rhs)]
        · rw [BitVec.divSubtractShift]
          simp [hdiscr]
        · exact hleft
        · exact hright
        · exact hq
        · exact hr
        · exact hfalse
        · exact htrue
      · intro idx hidx
        rw [denote_blastDivSubtractShift_r (rbv := rbv) (qbv := qbv) (lhs := lhs) (rhs := rhs)]
        · rw [BitVec.divSubtractShift]
          simp [hdiscr]
        · exact hleft
        · exact hright
        · exact hr
        · exact hfalse
      · rw [blastDivSubtractShift_denote_mem_prefix]
        · simp [hfalse]
        · simp [Ref.hgate]
      · rw [blastDivSubtractShift_denote_mem_prefix]
        · simp [htrue]
        · simp [Ref.hgate]
    · next hdiscr =>
      rw [ih]
      · rfl
      · intro idx hidx
        rw [blastDivSubtractShift_denote_mem_prefix]
        · simp [hleft]
        · simp [Ref.hgate]
      · intro idx hidx
        rw [blastDivSubtractShift_denote_mem_prefix]
        · simp [hright]
        · simp [Ref.hgate]
      · intro idx hidx
        rw [denote_blastDivSubtractShift_q (rbv := rbv) (qbv := qbv) (lhs := lhs) (rhs := rhs)]
        · rw [BitVec.divSubtractShift]
          simp [hdiscr]
        · exact hleft
        · exact hright
        · exact hq
        · exact hr
        · exact hfalse
        · exact htrue
      · intro idx hidx
        rw [denote_blastDivSubtractShift_r (rbv := rbv) (qbv := qbv) (lhs := lhs) (rhs := rhs)]
        · rw [BitVec.divSubtractShift]
          simp [hdiscr]
        · exact hleft
        · exact hright
        · exact hr
        · exact hfalse
      · rw [blastDivSubtractShift_denote_mem_prefix]
        · simp [hfalse]
        · simp [Ref.hgate]
      · rw [blastDivSubtractShift_denote_mem_prefix]
        · simp [htrue]
        · simp [Ref.hgate]

theorem denote_go (aig : AIG α) (assign : α → Bool) (lhs rhs : BitVec w)
    (falseRef trueRef : AIG.Ref aig) (n d q r : AIG.RefVec aig w)
    (hleft : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, n.get idx hidx, assign⟧ = lhs.getLsbD idx)
    (hright : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, d.get idx hidx, assign⟧ = rhs.getLsbD idx)
    (hq : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, q.get idx hidx, assign⟧ = false)
    (hr : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, r.get idx hidx, assign⟧ = false)
    (hfalse : ⟦aig, falseRef, assign⟧ = false)
    (htrue : ⟦aig, trueRef, assign⟧ = true)
    (hzero : 0#w < rhs)
      :
    ∀ (idx : Nat) (hidx : idx < w),
      ⟦
        (go aig w falseRef trueRef n d w 0 q r).aig,
        (go aig w falseRef trueRef n d w 0 q r).r.get idx hidx,
        assign
      ⟧
        =
      (lhs % rhs).getLsbD idx := by
  intro idx hidx
  rw [BitVec.umod_eq_divRec hzero]
  rw [BitVec.DivModState.init]
  rw [denote_go_eq_divRec_r (lhs := lhs) (rhs := rhs) (qbv := 0#w) (rbv := 0#w)]
  · exact hleft
  · exact hright
  · simp [hq]
  · simp [hr]
  · exact hfalse
  · exact htrue

end blastUmod

theorem denote_blastUmod (aig : AIG α) (lhs rhs : BitVec w) (assign : α → Bool)
      (input : BinaryRefVec aig w)
      (hleft : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, input.lhs.get idx hidx, assign⟧ = lhs.getLsbD idx)
      (hright : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, input.rhs.get idx hidx, assign⟧ = rhs.getLsbD idx) :
      ∀ (idx : Nat) (hidx : idx < w),
        ⟦(blastUmod aig input).aig, (blastUmod aig input).vec.get idx hidx, assign⟧
          =
        (lhs % rhs).getLsbD idx := by
  intro idx hidx
  unfold blastUmod
  simp only [Ref.cast_eq, id_eq, Int.reduceNeg, RefVec.denote_ite,
    LawfulVecOperator.denote_input_entry, RefVec.get_cast]
  split
  · next hdiscr =>
    rw [blastUdiv.go_denote_mem_prefix] at hdiscr
    rw [BVPred.mkEq_denote_eq (lhs := rhs) (rhs := 0#w)] at hdiscr
    · simp only [beq_iff_eq] at hdiscr
      rw [hdiscr]
      rw [blastUdiv.go_denote_mem_prefix]
      rw [AIG.LawfulOperator.denote_mem_prefix (f := BVPred.mkEq)]
      rw [AIG.LawfulOperator.denote_mem_prefix (f := AIG.mkConstCached)]
      rw [AIG.LawfulOperator.denote_mem_prefix (f := AIG.mkConstCached)]
      rw [AIG.LawfulVecOperator.denote_mem_prefix (f := blastConst)]
      · simp [hleft]
      · simp [Ref.hgate]
    · intro idx hidx
      rw [AIG.LawfulOperator.denote_mem_prefix (f := AIG.mkConstCached)]
      rw [AIG.LawfulOperator.denote_mem_prefix (f := AIG.mkConstCached)]
      rw [AIG.LawfulVecOperator.denote_mem_prefix (f := blastConst)]
      · simp [hright]
      · simp [Ref.hgate]
    · intro idx hidx
      rw [AIG.LawfulOperator.denote_mem_prefix (f := AIG.mkConstCached)]
      rw [AIG.LawfulOperator.denote_mem_prefix (f := AIG.mkConstCached)]
      · simp only [RefVec.get_cast, Ref.cast_eq, BitVec.getLsbD_zero]
        rw [denote_blastConst]
        simp
      · simp [Ref.hgate]
  · next hdiscr =>
    rw [blastUdiv.go_denote_mem_prefix] at hdiscr
    rw [BVPred.mkEq_denote_eq (lhs := rhs) (rhs := 0#w)] at hdiscr
    · have hzero : 0#w < rhs := by
        rw [Normalize.BitVec.zero_lt_iff_zero_neq]
        simpa using hdiscr
      rw [blastUmod.denote_go (hzero := hzero)]
      · intro idx hidx
        rw [AIG.LawfulOperator.denote_mem_prefix (f := BVPred.mkEq)]
        rw [AIG.LawfulOperator.denote_mem_prefix (f := AIG.mkConstCached)]
        rw [AIG.LawfulOperator.denote_mem_prefix (f := AIG.mkConstCached)]
        rw [AIG.LawfulVecOperator.denote_mem_prefix (f := blastConst)]
        · simp [hleft]
        · simp [Ref.hgate]
      · intro idx hidx
        rw [AIG.LawfulOperator.denote_mem_prefix (f := BVPred.mkEq)]
        rw [AIG.LawfulOperator.denote_mem_prefix (f := AIG.mkConstCached)]
        rw [AIG.LawfulOperator.denote_mem_prefix (f := AIG.mkConstCached)]
        rw [AIG.LawfulVecOperator.denote_mem_prefix (f := blastConst)]
        · simp [hright]
        · simp [Ref.hgate]
      · intro idx hidx
        rw [AIG.LawfulOperator.denote_mem_prefix (f := BVPred.mkEq)]
        rw [AIG.LawfulOperator.denote_mem_prefix (f := AIG.mkConstCached)]
        rw [AIG.LawfulOperator.denote_mem_prefix (f := AIG.mkConstCached)]
        · simp only [RefVec.get_cast, Ref.cast_eq]
          rw [denote_blastConst]
          simp
        · simp [Ref.hgate]
      · intro idx hidx
        rw [AIG.LawfulOperator.denote_mem_prefix (f := BVPred.mkEq)]
        rw [AIG.LawfulOperator.denote_mem_prefix (f := AIG.mkConstCached)]
        rw [AIG.LawfulOperator.denote_mem_prefix (f := AIG.mkConstCached)]
        · simp only [RefVec.get_cast, Ref.cast_eq]
          rw [denote_blastConst]
          simp
        · simp [Ref.hgate]
      · rw [AIG.LawfulOperator.denote_mem_prefix (f := BVPred.mkEq)]
        rw [AIG.LawfulOperator.denote_mem_prefix (f := AIG.mkConstCached)]
        · simp
        · simp [Ref.hgate]
      · rw [AIG.LawfulOperator.denote_mem_prefix (f := BVPred.mkEq)]
        · simp
        · simp [Ref.hgate]
    · intro idx hdix
      rw [AIG.LawfulOperator.denote_mem_prefix (f := AIG.mkConstCached)]
      rw [AIG.LawfulOperator.denote_mem_prefix (f := AIG.mkConstCached)]
      rw [AIG.LawfulVecOperator.denote_mem_prefix (f := blastConst)]
      · simp [hright]
      · simp [Ref.hgate]
    · intro idx hdix
      rw [AIG.LawfulOperator.denote_mem_prefix (f := AIG.mkConstCached)]
      rw [AIG.LawfulOperator.denote_mem_prefix (f := AIG.mkConstCached)]
      · simp only [RefVec.get_cast, Ref.cast_eq, BitVec.getLsbD_zero]
        rw [denote_blastConst]
        simp
      · simp [Ref.hgate]

end bitblast
end BVExpr

end Std.Tactic.BVDecide
