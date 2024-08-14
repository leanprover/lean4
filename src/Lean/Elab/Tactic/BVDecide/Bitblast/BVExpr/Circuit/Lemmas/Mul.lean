/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Lean.Elab.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Basic
import Lean.Elab.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Add
import Lean.Elab.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.ShiftLeft
import Lean.Elab.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Const
import Lean.Elab.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Mul


/-!
This module contains the verification of the bitblaster for `BitVec.mul` from `Impl.Mul`.
-/

namespace Lean.Elab.Tactic.BVDecide

open Std.Sat
open Std.Sat.AIG

namespace BVExpr

namespace bitblast
namespace blastMul

theorem go_denote_eq {w : Nat} (aig : AIG BVBit) (curr : Nat) (hcurr : curr + 1 ≤ w)
    (acc : AIG.RefVec aig w) (lhs rhs : AIG.RefVec aig w) (lexpr rexpr : BitVec w) (assign : Assignment)
    (hleft : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, lhs.get idx hidx, assign.toAIGAssignment⟧ = lexpr.getLsb idx)
    (hright : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, rhs.get idx hidx, assign.toAIGAssignment⟧ = rexpr.getLsb idx)
    (hacc : ∀ (idx : Nat) (hidx : idx < w),
                ⟦aig, acc.get idx hidx, assign.toAIGAssignment⟧
                  =
                (BitVec.mulRec lexpr rexpr curr).getLsb idx) :
    ∀ (idx : Nat) (hidx : idx < w),
        ⟦
          (go aig lhs rhs (curr + 1) hcurr acc).aig,
          (go aig lhs rhs (curr + 1) hcurr acc).vec.get idx hidx,
          assign.toAIGAssignment
        ⟧
          =
        (BitVec.mulRec lexpr rexpr w).getLsb idx := by
  intro idx hidx
  generalize hgo: go aig lhs rhs (curr + 1) hcurr acc = res
  unfold go at hgo
  split at hgo
  . dsimp only at hgo
    rw [← hgo]
    rw [go_denote_eq]
    . intro idx hidx
      simp only [RefVec.get_cast, Ref.cast_eq]
      rw [AIG.LawfulVecOperator.denote_mem_prefix (f := RefVec.ite)]
      rw [AIG.LawfulVecOperator.denote_mem_prefix (f := blastAdd)]
      rw [AIG.LawfulVecOperator.denote_mem_prefix (f := blastShiftLeftConst)]
      rw [hleft]
    . intro idx hidx
      simp only [RefVec.get_cast, Ref.cast_eq]
      rw [AIG.LawfulVecOperator.denote_mem_prefix (f := RefVec.ite)]
      rw [AIG.LawfulVecOperator.denote_mem_prefix (f := blastAdd)]
      rw [AIG.LawfulVecOperator.denote_mem_prefix (f := blastShiftLeftConst)]
      rw [hright]
    . intro idx hidx
      rw [BitVec.mulRec_succ_eq]
      simp only [RefVec.denote_ite, RefVec.get_cast, Ref.cast_eq, BitVec.ofNat_eq_ofNat]
      split
      . next hdiscr =>
        have : rexpr.getLsb (curr + 1) = true := by
          rw [AIG.LawfulVecOperator.denote_mem_prefix (f := blastAdd)] at hdiscr
          rw [AIG.LawfulVecOperator.denote_mem_prefix (f := blastShiftLeftConst)] at hdiscr
          rw [hright] at hdiscr
          exact hdiscr
        simp only [this, ↓reduceIte]
        rw [denote_blastAdd]
        . intros
          simp only [RefVec.get_cast, Ref.cast_eq]
          rw [AIG.LawfulVecOperator.denote_mem_prefix (f := blastShiftLeftConst)]
          rw [hacc]
        . intros
          simp only [denote_blastShiftLeftConst, BitVec.getLsb_shiftLeft]
          split
          . next hdiscr => simp [hdiscr]
          . next hidx hdiscr =>
            rw [hleft]
            simp [hdiscr, hidx]
      . next hdiscr =>
        have : rexpr.getLsb (curr + 1) = false := by
          rw [AIG.LawfulVecOperator.denote_mem_prefix (f := blastAdd)] at hdiscr
          rw [AIG.LawfulVecOperator.denote_mem_prefix (f := blastShiftLeftConst)] at hdiscr
          rw [hright] at hdiscr
          simp [hdiscr]
        simp only [this, Bool.false_eq_true, ↓reduceIte, BitVec.add_zero]
        rw [AIG.LawfulVecOperator.denote_mem_prefix (f := blastAdd)]
        rw [AIG.LawfulVecOperator.denote_mem_prefix (f := blastShiftLeftConst)]
        rw [hacc]
  . have : curr + 1 = w := by omega
    subst this
    rw [← hgo]
    rw [hacc]
    rw [BitVec.mulRec_succ_eq]
    have : rexpr.getLsb (curr + 1) = false := by
      apply BitVec.getLsb_ge
      omega
    simp [this]
termination_by w - curr
decreasing_by
  simp only [InvImage, WellFoundedRelation.rel, Nat.lt_wfRel, sizeOf_nat, Nat.lt_eq, gt_iff_lt]
  omega


end blastMul

theorem denote_blastMul (aig : AIG BVBit) (lhs rhs : BitVec w) (assign : Assignment)
      (input : BinaryRefVec aig w)
      (hleft : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, input.lhs.get idx hidx, assign.toAIGAssignment⟧ = lhs.getLsb idx)
      (hright : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, input.rhs.get idx hidx, assign.toAIGAssignment⟧ = rhs.getLsb idx) :
      ∀ (idx : Nat) (hidx : idx < w),
        ⟦(blastMul aig input).aig, (blastMul aig input).vec.get idx hidx, assign.toAIGAssignment⟧
          =
        (lhs * rhs).getLsb idx := by
  intro idx hidx
  rw [BitVec.getLsb_mul]
  generalize hb : blastMul aig input = res
  unfold blastMul at hb
  dsimp only at hb
  split at hb
  . omega
  . next hne =>
    have := Nat.exists_eq_succ_of_ne_zero hne
    rcases this with ⟨w, hw⟩
    subst hw
    rw [← hb]
    rw [blastMul.go_denote_eq]
    . intro idx hidx
      rw [AIG.LawfulVecOperator.denote_mem_prefix (f := RefVec.ite)]
      rw [AIG.LawfulVecOperator.denote_mem_prefix (f := blastConst)]
      . simp [hleft]
      . simp [Ref.hgate]
    . intro idx hidx
      rw [AIG.LawfulVecOperator.denote_mem_prefix (f := RefVec.ite)]
      rw [AIG.LawfulVecOperator.denote_mem_prefix (f := blastConst)]
      . simp [hright]
      . simp [Ref.hgate]
    . intro idx hidx
      rw [BitVec.mulRec_zero_eq]
      simp only [Nat.succ_eq_add_one, RefVec.denote_ite, BinaryRefVec.rhs_get_cast,
        Ref.gate_cast, BinaryRefVec.lhs_get_cast, denote_blastConst,
        BitVec.ofNat_eq_ofNat, eval_const, BitVec.getLsb_zero, Bool.if_false_right,
        Bool.decide_eq_true]
      split
      . next heq =>
        rw [← hright] at heq
        . rw [AIG.LawfulVecOperator.denote_mem_prefix (f := blastConst)]
          rw [AIG.LawfulVecOperator.denote_mem_prefix (f := blastConst)]
          . simp [heq, hleft]
          . simp [Ref.hgate]
          . simp [Ref.hgate]
        . omega
      . next heq =>
        simp only [Bool.not_eq_true] at heq
        rw [← hright] at heq
        . rw [AIG.LawfulVecOperator.denote_mem_prefix (f := blastConst)]
          . simp [heq]
          . simp [Ref.hgate]
        . omega

end bitblast
end BVExpr

end Lean.Elab.Tactic.BVDecide
