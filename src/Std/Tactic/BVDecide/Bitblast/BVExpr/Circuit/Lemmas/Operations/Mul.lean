/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Basic
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Add
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.ShiftLeft
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Const
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Mul


/-!
This module contains the verification of the bitblaster for `BitVec.mul` from `Impl.Operations.Mul`.
-/

namespace Std.Tactic.BVDecide

open Std.Sat
open Std.Sat.AIG

namespace BVExpr

namespace bitblast
namespace blastMul

theorem go_denote_eq {w : Nat} (aig : AIG BVBit) (curr : Nat) (hcurr : curr + 1 ≤ w)
    (acc : AIG.RefVec aig w) (lhs rhs : AIG.RefVec aig w) (lexpr rexpr : BitVec w) (assign : Assignment)
    (hleft : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, lhs.get idx hidx, assign.toAIGAssignment⟧ = lexpr.getLsbD idx)
    (hright : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, rhs.get idx hidx, assign.toAIGAssignment⟧ = rexpr.getLsbD idx)
    (hacc : ∀ (idx : Nat) (hidx : idx < w),
                ⟦aig, acc.get idx hidx, assign.toAIGAssignment⟧
                  =
                (BitVec.mulRec lexpr rexpr curr).getLsbD idx) :
    ∀ (idx : Nat) (hidx : idx < w),
        ⟦
          (go aig lhs rhs (curr + 1) acc).aig,
          (go aig lhs rhs (curr + 1) acc).vec.get idx hidx,
          assign.toAIGAssignment
        ⟧
          =
        (BitVec.mulRec lexpr rexpr w).getLsbD idx := by
  intro idx hidx
  generalize hgo: go aig lhs rhs (curr + 1) acc = res
  unfold go at hgo
  split at hgo
  · dsimp only at hgo
    rw [← hgo]
    rw [go_denote_eq]
    · omega
    · intro idx hidx
      simp only [RefVec.get_cast, Ref.cast_eq]
      rw [AIG.LawfulVecOperator.denote_mem_prefix (f := RefVec.ite)]
      rw [AIG.LawfulVecOperator.denote_mem_prefix (f := blastAdd)]
      rw [AIG.LawfulVecOperator.denote_mem_prefix (f := blastShiftLeftConst)]
      rw [hleft]
    · intro idx hidx
      simp only [RefVec.get_cast, Ref.cast_eq]
      rw [AIG.LawfulVecOperator.denote_mem_prefix (f := RefVec.ite)]
      rw [AIG.LawfulVecOperator.denote_mem_prefix (f := blastAdd)]
      rw [AIG.LawfulVecOperator.denote_mem_prefix (f := blastShiftLeftConst)]
      rw [hright]
    · intro idx hidx
      rw [BitVec.mulRec_succ_eq]
      simp only [RefVec.denote_ite, RefVec.get_cast, Ref.cast_eq, BitVec.ofNat_eq_ofNat]
      split
      · next hdiscr =>
        have : rexpr.getLsbD (curr + 1) = true := by
          rw [AIG.LawfulVecOperator.denote_mem_prefix (f := blastAdd)] at hdiscr
          rw [AIG.LawfulVecOperator.denote_mem_prefix (f := blastShiftLeftConst)] at hdiscr
          rw [hright] at hdiscr
          exact hdiscr
        simp only [this, ↓reduceIte]
        rw [denote_blastAdd]
        · intros
          simp only [RefVec.get_cast, Ref.cast_eq]
          rw [AIG.LawfulVecOperator.denote_mem_prefix (f := blastShiftLeftConst)]
          rw [hacc]
        · intros
          simp only [denote_blastShiftLeftConst, BitVec.getLsbD_shiftLeft]
          split
          · next hdiscr => simp [hdiscr]
          · next hidx hdiscr =>
            rw [hleft]
            simp [hdiscr, hidx]
      · next hdiscr =>
        have : rexpr.getLsbD (curr + 1) = false := by
          rw [AIG.LawfulVecOperator.denote_mem_prefix (f := blastAdd)] at hdiscr
          rw [AIG.LawfulVecOperator.denote_mem_prefix (f := blastShiftLeftConst)] at hdiscr
          rw [hright] at hdiscr
          simp [hdiscr]
        simp only [this, Bool.false_eq_true, ↓reduceIte, BitVec.add_zero]
        rw [AIG.LawfulVecOperator.denote_mem_prefix (f := blastAdd)]
        rw [AIG.LawfulVecOperator.denote_mem_prefix (f := blastShiftLeftConst)]
        rw [hacc]
  · have : curr + 1 = w := by omega
    subst this
    rw [← hgo]
    rw [hacc]
    rw [BitVec.mulRec_succ_eq]
    have : rexpr.getLsbD (curr + 1) = false := by
      apply BitVec.getLsbD_ge
      omega
    simp [this]
termination_by w - curr
decreasing_by
  simp only [InvImage, WellFoundedRelation.rel, Nat.lt_wfRel, sizeOf_nat, Nat.lt_eq, gt_iff_lt]
  omega

theorem denote_blast (aig : AIG BVBit) (lhs rhs : BitVec w) (assign : Assignment)
      (input : BinaryRefVec aig w)
      (hleft : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, input.lhs.get idx hidx, assign.toAIGAssignment⟧ = lhs.getLsbD idx)
      (hright : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, input.rhs.get idx hidx, assign.toAIGAssignment⟧ = rhs.getLsbD idx) :
      ∀ (idx : Nat) (hidx : idx < w),
        ⟦(blast aig input).aig, (blast aig input).vec.get idx hidx, assign.toAIGAssignment⟧
          =
        (lhs * rhs).getLsbD idx := by
  intro idx hidx
  rw [BitVec.getLsbD_mul]
  generalize hb : blast aig input = res
  unfold blast at hb
  dsimp only at hb
  split at hb
  · omega
  · next hne =>
    have := Nat.exists_eq_succ_of_ne_zero hne
    rcases this with ⟨w, hw⟩
    subst hw
    rw [← hb]
    rw [go_denote_eq]
    · omega
    · intro idx hidx
      rw [AIG.LawfulVecOperator.denote_mem_prefix (f := RefVec.ite)]
      rw [AIG.LawfulVecOperator.denote_mem_prefix (f := blastConst)]
      · simp [hleft]
      · simp [Ref.hgate]
    · intro idx hidx
      rw [AIG.LawfulVecOperator.denote_mem_prefix (f := RefVec.ite)]
      rw [AIG.LawfulVecOperator.denote_mem_prefix (f := blastConst)]
      · simp [hright]
      · simp [Ref.hgate]
    · intro idx hidx
      rw [BitVec.mulRec_zero_eq]
      simp only [Nat.succ_eq_add_one, RefVec.denote_ite, BinaryRefVec.rhs_get_cast,
        Ref.gate_cast, BinaryRefVec.lhs_get_cast, denote_blastConst,
        BitVec.ofNat_eq_ofNat, eval_const, BitVec.getLsbD_zero, Bool.if_false_right,
        Bool.decide_eq_true]
      split
      · next heq =>
        rw [← hright] at heq
        · rw [AIG.LawfulVecOperator.denote_mem_prefix (f := blastConst)]
          rw [AIG.LawfulVecOperator.denote_mem_prefix (f := blastConst)]
          · simp [heq, hleft]
          · simp [Ref.hgate]
          · simp [Ref.hgate]
        · omega
      · next heq =>
        simp only [Bool.not_eq_true] at heq
        rw [← hright] at heq
        · rw [AIG.LawfulVecOperator.denote_mem_prefix (f := blastConst)]
          · simp [heq]
          · simp [Ref.hgate]
        · omega


end blastMul

theorem denote_blastMul (aig : AIG BVBit) (lhs rhs : BitVec w) (assign : Assignment)
      (input : BinaryRefVec aig w)
      (hleft : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, input.lhs.get idx hidx, assign.toAIGAssignment⟧ = lhs.getLsbD idx)
      (hright : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, input.rhs.get idx hidx, assign.toAIGAssignment⟧ = rhs.getLsbD idx) :
      ∀ (idx : Nat) (hidx : idx < w),
        ⟦(blastMul aig input).aig, (blastMul aig input).vec.get idx hidx, assign.toAIGAssignment⟧
          =
        (lhs * rhs).getLsbD idx := by
  intro idx hidx
  generalize hb : blastMul aig input = res
  unfold blastMul at hb
  dsimp only at hb
  split at hb
  · rw [← hb, blastMul.denote_blast] <;> assumption
  · rw [BitVec.mul_comm, ← hb, blastMul.denote_blast] <;> assumption

end bitblast
end BVExpr

end Std.Tactic.BVDecide
