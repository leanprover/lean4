/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Basic
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Add
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.ShiftLeft
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Const
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Mul

@[expose] public section


/-!
This module contains the verification of the bitblaster for `BitVec.mul` from `Impl.Operations.Mul`.
-/

namespace Std.Tactic.BVDecide

open Std.Sat
open Std.Sat.AIG

variable [Hashable α] [DecidableEq α]

namespace BVExpr

namespace bitblast
namespace blastMul

theorem go_denote_eq {w : Nat} (aig : AIG α) (curr : Nat) (hcurr : curr + 1 ≤ w)
    (acc : AIG.RefVec aig w) (lhs rhs : AIG.RefVec aig w) (lexpr rexpr : BitVec w) (assign : α → Bool)
    (hleft : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, lhs.get idx hidx, assign⟧ = lexpr.getLsbD idx)
    (hright : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, rhs.get idx hidx, assign⟧ = rexpr.getLsbD idx)
    (hacc : ∀ (idx : Nat) (hidx : idx < w),
                ⟦aig, acc.get idx hidx, assign⟧
                  =
                (BitVec.mulRec lexpr rexpr curr).getLsbD idx) :
    ∀ (idx : Nat) (hidx : idx < w),
        ⟦
          (go aig lhs rhs (curr + 1) acc).aig,
          (go aig lhs rhs (curr + 1) acc).vec.get idx hidx,
          assign
        ⟧
          =
        (BitVec.mulRec lexpr rexpr w).getLsbD idx := by
  intro idx hidx
  generalize hgo: go aig lhs rhs (curr + 1) acc = res
  unfold go at hgo
  split at hgo
  · split at hgo
    next hconstant =>
      rw [← hgo]
      rw [go_denote_eq]
      · omega
      · exact hleft
      · exact hright
      · intro idx hidx
        rw [BitVec.mulRec_succ_eq]
        have : rexpr.getLsbD (curr + 1) = false := by
          rw [← hright]
          exact of_isConstant hconstant
        simp [this, hacc]
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
        next hdiscr =>
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
            next hdiscr => simp [hdiscr]
            next hidx hdiscr =>
              rw [hleft]
              simp [hdiscr, hidx]
        next hdiscr =>
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
      apply BitVec.getLsbD_of_ge
      omega
    simp
termination_by w - curr

theorem denote_blast (aig : AIG α) (lhs rhs : BitVec w) (assign : α → Bool)
      (input : BinaryRefVec aig w)
      (hleft : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, input.lhs.get idx hidx, assign⟧ = lhs.getLsbD idx)
      (hright : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, input.rhs.get idx hidx, assign⟧ = rhs.getLsbD idx) :
      ∀ (idx : Nat) (hidx : idx < w),
        ⟦(blast aig input).aig, (blast aig input).vec.get idx hidx, assign⟧
          =
        (lhs * rhs).getLsbD idx := by
  intro idx hidx
  rw [BitVec.getLsbD_mul]
  generalize hb : blast aig input = res
  unfold blast at hb
  dsimp only at hb
  split at hb
  · omega
  next hne =>
    have := Nat.exists_eq_succ_of_ne_zero hne
    rcases this with ⟨w, hw⟩
    subst hw
    rw [← hb]
    rw [go_denote_eq]
    · omega
    · intro idx hidx
      rw [AIG.LawfulVecOperator.denote_mem_prefix (f := RefVec.ite)]
      · simp [hleft]
      · simp [Ref.hgate]
    · intro idx hidx
      rw [AIG.LawfulVecOperator.denote_mem_prefix (f := RefVec.ite)]
      · simp [hright]
      · simp [Ref.hgate]
    · intro idx hidx
      rw [BitVec.mulRec_zero_eq]
      simp only [Nat.succ_eq_add_one, RefVec.denote_ite,
        denote_blastConst,
        BitVec.ofNat_eq_ofNat, BitVec.getLsbD_zero, Bool.if_false_right,
        Bool.decide_eq_true]
      split
      next heq =>
        rw [← hright] at heq
        · simp [heq, hleft]
        · omega
      next heq =>
        simp only [Bool.not_eq_true] at heq
        rw [← hright] at heq
        · simp [heq]
        · omega


end blastMul

theorem denote_blastMul (aig : AIG α) (lhs rhs : BitVec w) (assign : α → Bool)
      (input : BinaryRefVec aig w)
      (hleft : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, input.lhs.get idx hidx, assign⟧ = lhs.getLsbD idx)
      (hright : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, input.rhs.get idx hidx, assign⟧ = rhs.getLsbD idx) :
      ∀ (idx : Nat) (hidx : idx < w),
        ⟦(blastMul aig input).aig, (blastMul aig input).vec.get idx hidx, assign⟧
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
