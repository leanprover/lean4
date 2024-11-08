/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Basic
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Const
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Var
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Not
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.ShiftLeft
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.ShiftRight
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Add
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.ZeroExtend
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Append
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Replicate
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Extract
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.RotateLeft
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.RotateRight
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.SignExtend
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Mul
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Udiv
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Umod
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Expr

/-!
This module contains the verification of the `BitVec` expressions (`BVExpr`) bitblaster from
`Impl.Expr`.
-/

namespace Std.Tactic.BVDecide

open Std.Sat
open Std.Sat.AIG

namespace BVExpr
namespace bitblast

theorem go_val_eq_bitblast (aig : AIG BVBit) (expr : BVExpr w) :
    (go aig expr).val = bitblast aig expr := by
  rfl

theorem go_denote_mem_prefix (aig : AIG BVBit) (expr : BVExpr w) (assign : Assignment) (start : Nat)
    (hstart) :
    ⟦
      (go aig expr).val.aig,
      ⟨start, by apply Nat.lt_of_lt_of_le; exact hstart; apply (go aig expr).property⟩,
      assign.toAIGAssignment
    ⟧
      =
    ⟦aig, ⟨start, hstart⟩, assign.toAIGAssignment⟧ := by
  apply denote.eq_of_isPrefix (entry := ⟨aig, start,hstart⟩)
  apply IsPrefix.of
  · intros
    apply go_decl_eq
  · intros
    apply (go aig expr).property

theorem go_denote_eq (aig : AIG BVBit) (expr : BVExpr w) (assign : Assignment) :
    ∀ (idx : Nat) (hidx : idx < w),
        ⟦(go aig expr).val.aig, (go aig expr).val.vec.get idx hidx, assign.toAIGAssignment⟧
          =
        (expr.eval assign).getLsbD idx := by
  intro idx hidx
  induction expr generalizing aig idx with
  | const =>
    simp [go, denote_blastConst]
  | var =>
    simp [go, hidx, denote_blastVar]
  | zeroExtend v inner ih =>
    simp only [go, denote_blastZeroExtend, ih, dite_eq_ite, Bool.if_false_right,
      eval_zeroExtend, BitVec.getLsbD_setWidth, hidx, decide_true, Bool.true_and,
      Bool.and_iff_right_iff_imp, decide_eq_true_eq]
    apply BitVec.lt_of_getLsbD
  | append lhs rhs lih rih =>
    rename_i lw rw
    simp only [go, denote_blastAppend, RefVec.get_cast, Ref.cast_eq, eval_append,
      BitVec.getLsbD_append]
    split
    · next hsplit =>
      simp only [hsplit, decide_true, cond_true]
      rw [rih]
    · next hsplit =>
      simp only [hsplit, decide_false, cond_false]
      rw [go_denote_mem_prefix, lih]
  | replicate n expr ih => simp [go, ih, hidx]
  | signExtend v inner ih =>
    rename_i originalWidth
    generalize hgo : (go aig (signExtend v inner)).val = res
    unfold go at hgo
    dsimp only at hgo
    have : 0 ≤ originalWidth := by omega
    cases Nat.eq_or_lt_of_le this with
    | inl heq =>
      rw [blastSignExtend_empty_eq_zeroExtend] at hgo
      · rw [← hgo]
        simp only [eval_signExtend]
        rw [BitVec.signExtend_eq_not_setWidth_not_of_msb_false]
        · simp only [denote_blastZeroExtend, ih, dite_eq_ite, Bool.if_false_right,
            BitVec.getLsbD_setWidth, hidx, decide_true, Bool.true_and, Bool.and_iff_right_iff_imp,
            decide_eq_true_eq]
          apply BitVec.lt_of_getLsbD
        · subst heq
          rw [BitVec.msb_zero_length]
      · simp [heq]
    | inr hlt =>
      rw [← hgo]
      rw [denote_blastSignExtend]
      simp only [eval_signExtend]
      rw [BitVec.getLsbD_signExtend]
      · simp only [hidx, decide_true, Bool.true_and]
        split
        · rw [ih]
        · rw [BitVec.msb_eq_getLsbD_last]
          rw [ih]
      · dsimp only; omega
  | @extract w start len inner ih =>
    simp only [go, denote_blastExtract, Bool.if_false_right, eval_extract,
      BitVec.getLsbD_extractLsb', hidx, decide_true, Bool.true_and]
    split
    · next hsplit =>
      rw [ih]
    · apply Eq.symm
      apply BitVec.getLsbD_ge
      omega
  | shiftLeft lhs rhs lih rih =>
    simp only [go, eval_shiftLeft]
    apply denote_blastShiftLeft
    · intros
      dsimp only
      rw [go_denote_mem_prefix]
      rw [← lih (aig := aig)]
      · simp
      · assumption
      · simp [Ref.hgate]
    · intros
      rw [← rih]
  | shiftRight lhs rhs lih rih =>
    simp only [go, eval_shiftRight]
    apply denote_blastShiftRight
    · intros
      dsimp only
      rw [go_denote_mem_prefix]
      rw [← lih (aig := aig)]
      · simp
      · assumption
      · simp [Ref.hgate]
    · intros
      rw [← rih]
  | arithShiftRight lhs rhs lih rih =>
    simp only [go, eval_arithShiftRight]
    apply denote_blastArithShiftRight
    · intros
      dsimp only
      rw [go_denote_mem_prefix]
      rw [← lih (aig := aig)]
      · simp
      · assumption
      · simp [Ref.hgate]
    · intros
      rw [← rih]
  | bin lhs op rhs lih rih =>
    cases op with
    | and =>
      simp only [go, RefVec.denote_zip, denote_mkAndCached, rih, eval_bin, BVBinOp.eval_and,
        BitVec.getLsbD_and]
      simp only [go_val_eq_bitblast, RefVec.get_cast]
      rw [AIG.LawfulVecOperator.denote_input_vec (f := bitblast)]
      rw [← go_val_eq_bitblast]
      rw [lih]
    | or =>
      simp only [go, RefVec.denote_zip, denote_mkOrCached, rih, eval_bin, BVBinOp.eval_or,
        BitVec.getLsbD_or]
      simp only [go_val_eq_bitblast, RefVec.get_cast]
      rw [AIG.LawfulVecOperator.denote_input_vec (f := bitblast)]
      rw [← go_val_eq_bitblast]
      rw [lih]
    | xor =>
      simp only [go, RefVec.denote_zip, denote_mkXorCached, rih, eval_bin, BVBinOp.eval_xor,
        BitVec.getLsbD_xor]
      simp only [go_val_eq_bitblast, RefVec.get_cast]
      rw [AIG.LawfulVecOperator.denote_input_vec (f := bitblast)]
      rw [← go_val_eq_bitblast]
      rw [lih]
    | add =>
      simp only [go, eval_bin, BVBinOp.eval_add]
      apply denote_blastAdd
      · intros
        dsimp only
        rw [go_denote_mem_prefix]
        rw [← lih (aig := aig)]
        · simp
        · assumption
        · simp [Ref.hgate]
      · intros
        rw [← rih]
    | mul =>
      simp only [go, eval_bin, BVBinOp.eval_mul]
      apply denote_blastMul
      · intros
        dsimp only
        rw [go_denote_mem_prefix]
        rw [← lih (aig := aig)]
        · simp
        · assumption
        · simp [Ref.hgate]
      · intros
        rw [← rih]
    | udiv =>
      simp only [go, eval_bin, BVBinOp.eval_udiv]
      apply denote_blastUdiv
      · intros
        dsimp only
        rw [go_denote_mem_prefix]
        rw [← lih (aig := aig)]
        · simp
        · assumption
        · simp [Ref.hgate]
      · intros
        rw [← rih]
    | umod =>
      simp only [go, eval_bin, BVBinOp.eval_umod]
      apply denote_blastUmod
      · intros
        dsimp only
        rw [go_denote_mem_prefix]
        rw [← lih (aig := aig)]
        · simp
        · assumption
        · simp [Ref.hgate]
      · intros
        rw [← rih]
  | un op expr ih =>
    cases op with
    | not => simp [go, ih, hidx]
    | shiftLeftConst => simp [go, ih, hidx]
    | shiftRightConst =>
      simp only [go, denote_blastShiftRightConst, ih, dite_eq_ite, Bool.if_false_right, eval_un,
        BVUnOp.eval_shiftRightConst, BitVec.getLsbD_ushiftRight, Bool.and_iff_right_iff_imp,
        decide_eq_true_eq]
      intro h
      apply BitVec.lt_of_getLsbD
      assumption
    | rotateLeft => simp [go, ih, hidx]
    | rotateRight => simp [go, ih, hidx]
    | arithShiftRightConst n =>
      rename_i w
      have : ¬(w ≤ idx) := by omega
      simp [go, ih, this, BitVec.getLsbD_sshiftRight, BitVec.msb_eq_getLsbD_last ]

end bitblast

@[simp]
theorem denote_bitblast (aig : AIG BVBit) (expr : BVExpr w) (assign : Assignment) :
    ∀ (idx : Nat) (hidx : idx < w),
        ⟦(bitblast aig expr).aig, (bitblast aig expr).vec.get idx hidx, assign.toAIGAssignment⟧
          =
        (expr.eval assign).getLsbD idx
    := by
  intros
  rw [← bitblast.go_val_eq_bitblast]
  rw [bitblast.go_denote_eq]

end BVExpr

end Std.Tactic.BVDecide
