/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Eq
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Ult
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.GetLsbD
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Expr
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Pred

/-!
This module contains the verification of the bitblaster for predicates over `BitVec` expressions
(`BVPred`) from `Impl.Pred`.
-/

namespace Std.Tactic.BVDecide

open Std.Sat
open Std.Sat.AIG

namespace BVPred

theorem bitblast_aig_IsPrefix (aig : AIG BVBit) (input : BVExpr.WithCache BVPred aig) :
    IsPrefix aig.decls (bitblast aig input).result.val.aig.decls := by
  apply IsPrefix.of
  · intros
    apply bitblast_decl_eq
  · intros
    apply (bitblast aig input).result.property

theorem bitblast_denote_mem_prefix (aig : AIG BVBit) (input : BVExpr.WithCache BVPred aig)
    (assign : BVExpr.Assignment) (start : Nat) (hstart) :
    ⟦
      (bitblast aig input).result.val.aig,
      ⟨start, inv, by apply Nat.lt_of_lt_of_le; exact hstart; apply (bitblast aig input).result.property⟩,
      assign.toAIGAssignment
    ⟧
      =
    ⟦aig, ⟨start, inv, hstart⟩, assign.toAIGAssignment⟧ := by
  apply denote.eq_of_isPrefix (entry := ⟨aig, start, inv, hstart⟩)
  apply bitblast_aig_IsPrefix

theorem bitblast_Inv_of_Inv (input : BVExpr.WithCache BVPred aig)
    (hinv : BVExpr.Cache.Inv assign aig input.cache) :
    BVExpr.Cache.Inv assign (bitblast aig input).result.val.aig (bitblast aig input).cache := by
  unfold bitblast
  dsimp only
  split
  · next op _ _ =>
    cases op
    · dsimp only
      apply BVExpr.Cache.Inv_cast
      · apply AIG.LawfulOperator.isPrefix_aig (f := mkEq)
      · apply BVExpr.bitblast_Inv_of_Inv
        apply BVExpr.bitblast_Inv_of_Inv
        exact hinv
    · dsimp only
      apply BVExpr.Cache.Inv_cast
      · apply AIG.LawfulOperator.isPrefix_aig (f := mkUlt)
      · apply BVExpr.bitblast_Inv_of_Inv
        apply BVExpr.bitblast_Inv_of_Inv
        exact hinv
  · dsimp only
    apply BVExpr.Cache.Inv_cast
    · apply AIG.LawfulOperator.isPrefix_aig (f := blastGetLsbD)
    · apply BVExpr.bitblast_Inv_of_Inv
      exact hinv

theorem denote_bitblast (aig : AIG BVBit) (input : BVExpr.WithCache BVPred aig)
    (assign : BVExpr.Assignment) (hinv : BVExpr.Cache.Inv assign aig input.cache ) :
    ⟦(bitblast aig input).result.val.aig, (bitblast aig input).result.val.ref, assign.toAIGAssignment⟧
      =
    input.val.eval assign := by
  rcases input with ⟨pred, cache⟩
  cases pred with
  | bin lhs op rhs =>
    cases op with
    | eq =>
      simp only [bitblast, eval_bin, BVBinPred.eval_eq]
      rw [mkEq_denote_eq]
      · intros
        rw [BVExpr.bitblast_denote_mem_prefix]
        · simp only [RefVec.get_cast, Ref.cast_eq]
          rw [BVExpr.denote_bitblast]
          exact hinv
        · simp [Ref.hgate]
      · intros
        rw [BVExpr.denote_bitblast]
        apply BVExpr.bitblast_Inv_of_Inv
        exact hinv
    | ult =>
      simp only [bitblast, eval_bin, BVBinPred.eval_ult]
      rw [mkUlt_denote_eq]
      · intros
        rw [BVExpr.bitblast_denote_mem_prefix]
        · simp only [RefVec.get_cast, Ref.cast_eq]
          rw [BVExpr.denote_bitblast]
          exact hinv
        · simp [Ref.hgate]
      · intros
        rw [BVExpr.denote_bitblast]
        apply BVExpr.bitblast_Inv_of_Inv
        exact hinv
  | getLsbD expr idx =>
    simp only [bitblast, denote_projected_entry, denote_blastGetLsbD, eval_getLsbD]
    split
    · rw [BVExpr.denote_bitblast]
      exact hinv
    · symm
      apply BitVec.getLsbD_ge
      omega

end BVPred

end Std.Tactic.BVDecide
