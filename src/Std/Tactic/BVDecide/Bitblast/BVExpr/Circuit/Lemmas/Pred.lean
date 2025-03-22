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

@[simp]
theorem denote_bitblast (aig : AIG BVBit) (pred : BVPred) (assign : BVExpr.Assignment) :
    ⟦bitblast aig pred, assign.toAIGAssignment⟧ = pred.eval assign := by
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
          apply BVExpr.Cache.Inv_empty
        · simp [Ref.hgate]
      · intros
        rw [BVExpr.denote_bitblast]
        apply BVExpr.bitblast_Inv_of_Inv
        apply BVExpr.Cache.Inv_empty
    | ult =>
      simp only [bitblast, eval_bin, BVBinPred.eval_ult]
      rw [mkUlt_denote_eq]
      · intros
        rw [BVExpr.bitblast_denote_mem_prefix]
        · simp only [RefVec.get_cast, Ref.cast_eq]
          rw [BVExpr.denote_bitblast]
          apply BVExpr.Cache.Inv_empty
        · simp [Ref.hgate]
      · intros
        rw [BVExpr.denote_bitblast]
        apply BVExpr.bitblast_Inv_of_Inv
        apply BVExpr.Cache.Inv_empty
  | getLsbD expr idx =>
    simp only [bitblast, denote_blastGetLsbD, eval_getLsbD]
    split
    · rw [BVExpr.denote_bitblast]
      apply BVExpr.Cache.Inv_empty
    · symm
      apply BitVec.getLsbD_ge
      omega

end BVPred

end Std.Tactic.BVDecide
