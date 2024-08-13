/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Lean.Elab.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Eq
import Lean.Elab.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Ult
import Lean.Elab.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.GetLsb
import Lean.Elab.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Expr
import Lean.Elab.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Pred

/-!
This module contains the verification of the bitblaster for predicates over `BitVec` expressions
(`BVPred`) from `Impl.Pred`.
-/

namespace Lean.Elab.Tactic.BVDecide

open Std.Sat
open Std.Sat.AIG

namespace BVPred

@[simp]
theorem bitblast_denote_eq (aig : AIG BVBit) (pred : BVPred) (assign : BVExpr.Assignment) :
    ⟦bitblast aig pred, assign.toAIGAssignment⟧ = pred.eval assign := by
  cases pred with
  | bin lhs op rhs =>
    cases op with
    | eq =>
      simp only [bitblast, eval_bin, BVBinPred.eval_eq]
      rw [mkEq_denote_eq]
      . intros
        rw [AIG.LawfulVecOperator.denote_mem_prefix (f := BVExpr.bitblast)]
        . simp
          rw [BVExpr.bitblast_denote_eq]
        . simp [Ref.hgate]
      . intros
        simp
    | ult =>
      simp only [bitblast, eval_bin, BVBinPred.eval_ult]
      rw [mkUlt_denote_eq]
      . intros
        rw [AIG.LawfulVecOperator.denote_mem_prefix (f := BVExpr.bitblast)]
        . simp
          rw [BVExpr.bitblast_denote_eq]
        . simp [Ref.hgate]
      . intros
        simp
  | getLsb expr idx =>
    simp only [bitblast, blastGetLsb_denote_eq, BVExpr.bitblast_denote_eq, dite_eq_ite,
      Bool.if_false_right, eval_getLsb, Bool.and_iff_right_iff_imp, decide_eq_true_eq]
    apply BitVec.lt_of_getLsb

end BVPred

end Lean.Elab.Tactic.BVDecide
