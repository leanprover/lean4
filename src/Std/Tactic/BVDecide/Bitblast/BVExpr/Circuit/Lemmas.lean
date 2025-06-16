/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Pred

/-!
This module contains the verification of the bitblaster for general `BitVec` problems with boolean
substructure (`BVLogicalExpr`). It is the main entrypoint for verification of the bitblasting
framework.
-/

namespace Std.Tactic.BVDecide

open Std.Sat
open Std.Sat.AIG

namespace BVLogicalExpr

namespace bitblast

mutual

theorem go_Inv_of_Inv (expr : BVLogicalExpr) (aig : AIG BVBit) (assign : BVExpr.Assignment)
    (cache : BVExpr.Cache aig) (hinv : BVExpr.Cache.Inv assign aig cache) :
    BVExpr.Cache.Inv assign (go aig expr cache).result.val.aig (go aig expr cache).cache := by
  induction expr generalizing aig with
  | const =>
    simp only [go]
    apply BVExpr.Cache.Inv_cast
    apply LawfulOperator.isPrefix_aig (f := mkConstCached)
    exact hinv
  | literal =>
    simp only [go]
    apply BVPred.bitblast_Inv_of_Inv
    exact hinv
  | not expr ih =>
    simp only [go]
    apply BVExpr.Cache.Inv_cast
    · apply LawfulOperator.isPrefix_aig (f := mkNotCached)
    · apply ih
      exact hinv
  | gate g lhs rhs lih rih =>
    cases g
    all_goals
      simp [go, Gate.eval]
      apply BVExpr.Cache.Inv_cast
      · apply LawfulOperator.isPrefix_aig
      · apply rih
        apply lih
        exact hinv
  | ite discr lhs rhs dih lih rih =>
    simp only [go]
    apply BVExpr.Cache.Inv_cast
    · apply LawfulOperator.isPrefix_aig (f := mkIfCached)
    · apply rih
      apply lih
      apply dih
      exact hinv

theorem go_eval_eq_eval (expr : BVLogicalExpr) (aig : AIG BVBit) (assign : BVExpr.Assignment)
    (cache : BVExpr.Cache aig) (hinv : BVExpr.Cache.Inv assign aig cache) :
    ⟦(go aig expr cache).result, assign.toAIGAssignment⟧ = expr.eval assign := by
  induction expr generalizing aig with
  | const => simp [go]
  | literal =>
    simp only [go, eval_literal]
    rw [BVPred.denote_bitblast]
    exact hinv
  | not expr ih =>
    specialize ih _ _ hinv
    simp [go, ih]
  | gate g lhs rhs lih rih =>
    cases g
    all_goals
      simp [go, Gate.eval]
      congr 1
      · rw [go_denote_mem_prefix]
        apply lih
        exact hinv
      · apply rih
        apply go_Inv_of_Inv
        exact hinv
  | ite discr lhs rhs dih lih rih =>
    simp only [go, Ref.cast_eq, denote_mkIfCached, denote_projected_entry,
      eval_ite, Bool.ite_eq_cond_iff]
    apply ite_congr
    · rw [go_denote_mem_prefix]
      rw [go_denote_mem_prefix]
      · specialize dih _ _ hinv
        simp [dih]
      · simp [Ref.hgate]
    · intro h
      rw [go_denote_mem_prefix]
      apply lih
      apply go_Inv_of_Inv
      exact hinv
    · intro h
      apply rih
      apply go_Inv_of_Inv
      apply go_Inv_of_Inv
      exact hinv

end

end bitblast

theorem denote_bitblast (expr : BVLogicalExpr) (assign : BVExpr.Assignment) :
    ⟦bitblast expr, assign.toAIGAssignment⟧ = expr.eval assign := by
  unfold bitblast
  rw [bitblast.go_eval_eq_eval]
  apply BVExpr.Cache.Inv_empty

theorem unsat_of_bitblast (expr : BVLogicalExpr) : expr.bitblast.Unsat → expr.Unsat :=  by
  intro h assign
  rw [← denote_bitblast]
  apply h

end BVLogicalExpr

end Std.Tactic.BVDecide
