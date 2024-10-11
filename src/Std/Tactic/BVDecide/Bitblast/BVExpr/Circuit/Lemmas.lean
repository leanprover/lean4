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

theorem go_eval_eq_eval (expr : BVLogicalExpr) (aig : AIG BVBit) (assign : BVExpr.Assignment) :
    ⟦go aig expr, assign.toAIGAssignment⟧ = expr.eval assign := by
  induction expr generalizing aig with
  | const => simp [go]
  | literal => simp [go]
  | not expr ih => simp [go, ih]
  | gate g lhs rhs lih rih => cases g <;> simp [go, Gate.eval, lih, rih]

end bitblast

theorem denote_bitblast (expr : BVLogicalExpr) (assign : BVExpr.Assignment) :
    ⟦bitblast expr, assign.toAIGAssignment⟧ = expr.eval assign := by
  unfold bitblast
  rw [bitblast.go_eval_eq_eval]

theorem unsat_of_bitblast (expr : BVLogicalExpr) : expr.bitblast.Unsat → expr.Unsat :=  by
  intro h assign
  rw [← denote_bitblast]
  apply h

end BVLogicalExpr

end Std.Tactic.BVDecide
