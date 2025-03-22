/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Eq
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Ult
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.GetLsbD
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Expr

/-!
This module contains the implementation of a bitblaster for predicates over `BitVec` expressions
(`BVPred`).
-/

namespace Std.Tactic.BVDecide

open Std.Sat

namespace BVPred

def bitblast (aig : AIG BVBit) (pred : BVPred) : AIG.Entrypoint BVBit :=
  let cache := BVExpr.Cache.empty
  match pred with
  | .bin lhs op rhs =>
    let ⟨⟨⟨aig, lhsRefs⟩, _⟩, cache⟩ := BVExpr.bitblast aig ⟨lhs, cache⟩
    let ⟨⟨⟨aig, rhsRefs⟩, hrhs⟩, _⟩ := BVExpr.bitblast aig ⟨rhs, cache⟩
    let lhsRefs := lhsRefs.cast hrhs
    match op with
    | .eq => mkEq aig ⟨lhsRefs, rhsRefs⟩
    | .ult => mkUlt aig ⟨lhsRefs, rhsRefs⟩
  | .getLsbD expr idx =>
    /-
    Note: This blasts the entire expression up to `w` despite only needing it up to `idx`.
    However the vast majority of operations are interested in all bits so the API is currently
    not designed to support this use case.
    -/
    let ⟨⟨⟨aig, refs⟩, _⟩, _⟩ := BVExpr.bitblast aig ⟨expr, cache⟩
    blastGetLsbD aig ⟨refs, idx⟩

instance : AIG.LawfulOperator BVBit (fun _ => BVPred) bitblast where
  le_size := by
    intro aig pred
    unfold BVPred.bitblast
    cases pred with
    | bin lhs op rhs =>
      cases op with
      | eq =>
        dsimp only
        apply AIG.LawfulOperator.le_size_of_le_aig_size (f := mkEq)
        refine Nat.le_trans ?_ (BVExpr.bitblast_le_size ..)
        apply BVExpr.bitblast_le_size
      | ult =>
        dsimp only
        apply AIG.LawfulOperator.le_size_of_le_aig_size (f := mkUlt)
        refine Nat.le_trans ?_ (BVExpr.bitblast_le_size ..)
        apply BVExpr.bitblast_le_size
    | getLsbD expr idx =>
      dsimp only
      apply AIG.LawfulOperator.le_size_of_le_aig_size (f := blastGetLsbD)
      apply BVExpr.bitblast_le_size
  decl_eq := by
    intro aig pred idx h1 h2
    unfold BVPred.bitblast
    cases pred with
    | bin lhs op rhs =>
      cases op with
      | eq =>
        dsimp only
        rw [AIG.LawfulOperator.decl_eq (f := mkEq)]
        rw [BVExpr.bitblast_decl_eq]
        rw [BVExpr.bitblast_decl_eq]
        · apply BVExpr.bitblast_lt_size_of_lt_aig_size
          assumption
        · apply BVExpr.bitblast_lt_size_of_lt_aig_size
          apply BVExpr.bitblast_lt_size_of_lt_aig_size
          assumption
      | ult =>
        simp only [bitblast]
        rw [AIG.LawfulOperator.decl_eq (f := mkUlt)]
        rw [BVExpr.bitblast_decl_eq]
        rw [BVExpr.bitblast_decl_eq]
        · apply BVExpr.bitblast_lt_size_of_lt_aig_size
          assumption
        · apply BVExpr.bitblast_lt_size_of_lt_aig_size
          apply BVExpr.bitblast_lt_size_of_lt_aig_size
          assumption
    | getLsbD expr idx =>
      simp only [bitblast]
      rw [AIG.LawfulOperator.decl_eq (f := blastGetLsbD)]
      rw [BVExpr.bitblast_decl_eq]
      apply BVExpr.bitblast_lt_size_of_lt_aig_size
      assumption

end BVPred

end Std.Tactic.BVDecide
