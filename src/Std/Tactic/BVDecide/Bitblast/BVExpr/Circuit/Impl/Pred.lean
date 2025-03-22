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

structure Return (aig : AIG BVBit) where
  result : AIG.ExtendingEntrypoint aig
  cache : BVExpr.Cache result.val.aig

namespace BVPred

def bitblast (aig : AIG BVBit) (input : BVExpr.WithCache BVPred aig) : Return aig :=
  let ⟨pred, cache⟩ := input
  match pred with
  | .bin lhs op rhs =>
    let ⟨⟨⟨aig, lhsRefs⟩, hlhs⟩, cache⟩ := BVExpr.bitblast aig ⟨lhs, cache⟩
    let ⟨⟨⟨aig, rhsRefs⟩, hrhs⟩, cache⟩ := BVExpr.bitblast aig ⟨rhs, cache⟩
    let lhsRefs := lhsRefs.cast hrhs
    match op with
    | .eq =>
      let res := mkEq aig ⟨lhsRefs, rhsRefs⟩
      let cache := cache.cast (AIG.LawfulOperator.le_size (f := mkEq) ..)
      have := by
        apply AIG.LawfulOperator.le_size_of_le_aig_size (f := mkEq)
        dsimp only at hlhs hrhs
        omega
      ⟨⟨res, this⟩, cache⟩
    | .ult =>
      let res := mkUlt aig ⟨lhsRefs, rhsRefs⟩
      have := AIG.LawfulOperator.le_size (f := mkUlt) ..
      let cache := cache.cast this
      have := by
        apply AIG.LawfulOperator.le_size_of_le_aig_size (f := mkUlt)
        dsimp only at hlhs hrhs
        omega
      ⟨⟨res, this⟩, cache⟩
  | .getLsbD expr idx =>
    /-
    Note: This blasts the entire expression up to `w` despite only needing it up to `idx`.
    However the vast majority of operations are interested in all bits so the API is currently
    not designed to support this use case.
    -/
    let ⟨⟨⟨aig, refs⟩, hrefs⟩, cache⟩ := BVExpr.bitblast aig ⟨expr, cache⟩
    let res := blastGetLsbD aig ⟨refs, idx⟩
    let cache := cache.cast (AIG.LawfulOperator.le_size (f := blastGetLsbD) ..)
    have := by
      apply AIG.LawfulOperator.le_size_of_le_aig_size (f := blastGetLsbD)
      exact hrefs
    ⟨⟨res, this⟩, cache⟩

theorem bitblast_decl_eq (aig : AIG BVBit) (input : BVExpr.WithCache BVPred aig) :
    ∀ (idx : Nat) (h1) (h2), (bitblast aig input).result.val.aig.decls[idx]'h2 = aig.decls[idx]'h1 := by
  intro idx h1 h2
  rcases input with ⟨pred, cache⟩
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

theorem bitblast_le_size (aig : AIG BVBit) (input : BVExpr.WithCache BVPred aig) :
    aig.decls.size ≤ (bitblast aig input).result.val.aig.decls.size := by
  exact (bitblast aig input).result.property

end BVPred

end Std.Tactic.BVDecide
