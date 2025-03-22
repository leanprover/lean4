/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Pred

/-!
This module contains the logic to turn a `BVLogicalExpr` into an `AIG` with maximum subterm sharing,
through the use of a cache that re-uses sub-circuits if possible. Additionally a term level cache
is used to prevent rerunning bitblasting on commong bitvector subexpressions.
-/

namespace Std.Tactic.BVDecide

open Std.Sat Std.Sat.AIG

namespace BVLogicalExpr

/--
Turn a `BoolExpr` into an `Entrypoint`.
-/
def bitblast (expr : BVLogicalExpr) : Entrypoint BVBit :=
  go AIG.empty expr .empty |>.result.val
where
  go (aig : AIG BVBit) (expr : BVLogicalExpr) (cache : BVExpr.Cache aig) : Return aig :=
    match expr with
    | .literal var => BVPred.bitblast aig ⟨var, cache⟩
    | .const val =>
      have := LawfulOperator.le_size (f := mkConstCached) ..
      ⟨⟨aig.mkConstCached val, this⟩, cache.cast this⟩
    | .not expr =>
      let ⟨⟨⟨aig, exprRef⟩, hexpr⟩, cache⟩ := go aig expr cache
      let ret := aig.mkNotCached exprRef
      have := LawfulOperator.le_size (f := mkNotCached) ..
      let cache := cache.cast this
      have := by
        apply LawfulOperator.le_size_of_le_aig_size (f := mkNotCached)
        exact hexpr
      ⟨⟨ret, this⟩, cache⟩
    | .ite discr lhs rhs =>
      let ⟨⟨⟨aig, discrRef⟩, dextend⟩, cache⟩ := go aig discr cache
      let ⟨⟨⟨aig, lhsRef⟩, lextend⟩, cache⟩ := go aig lhs cache
      let ⟨⟨⟨aig, rhsRef⟩, rextend⟩, cache⟩ := go aig rhs cache
      let discrRef := discrRef.cast <| by
        dsimp only at lextend rextend ⊢
        omega
      let lhsRef := lhsRef.cast <| by
        dsimp only at rextend ⊢
        omega

      let input := ⟨discrRef, lhsRef, rhsRef⟩
      let ret := aig.mkIfCached input
      have := LawfulOperator.le_size (f := mkIfCached) ..
      let cache := cache.cast this
      have := by
        apply LawfulOperator.le_size_of_le_aig_size (f := mkIfCached)
        dsimp only at dextend lextend rextend
        omega
      ⟨⟨ret, this⟩, cache⟩
    | .gate g lhs rhs =>
      let ⟨⟨⟨aig, lhsRef⟩, lextend⟩, cache⟩ := go aig lhs cache
      let ⟨⟨⟨aig, rhsRef⟩, rextend⟩, cache⟩ := go aig rhs cache
      let lhsRef := lhsRef.cast <| by
        dsimp only at rextend ⊢
        omega
      let input := ⟨lhsRef, rhsRef⟩
      match g with
      | .and =>
        let ret := aig.mkAndCached input
        have := LawfulOperator.le_size (f := mkAndCached) ..
        let cache := cache.cast this
        have := by
          apply LawfulOperator.le_size_of_le_aig_size (f := mkAndCached)
          dsimp only at lextend rextend
          omega
        ⟨⟨ret, this⟩, cache⟩
      | .xor =>
        let ret := aig.mkXorCached input
        have := LawfulOperator.le_size (f := mkXorCached) ..
        let cache := cache.cast this
        have := by
          apply LawfulOperator.le_size_of_le_aig_size (f := mkXorCached)
          dsimp only at lextend rextend
          omega
        ⟨⟨ret, this⟩, cache⟩
      | .beq =>
        let ret := aig.mkBEqCached input
        have := LawfulOperator.le_size (f := mkBEqCached) ..
        let cache := cache.cast this
        have := by
          apply LawfulOperator.le_size_of_le_aig_size (f := mkBEqCached)
          dsimp only at lextend rextend
          omega
        ⟨⟨ret, this⟩, cache⟩
      | .or =>
        let ret := aig.mkOrCached input
        have := LawfulOperator.le_size (f := mkOrCached) ..
        let cache := cache.cast this
        have := by
          apply LawfulOperator.le_size_of_le_aig_size (f := mkOrCached)
          dsimp only at lextend rextend
          omega
        ⟨⟨ret, this⟩, cache⟩

namespace bitblast

theorem go_le_size (aig : AIG BVBit) (expr : BVLogicalExpr) (cache : BVExpr.Cache aig) :
    aig.decls.size ≤ (go aig expr cache).result.val.aig.decls.size :=
  (go aig expr cache).result.property

theorem go_lt_size_of_lt_aig_size (aig : AIG BVBit) (expr : BVLogicalExpr)
    (cache : BVExpr.Cache aig) (h : x < aig.decls.size) :
    x < (go aig expr cache).result.val.aig.decls.size := by
  apply Nat.lt_of_lt_of_le
  · exact h
  · apply go_le_size

theorem go_decl_eq (idx) (aig : AIG BVBit) (cache : BVExpr.Cache aig) (h : idx < aig.decls.size) (hbounds) :
    (go aig expr cache).result.val.aig.decls[idx]'hbounds = aig.decls[idx] := by
  induction expr generalizing aig with
  | const =>
    simp only [go]
    rw [AIG.LawfulOperator.decl_eq (f := mkConstCached)]
  | literal =>
    simp only [go]
    rw [BVPred.bitblast_decl_eq]
  | not expr ih =>
    simp only [go]
    have := go_le_size aig expr cache
    specialize ih aig cache (by omega) (by omega)
    rw [AIG.LawfulOperator.decl_eq (f := mkNotCached)]
    assumption
  | ite discr lhs rhs dih lih rih =>
    simp only [go]
    rw [AIG.LawfulOperator.decl_eq (f := mkIfCached), rih, lih, dih]
    · apply go_lt_size_of_lt_aig_size
      assumption
    · apply go_lt_size_of_lt_aig_size
      apply go_lt_size_of_lt_aig_size
      assumption
    · apply go_lt_size_of_lt_aig_size
      apply go_lt_size_of_lt_aig_size
      apply go_lt_size_of_lt_aig_size
      assumption
  | gate g lhs rhs lih rih =>
    cases g with
    | and =>
      simp only [go]
      rw [AIG.LawfulOperator.decl_eq (f := mkAndCached), rih, lih]
      · apply go_lt_size_of_lt_aig_size
        assumption
      · apply go_lt_size_of_lt_aig_size
        apply go_lt_size_of_lt_aig_size
        assumption
    | xor =>
      simp only [go]
      rw [AIG.LawfulOperator.decl_eq (f := mkXorCached), rih, lih]
      · apply go_lt_size_of_lt_aig_size
        assumption
      · apply go_lt_size_of_lt_aig_size
        apply go_lt_size_of_lt_aig_size
        assumption
    | beq =>
      simp only [go]
      rw [AIG.LawfulOperator.decl_eq (f := mkBEqCached), rih, lih]
      · apply go_lt_size_of_lt_aig_size
        assumption
      · apply go_lt_size_of_lt_aig_size
        apply go_lt_size_of_lt_aig_size
        assumption
    | or =>
      simp only [go]
      rw [AIG.LawfulOperator.decl_eq (f := mkOrCached), rih, lih]
      · apply go_lt_size_of_lt_aig_size
        assumption
      · apply go_lt_size_of_lt_aig_size
        apply go_lt_size_of_lt_aig_size
        assumption

theorem go_isPrefix_aig {aig : AIG BVBit} (cache : BVExpr.Cache aig) :
    IsPrefix aig.decls (go aig expr cache).result.val.aig.decls := by
  apply IsPrefix.of
  · intro idx h
    apply go_decl_eq
  · apply go_le_size

theorem go_denote_mem_prefix (aig : AIG BVBit) (cache : BVExpr.Cache aig) (hstart) :
    ⟦
      (go aig expr cache).result.val.aig,
      ⟨start, inv, go_lt_size_of_lt_aig_size (h := hstart) ..⟩,
      assign
    ⟧
      =
    ⟦aig, ⟨start, inv, hstart⟩, assign⟧ := by
  apply denote.eq_of_isPrefix (entry := ⟨aig, start, inv, hstart⟩)
  apply go_isPrefix_aig

end bitblast
end BVLogicalExpr

end Std.Tactic.BVDecide
