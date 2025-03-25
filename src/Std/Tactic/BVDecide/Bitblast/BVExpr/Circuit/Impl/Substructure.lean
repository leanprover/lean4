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

structure Cache (aig : AIG BVBit) where
  map : Std.HashMap BVLogicalExpr (Nat × Bool)
  hbound : ∀ k (h : k ∈ map), (map.get k h).1 < aig.decls.size

@[inline]
def Cache.empty : Cache aig :=
  ⟨{}, by simp⟩

@[inline]
def Cache.insert (cache : Cache aig) (expr : BVLogicalExpr) (ref : AIG.Ref aig) :
    Cache aig :=
  let ⟨map, hbound⟩ := cache
  have := by sorry
  ⟨map.insert expr ⟨ref.gate, ref.invert⟩, this⟩

@[inline]
def Cache.get? (cache : Cache aig) (expr : BVLogicalExpr) : Option (AIG.Ref aig) :=
  match h : cache.map.get? expr with
  | some ref =>
    some ⟨ref.1, ref.2, sorry⟩
  | none =>
    none

@[inline]
def Cache.cast (cache : Cache aig1) (h : aig1.decls.size ≤ aig2.decls.size) :
    Cache aig2 :=
  let ⟨map, hbound⟩ := cache
  have := by sorry
  ⟨map, this⟩

structure Return (aig : AIG BVBit) where
  result : AIG.ExtendingEntrypoint aig
  bvCache : BVExpr.Cache result.val.aig
  logCache : Cache result.val.aig

/--
Turn a `BVLogicalExpr` into an `Entrypoint`.
-/
def bitblast (expr : BVLogicalExpr) : Entrypoint BVBit :=
  goCache AIG.empty expr .empty .empty |>.result.val
where
  goCache (aig : AIG BVBit) (expr : BVLogicalExpr) (bvCache : BVExpr.Cache aig)
      (logCache : Cache aig) : Return aig :=
    match logCache.get? expr with
    | some ref => ⟨⟨⟨aig, ref⟩, Nat.le_refl ..⟩, bvCache, logCache⟩
    | none =>
      let ⟨result, bvCache, logCache⟩ := go aig expr bvCache logCache
      ⟨result, bvCache, logCache.insert expr result.val.ref⟩
    termination_by (sizeOf expr, 1)

  go (aig : AIG BVBit) (expr : BVLogicalExpr) (bvCache : BVExpr.Cache aig) (logCache : Cache aig) :
      Return aig :=
    match expr with
    | .atom pred =>
      let ⟨result, bvCache⟩ := BVPred.bitblast aig ⟨pred, bvCache⟩
      ⟨result, bvCache, logCache.cast result.property⟩
    | .const val =>
      have := LawfulOperator.le_size (f := mkConstCached) ..
      ⟨⟨aig.mkConstCached val, this⟩, bvCache.cast this, logCache.cast this⟩
    | .not expr =>
      let ⟨⟨⟨aig, exprRef⟩, hexpr⟩, bvCache, logCache⟩ := goCache aig expr bvCache logCache
      let ret := aig.mkNotCached exprRef
      have := LawfulOperator.le_size (f := mkNotCached) ..
      let bvCache := bvCache.cast this
      let logCache := logCache.cast this
      have := by
        apply LawfulOperator.le_size_of_le_aig_size (f := mkNotCached)
        exact hexpr
      ⟨⟨ret, this⟩, bvCache, logCache⟩
    | .ite discr lhs rhs =>
      let ⟨⟨⟨aig, discrRef⟩, dextend⟩, bvCache, logCache⟩ := goCache aig discr bvCache logCache
      let ⟨⟨⟨aig, lhsRef⟩, lextend⟩, bvCache, logCache⟩ := goCache aig lhs bvCache logCache
      let ⟨⟨⟨aig, rhsRef⟩, rextend⟩, bvCache, logCache⟩ := goCache aig rhs bvCache logCache
      let discrRef := discrRef.cast <| by
        dsimp only at lextend rextend ⊢
        omega
      let lhsRef := lhsRef.cast <| by
        dsimp only at rextend ⊢
        omega

      let input := ⟨discrRef, lhsRef, rhsRef⟩
      let ret := aig.mkIfCached input
      have := LawfulOperator.le_size (f := mkIfCached) ..
      let bvCache := bvCache.cast this
      let logCache := logCache.cast this
      have := by
        apply LawfulOperator.le_size_of_le_aig_size (f := mkIfCached)
        dsimp only at dextend lextend rextend
        omega
      ⟨⟨ret, this⟩, bvCache, logCache⟩
    | .gate g lhs rhs =>
      let ⟨⟨⟨aig, lhsRef⟩, lextend⟩, bvCache, logCache⟩ := goCache aig lhs bvCache logCache
      let ⟨⟨⟨aig, rhsRef⟩, rextend⟩, bvCache, logCache⟩ := goCache aig rhs bvCache logCache
      let lhsRef := lhsRef.cast <| by
        dsimp only at rextend ⊢
        omega
      let input := ⟨lhsRef, rhsRef⟩
      match g with
      | .and =>
        let ret := aig.mkAndCached input
        have := LawfulOperator.le_size (f := mkAndCached) ..
        let bvCache := bvCache.cast this
        let logCache := logCache.cast this
        have := by
          apply LawfulOperator.le_size_of_le_aig_size (f := mkAndCached)
          dsimp only at lextend rextend
          omega
        ⟨⟨ret, this⟩, bvCache, logCache⟩
      | .xor =>
        let ret := aig.mkXorCached input
        have := LawfulOperator.le_size (f := mkXorCached) ..
        let bvCache := bvCache.cast this
        let logCache := logCache.cast this
        have := by
          apply LawfulOperator.le_size_of_le_aig_size (f := mkXorCached)
          dsimp only at lextend rextend
          omega
        ⟨⟨ret, this⟩, bvCache, logCache⟩
      | .beq =>
        let ret := aig.mkBEqCached input
        have := LawfulOperator.le_size (f := mkBEqCached) ..
        let bvCache := bvCache.cast this
        let logCache := logCache.cast this
        have := by
          apply LawfulOperator.le_size_of_le_aig_size (f := mkBEqCached)
          dsimp only at lextend rextend
          omega
        ⟨⟨ret, this⟩, bvCache, logCache⟩
      | .or =>
        let ret := aig.mkOrCached input
        have := LawfulOperator.le_size (f := mkOrCached) ..
        let bvCache := bvCache.cast this
        let logCache := logCache.cast this
        have := by
          apply LawfulOperator.le_size_of_le_aig_size (f := mkOrCached)
          dsimp only at lextend rextend
          omega
        ⟨⟨ret, this⟩, bvCache, logCache⟩
    termination_by (sizeOf expr, 0)

namespace bitblast

theorem goCache_le_size (aig : AIG BVBit) (expr : BVLogicalExpr) (bvCache : BVExpr.Cache aig)
    (logCache : Cache aig) :
    aig.decls.size ≤ (goCache aig expr bvCache logCache).result.val.aig.decls.size :=
  (goCache aig expr bvCache logCache).result.property

theorem go_le_size (aig : AIG BVBit) (expr : BVLogicalExpr) (bvCache : BVExpr.Cache aig)
    (logCache : Cache aig) :
    aig.decls.size ≤ (go aig expr bvCache logCache).result.val.aig.decls.size :=
  (go aig expr bvCache logCache).result.property

theorem go_lt_size_of_lt_aig_size (aig : AIG BVBit) (expr : BVLogicalExpr)
    (bvCache : BVExpr.Cache aig) (logCache : Cache aig) (h : x < aig.decls.size) :
    x < (go aig expr bvCache logCache).result.val.aig.decls.size := by
  apply Nat.lt_of_lt_of_le
  · exact h
  · apply go_le_size

mutual

theorem goCache_decl_eq (idx) (aig : AIG BVBit) (bvCache : BVExpr.Cache aig)
    (logCache : Cache aig) (h : idx < aig.decls.size) (hbounds) :
    (goCache aig expr bvCache logCache).result.val.aig.decls[idx]'hbounds = aig.decls[idx] := by
  sorry

theorem go_decl_eq (idx) (aig : AIG BVBit) (bvCache : BVExpr.Cache aig)
    (logCache : Cache aig) (h : idx < aig.decls.size) (hbounds) :
    (go aig expr bvCache logCache).result.val.aig.decls[idx]'hbounds = aig.decls[idx] := by
  sorry
  /-
  induction expr generalizing aig with
  | const =>
    simp only [go]
    rw [AIG.LawfulOperator.decl_eq (f := mkConstCached)]
  | atom =>
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
        assumption -/

end

theorem goCache_isPrefix_aig {aig : AIG BVBit} (bvCache : BVExpr.Cache aig)
    (logCache : Cache aig) :
    IsPrefix aig.decls (goCache aig expr bvCache logCache).result.val.aig.decls := by
  apply IsPrefix.of
  · intro idx h
    apply goCache_decl_eq
  · apply goCache_le_size

theorem go_isPrefix_aig {aig : AIG BVBit} (bvCache : BVExpr.Cache aig)
    (logCache : Cache aig) :
    IsPrefix aig.decls (go aig expr bvCache logCache).result.val.aig.decls := by
  apply IsPrefix.of
  · intro idx h
    apply go_decl_eq
  · apply go_le_size

theorem go_denote_mem_prefix (aig : AIG BVBit) (bvCache : BVExpr.Cache aig) (logCache : Cache aig)
    (hstart) :
    ⟦
      (go aig expr bvCache logCache).result.val.aig,
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
