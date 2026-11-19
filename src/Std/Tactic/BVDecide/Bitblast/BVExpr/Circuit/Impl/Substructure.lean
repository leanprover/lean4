/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Pred
import Init.Omega

@[expose] public section

/-!
This module contains the logic to turn a `BVLogicalExpr` into an `AIG` with maximum subterm sharing,
through the use of a cache that re-uses sub-circuits if possible. Additionally a term level cache
is used to prevent rerunning bitblasting on common bitvector subexpressions.
-/

namespace Std.Tactic.BVDecide

open Std.Sat Std.Sat.AIG

namespace BVLogicalExpr

structure Cache (aig : AIG BVBit) where
  exprs : BVExpr.Cache aig
  map : Std.HashMap BVLogicalExpr AIG.Fanin
  hbound : ∀ k (h : k ∈ map), (map[k]'h).gate < aig.decls.size

@[inline]
def Cache.empty : Cache aig :=
  ⟨.empty, {}, by simp⟩

@[inline]
def Cache.insert (cache : Cache aig) (expr : BVLogicalExpr) (ref : AIG.Ref aig) : Cache aig :=
  let ⟨exprs, map, hbound⟩ := cache
  have := by
    intro k hk
    rw [Std.HashMap.getElem_insert]
    split
    next heq =>
      simp only [beq_iff_eq] at heq
      subst heq
      simp [ref.hgate]
    · apply hbound
  ⟨exprs, map.insert expr (.mk ref.gate ref.invert), this⟩

@[inline]
def Cache.get? (cache : Cache aig) (expr : BVLogicalExpr) : Option (AIG.Ref aig) :=
  match h : cache.map[expr]? with
  | some ref =>
    have : expr ∈ cache.map := by
      rw [Std.HashMap.mem_iff_contains, Std.HashMap.contains_eq_isSome_getElem?]
      simp [h]
    have : cache.map[expr]'this = ref := by
      rw [Std.HashMap.getElem?_eq_some_getElem (h' := this)] at h
      simpa using h
    have := by
      rw [← this]
      apply cache.hbound
    some ⟨ref.gate, ref.invert, this⟩
  | none => none

@[inline]
def Cache.cast (cache : Cache aig1) (h : aig1.decls.size ≤ aig2.decls.size) : Cache aig2 :=
  let ⟨exprs, map, hbound⟩ := cache
  have := by
    intro k hk
    apply Nat.lt_of_lt_of_le
    · apply hbound
    · exact h
  ⟨exprs.cast h, map, this⟩

structure Return (aig : AIG BVBit) where
  result : AIG.ExtendingEntrypoint aig
  cache : Cache result.val.aig

def bitblastWithCache (expr : BVLogicalExpr) (aig : AIG BVBit) (cache : Cache aig) :
    Return aig :=
  goCache aig expr cache
where
  goCache (aig : AIG BVBit) (expr : BVLogicalExpr) (cache : Cache aig) : Return aig :=
    match cache.get? expr with
    | some ref =>
      ⟨⟨⟨aig, ref⟩, Nat.le_refl ..⟩, cache⟩
    | none =>
      let ⟨result, cache⟩ := go aig expr cache
      ⟨result, cache.insert expr result.val.ref⟩
  termination_by (sizeOf expr, 1)

  go (aig : AIG BVBit) (expr : BVLogicalExpr) (cache : Cache aig) : Return aig :=
    match expr with
    | .literal var =>
      let ⟨⟨⟨aig, ref⟩, hpred⟩, exprs⟩ := BVPred.bitblast aig ⟨var, cache.exprs⟩
      ⟨⟨⟨aig, ref⟩, hpred⟩, { cache.cast hpred with exprs }⟩
    | .const val =>
      ⟨⟨⟨aig, aig.mkConstCached val⟩, by simp⟩, cache⟩
    | .not expr =>
      let ⟨⟨⟨aig, exprRef⟩, hexpr⟩, cache⟩ := goCache aig expr cache
      let ret := aig.mkNotCached exprRef
      have := LawfulOperator.le_size (f := mkNotCached) ..
      let cache := cache.cast this
      have := by
        apply LawfulOperator.le_size_of_le_aig_size (f := mkNotCached)
        exact hexpr
      ⟨⟨ret, this⟩, cache⟩
    | .ite discr lhs rhs =>
      let ⟨⟨⟨aig, discrRef⟩, dextend⟩, cache⟩ := goCache aig discr cache
      let ⟨⟨⟨aig, lhsRef⟩, lextend⟩, cache⟩ := goCache aig lhs cache
      let ⟨⟨⟨aig, rhsRef⟩, rextend⟩, cache⟩ := goCache aig rhs cache
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
      let ⟨⟨⟨aig, lhsRef⟩, lextend⟩, cache⟩ := goCache aig lhs cache
      let ⟨⟨⟨aig, rhsRef⟩, rextend⟩, cache⟩ := goCache aig rhs cache
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
  termination_by (sizeOf expr, 0)

/--
Turn a `BVLogicalExpr` into an `Entrypoint`.
-/
def bitblast (expr : BVLogicalExpr) : Entrypoint BVBit :=
  bitblastWithCache expr AIG.empty .empty |>.result.val

namespace bitblastWithCache

theorem goCache_le_size (aig : AIG BVBit) (expr : BVLogicalExpr) (cache : Cache aig) :
    aig.decls.size ≤ (goCache aig expr cache).result.val.aig.decls.size :=
  (goCache aig expr cache).result.property

theorem go_le_size (aig : AIG BVBit) (expr : BVLogicalExpr) (cache : Cache aig) :
    aig.decls.size ≤ (go aig expr cache).result.val.aig.decls.size :=
  (go aig expr cache).result.property

theorem goCache_lt_size_of_lt_aig_size (aig : AIG BVBit) (expr : BVLogicalExpr)
    (cache : Cache aig) (h : x < aig.decls.size) :
    x < (goCache aig expr cache).result.val.aig.decls.size := by
  apply Nat.lt_of_lt_of_le
  · exact h
  · apply goCache_le_size

mutual

theorem goCache_decl_eq (aig : AIG BVBit) (expr : BVLogicalExpr) (cache : Cache aig) :
    ∀ (idx : Nat) (h1) (h2), (goCache aig expr cache).result.val.aig.decls[idx]'h2 = aig.decls[idx]'h1 := by
  generalize hres : goCache aig expr cache = res
  intro idx h1 h2
  unfold goCache at hres
  split at hres
  · rw [getElem_congr_coll]
    rw [← hres]
  · symm at hres
    subst hres
    apply go_decl_eq
termination_by (sizeOf expr, 1)

theorem go_decl_eq (aig : AIG BVBit) (expr : BVLogicalExpr) (cache : Cache aig) :
    ∀ (idx : Nat) (h1) (h2), (go aig expr cache).result.val.aig.decls[idx]'h2 = aig.decls[idx]'h1 := by
  intro idx h1 h2
  unfold go
  split
  · rw [BVPred.bitblast_decl_eq]
  · simp
  · rw [AIG.LawfulOperator.decl_eq (f := mkNotCached), goCache_decl_eq]
    apply goCache_lt_size_of_lt_aig_size
    assumption
  · rw [AIG.LawfulOperator.decl_eq (f := mkIfCached), goCache_decl_eq, goCache_decl_eq, goCache_decl_eq]
    · apply goCache_lt_size_of_lt_aig_size
      assumption
    · apply goCache_lt_size_of_lt_aig_size
      apply goCache_lt_size_of_lt_aig_size
      assumption
    · apply goCache_lt_size_of_lt_aig_size
      apply goCache_lt_size_of_lt_aig_size
      apply goCache_lt_size_of_lt_aig_size
      assumption
  next g lhs rhs =>
    cases g
    all_goals
      dsimp only
      rw [AIG.LawfulOperator.decl_eq, goCache_decl_eq, goCache_decl_eq]
      · apply goCache_lt_size_of_lt_aig_size
        assumption
      · apply goCache_lt_size_of_lt_aig_size
        apply goCache_lt_size_of_lt_aig_size
        assumption
termination_by (sizeOf expr, 0)
decreasing_by all_goals (subst_vars; decreasing_tactic)

end

theorem goCache_isPrefix_aig {aig : AIG BVBit} (cache : Cache aig) :
    IsPrefix aig.decls (goCache aig expr cache).result.val.aig.decls := by
  apply IsPrefix.of
  · intro idx h
    apply goCache_decl_eq
  · apply goCache_le_size

theorem goCache_denote_mem_prefix (aig : AIG BVBit) (cache : Cache aig) (hstart) :
    ⟦
      (goCache aig expr cache).result.val.aig,
      ⟨start, inv, goCache_lt_size_of_lt_aig_size (h := hstart) ..⟩,
      assign
    ⟧
      =
    ⟦aig, ⟨start, inv, hstart⟩, assign⟧ := by
  apply denote.eq_of_isPrefix (entry := ⟨aig, start, inv, hstart⟩)
  apply goCache_isPrefix_aig

end bitblastWithCache

open bitblastWithCache in
theorem bitblastWithCache_isPrefix_aig {aig : AIG BVBit} {cache : Cache aig} :
    IsPrefix aig.decls (bitblastWithCache expr aig cache).result.val.aig.decls := by
  unfold bitblastWithCache
  apply goCache_isPrefix_aig

end BVLogicalExpr

end Std.Tactic.BVDecide
