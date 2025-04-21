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

namespace Cache

abbrev Inv (assign : BVExpr.Assignment) (aig : AIG BVBit) (cache : Cache aig) : Prop :=
  ∀ expr (h : expr ∈ cache.map),
    ⟦aig, ⟨(cache.map[expr]'h).1, (cache.map[expr]'h).2, cache.hbound ..⟩, assign.toAIGAssignment⟧
      =
    expr.eval assign

theorem Inv_empty (aig : AIG BVBit) : Inv assign aig Cache.empty := by
  intro k hk
  simp [Cache.empty] at hk

theorem Inv_cast (cache : Cache aig1) (hpref : IsPrefix aig1.decls aig2.decls)
    (hinv : Inv assign aig1 cache):
    Inv assign aig2 (cache.cast hpref.size_le) := by
  unfold Cache.cast
  intro expr hexpr
  specialize hinv expr hexpr
  rw [← hinv]
  apply denote.eq_of_isPrefix (entry := ⟨aig1, _, _, _⟩)
  exact hpref

theorem Inv_insert (cache : Cache aig) (expr : BVLogicalExpr) (ref : AIG.Ref aig)
    (hinv : Inv assign aig cache)
    (href : ⟦aig, ref, assign.toAIGAssignment⟧ = expr.eval assign) :
    Inv assign aig (cache.insert expr ref) := by
  intro k hk
  by_cases heq : expr = k
  · subst heq
    have : ((cache.insert expr ref).map[expr]'hk) = (ref.gate, ref.invert) := by
      unfold Cache.insert
      apply Std.HashMap.getElem_insert_self
    rw [← href]
    congr 3
    all_goals
      rw [this]
  · have hmem : k ∈ cache.map := by
      unfold Cache.insert at hk
      apply Std.HashMap.mem_of_mem_insert
      · exact hk
      · simp [heq]
    have : ((cache.insert expr ref).map[k]'hk) = cache.map[k]'hmem := by
      unfold Cache.insert
      rw [Std.HashMap.getElem_insert]
      simp [heq]
    rw [← hinv]
    congr 3
    all_goals
      rw [this]

theorem get?_eq_some_iff (cache : Cache aig) (expr : BVLogicalExpr) :
    cache.get? expr = some ref ↔ cache.map[expr]? = some (ref.gate, ref.invert) := by
  cases ref
  unfold Cache.get?
  split
  · next ref heq => cases ref; simp [heq]
  · next heq => simp [heq]

theorem denote_eq_eval_of_get?_eq_some_of_Inv (cache : Cache aig) (expr : BVLogicalExpr)
    (ref : AIG.Ref aig) (hsome : cache.get? expr = some ref) (hinv : Inv assign aig cache) :
    ⟦aig,  ref, assign.toAIGAssignment⟧ = expr.eval assign := by
  rw [get?_eq_some_iff] at hsome
  have hmem : expr ∈ cache.map := by
    rw [Std.HashMap.mem_iff_contains, Std.HashMap.contains_eq_isSome_getElem?]
    simp [hsome]
  have href : cache.map[expr]'hmem = (ref.gate, ref.invert) := by
    rw [Std.HashMap.getElem?_eq_some_getElem (h' := hmem)] at hsome
    simp only [Option.some.injEq] at hsome
    rw [hsome]
  specialize hinv expr hmem
  rw [← hinv]
  cases ref
  congr 3
  all_goals
    rw [href]

end Cache

namespace bitblast

mutual

theorem goCache_BvInv_of_BvInv (expr : BVLogicalExpr) (aig : AIG BVBit) (assign : BVExpr.Assignment)
    (bvCache : BVExpr.Cache aig) (logCache : Cache aig) (hinv : BVExpr.Cache.Inv assign aig bvCache) :
    BVExpr.Cache.Inv assign (goCache aig expr bvCache logCache).result.val.aig (goCache aig expr bvCache logCache).bvCache := by
  generalize hres : goCache aig expr bvCache logCache = res
  unfold goCache at hres
  split at hres
  · rw [← hres]
    exact hinv
  · rw [← hres]
    apply go_BvInv_of_BvInv
    exact hinv
termination_by (sizeOf expr, 1)

theorem go_BvInv_of_BvInv (expr : BVLogicalExpr) (aig : AIG BVBit) (assign : BVExpr.Assignment)
    (bvCache : BVExpr.Cache aig) (logCache : Cache aig) (hinv : BVExpr.Cache.Inv assign aig bvCache) :
    BVExpr.Cache.Inv assign (go aig expr bvCache logCache).result.val.aig (go aig expr bvCache logCache).bvCache := by
  generalize hres : go aig expr bvCache logCache = res
  unfold go at hres
  split at hres
  · rw [← hres]
    apply BVPred.bitblast_Inv_of_Inv
    exact hinv
  · rw [← hres]
    apply BVExpr.Cache.Inv_cast
    apply LawfulOperator.isPrefix_aig (f := mkConstCached)
    exact hinv
  · next expr =>
    rw [← hres]
    apply BVExpr.Cache.Inv_cast
    · apply LawfulOperator.isPrefix_aig (f := mkNotCached)
    · apply goCache_BvInv_of_BvInv
      exact hinv
  · next discr lhs rhs =>
    rw [← hres]
    apply BVExpr.Cache.Inv_cast
    · apply LawfulOperator.isPrefix_aig
    · apply goCache_BvInv_of_BvInv
      apply goCache_BvInv_of_BvInv
      apply goCache_BvInv_of_BvInv
      exact hinv
  · next g lhs rhs =>
    match g with
    | .and | .xor | .beq | .or =>
      rw [← hres]
      apply BVExpr.Cache.Inv_cast
      · apply LawfulOperator.isPrefix_aig
      · apply goCache_BvInv_of_BvInv
        apply goCache_BvInv_of_BvInv
        exact hinv
termination_by (sizeOf expr, 0)

end

mutual

theorem goCache_Inv_of_Inv (expr : BVLogicalExpr) (aig : AIG BVBit) (assign : BVExpr.Assignment)
    (bvCache : BVExpr.Cache aig) (logCache : Cache aig) (hinv1 : BVExpr.Cache.Inv assign aig bvCache)
    (hinv2 : Cache.Inv assign aig logCache) :
    Cache.Inv assign (goCache aig expr bvCache logCache).result.val.aig (goCache aig expr bvCache logCache).logCache := by
  generalize hres : goCache aig expr bvCache logCache = res
  unfold goCache at hres
  split at hres
  · rw [← hres]
    exact hinv2
  · rw [← hres]
    apply Cache.Inv_insert
    · apply go_Inv_of_Inv
      · exact hinv1
      · exact hinv2
    · rw [go_denote_eq]
      · exact hinv1
      · exact hinv2
termination_by (sizeOf expr, 1, 0)

theorem go_Inv_of_Inv (expr : BVLogicalExpr) (aig : AIG BVBit) (assign : BVExpr.Assignment)
    (bvCache : BVExpr.Cache aig) (logCache : Cache aig) (hinv1 : BVExpr.Cache.Inv assign aig bvCache)
    (hinv2 : Cache.Inv assign aig logCache) :
    Cache.Inv assign (go aig expr bvCache logCache).result.val.aig (go aig expr bvCache logCache).logCache := by
  generalize hres : go aig expr bvCache logCache = res
  unfold go at hres
  split at hres
  · rw [← hres]
    apply Cache.Inv_cast
    · dsimp only
      apply BVPred.bitblast_aig_IsPrefix
    · exact hinv2
  · rw [← hres]
    apply Cache.Inv_cast
    apply LawfulOperator.isPrefix_aig (f := mkConstCached)
    exact hinv2
  · next expr =>
    rw [← hres]
    apply Cache.Inv_cast
    · apply LawfulOperator.isPrefix_aig (f := mkNotCached)
    · apply goCache_Inv_of_Inv
      · exact hinv1
      · exact hinv2
  · next discr lhs rhs =>
    rw [← hres]
    apply Cache.Inv_cast
    · apply LawfulOperator.isPrefix_aig
    · apply goCache_Inv_of_Inv
      · apply goCache_BvInv_of_BvInv
        apply goCache_BvInv_of_BvInv
        exact hinv1
      · apply goCache_Inv_of_Inv
        · apply goCache_BvInv_of_BvInv
          exact hinv1
        · apply goCache_Inv_of_Inv
          · exact hinv1
          · exact hinv2
  · next g lhs rhs =>
    match g with
    | .and | .xor | .beq | .or =>
      rw [← hres]
      apply Cache.Inv_cast
      · apply LawfulOperator.isPrefix_aig
      · apply goCache_Inv_of_Inv
        · apply goCache_BvInv_of_BvInv
          exact hinv1
        · apply goCache_Inv_of_Inv
          · exact hinv1
          · exact hinv2
termination_by (sizeOf expr, 0, 0)

theorem goCache_denote_eq (expr : BVLogicalExpr) (aig : AIG BVBit) (assign : BVExpr.Assignment)
    (bvCache : BVExpr.Cache aig) (logCache : Cache aig) (hinv1 : BVExpr.Cache.Inv assign aig bvCache)
    (hinv2 : Cache.Inv assign aig logCache) :
    ⟦(goCache aig expr bvCache logCache).result, assign.toAIGAssignment⟧ = expr.eval assign := by
  unfold goCache
  split
  · next heq =>
    apply Cache.denote_eq_eval_of_get?_eq_some_of_Inv
    · exact heq
    · exact hinv2
  · rw [go_denote_eq]
    · exact hinv1
    · exact hinv2
termination_by (sizeOf expr, 0, 1)

theorem go_denote_eq (expr : BVLogicalExpr) (aig : AIG BVBit) (assign : BVExpr.Assignment)
    (bvCache : BVExpr.Cache aig) (logCache : Cache aig) (hinv1 : BVExpr.Cache.Inv assign aig bvCache)
    (hinv2 : Cache.Inv assign aig logCache) :
    ⟦(go aig expr bvCache logCache).result, assign.toAIGAssignment⟧ = expr.eval assign := by
  unfold go
  split
  · rw [BVPred.denote_bitblast]
    · simp
    · exact hinv1
  · simp
  · simp only [denote_mkNotCached, denote_projected_entry, eval_not, Bool.not_eq_eq_eq_not,
      Bool.not_not]
    rw [goCache_denote_eq]
    · exact hinv1
    · exact hinv2
  · next discr lhs rhs =>
    simp only [Ref.cast_eq, denote_mkIfCached, denote_projected_entry, eval_ite,
      Bool.ite_eq_cond_iff]
    apply ite_congr
    · rw [goCache_denote_mem_prefix]
      rw [goCache_denote_mem_prefix]
      rw [goCache_denote_eq]
      · exact hinv1
      · exact hinv2
    · intro h
      rw [goCache_denote_mem_prefix]
      rw [goCache_denote_eq]
      · apply goCache_BvInv_of_BvInv
        exact hinv1
      · apply goCache_Inv_of_Inv
        · exact hinv1
        · exact hinv2
    · intro h
      rw [goCache_denote_eq]
      · apply goCache_BvInv_of_BvInv
        apply goCache_BvInv_of_BvInv
        exact hinv1
      · apply goCache_Inv_of_Inv
        · apply goCache_BvInv_of_BvInv
          exact hinv1
        · apply goCache_Inv_of_Inv
          · exact hinv1
          · exact hinv2
  · next g lhs rhs =>
    match g with
    | .and | .xor | .beq | .or =>
      simp only [Ref.cast_eq, denote_mkAndCached, denote_mkXorCached, denote_mkBEqCached,
        denote_mkOrCached, denote_projected_entry, eval_gate, Gate.eval]
      rw [goCache_denote_eq]
      · rw [goCache_denote_mem_prefix]
        rw [goCache_denote_eq]
        · exact hinv1
        · exact hinv2
      · apply goCache_BvInv_of_BvInv
        exact hinv1
      · apply goCache_Inv_of_Inv
        · exact hinv1
        · exact hinv2
termination_by (sizeOf expr, 0, 0)

end

end bitblast

theorem denote_bitblast (expr : BVLogicalExpr) (assign : BVExpr.Assignment) :
    ⟦bitblast expr, assign.toAIGAssignment⟧ = expr.eval assign := by
  unfold bitblast
  rw [bitblast.goCache_denote_eq]
  · apply BVExpr.Cache.Inv_empty
  · apply Cache.Inv_empty

theorem unsat_of_bitblast (expr : BVLogicalExpr) : expr.bitblast.Unsat → expr.Unsat :=  by
  intro h assign
  rw [← denote_bitblast]
  apply h

end BVLogicalExpr

end Std.Tactic.BVDecide
