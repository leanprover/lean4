/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Pred
import Init.ByCases
import Init.Omega

@[expose] public section

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
  BVExpr.Cache.Inv assign aig cache.exprs ∧
  ∀ k (h : k ∈ cache.map),
    ⟦aig, ⟨(cache.map[k]'h).gate, (cache.map[k]'h).invert, cache.hbound k h⟩, assign.toAIGAssignment⟧
      =
    k.eval assign

theorem Inv_empty (aig : AIG BVBit) : Inv assign aig Cache.empty := by
  refine ⟨BVExpr.Cache.Inv_empty aig, ?_⟩
  intro k hk
  simp [Cache.empty] at hk

theorem Inv_cast (cache : Cache aig1) (hpref : IsPrefix aig1.decls aig2.decls)
    (hinv : Inv assign aig1 cache) :
    Inv assign aig2 (cache.cast hpref.size_le) := by
  refine ⟨BVExpr.Cache.Inv_cast _ hpref hinv.1, ?_⟩
  unfold Cache.cast
  intro k hk
  rw [← hinv.2 k hk]
  apply denote.eq_of_isPrefix (entry := ⟨aig1, _, _, _⟩)
  exact hpref

theorem Inv_insert (cache : Cache aig) (expr : BVLogicalExpr) (ref : AIG.Ref aig)
    (hinv : Inv assign aig cache)
    (href : ⟦aig, ref, assign.toAIGAssignment⟧ = expr.eval assign) :
    Inv assign aig (cache.insert expr ref) := by
  refine ⟨hinv.1, ?_⟩
  intro k hk
  by_cases heq : expr = k
  · subst heq
    have : (cache.insert expr ref).map[expr]'hk = .mk ref.gate ref.invert := by
      unfold Cache.insert
      apply Std.HashMap.getElem_insert_self
    rw [← href]
    congr 3 <;> simp [this]
  · have hmem : k ∈ cache.map := by
      unfold Cache.insert at hk
      apply Std.HashMap.mem_of_mem_insert
      · exact hk
      · simp [heq]
    have : (cache.insert expr ref).map[k]'hk = cache.map[k]'hmem := by
      simp only [Cache.insert]
      rw [Std.HashMap.getElem_insert]
      simp [heq]
    rw [← hinv.2 k hmem]
    congr 3 <;> simp [this]

theorem get?_eq_some_iff (cache : Cache aig) (expr : BVLogicalExpr) (ref : AIG.Ref aig) :
    cache.get? expr = some ref ↔ cache.map[expr]? = some (.mk ref.gate ref.invert) := by
  rcases ref with ⟨gate, invert, hgate⟩
  unfold Cache.get?
  split
  next fanin heq =>
    simp only [heq, Option.some.injEq, Ref.mk.injEq]
    constructor
    · rintro ⟨rfl, rfl⟩
      simp
    · rintro rfl
      simp
  · simp_all

theorem denote_eq_eval_of_get?_eq_some_of_Inv (cache : Cache aig) (expr : BVLogicalExpr)
    (ref : AIG.Ref aig) (hsome : cache.get? expr = some ref) (hinv : Inv assign aig cache) :
    ⟦aig, ref, assign.toAIGAssignment⟧ = expr.eval assign := by
  rw [get?_eq_some_iff] at hsome
  have hmem : expr ∈ cache.map := by
    rw [Std.HashMap.mem_iff_contains, Std.HashMap.contains_eq_isSome_getElem?]
    simp [hsome]
  have : cache.map[expr]'hmem = .mk ref.gate ref.invert := by
    rw [Std.HashMap.getElem?_eq_some_getElem (h' := hmem)] at hsome
    simpa using hsome
  rw [← hinv.2 expr hmem]
  congr 3 <;> simp [this]

end Cache

namespace bitblastWithCache

mutual

theorem goCache_Inv_of_Inv (expr : BVLogicalExpr) (aig : AIG BVBit) (assign : BVExpr.Assignment)
    (cache : Cache aig) (hinv : Cache.Inv assign aig cache) :
    Cache.Inv assign (goCache aig expr cache).result.val.aig (goCache aig expr cache).cache := by
  generalize hres : goCache aig expr cache = res
  unfold goCache at hres
  split at hres
  · rw [← hres]
    exact hinv
  · rw [← hres]
    dsimp only
    apply Cache.Inv_insert
    · apply go_Inv_of_Inv
      exact hinv
    · rw [go_eval_eq_eval]
      exact hinv
termination_by (sizeOf expr, 1)

theorem go_Inv_of_Inv (expr : BVLogicalExpr) (aig : AIG BVBit) (assign : BVExpr.Assignment)
    (cache : Cache aig) (hinv : Cache.Inv assign aig cache) :
    Cache.Inv assign (go aig expr cache).result.val.aig (go aig expr cache).cache := by
  generalize hres : go aig expr cache = res
  unfold go at hres
  split at hres
  · rw [← hres]
    dsimp only
    refine ⟨?_, ?_⟩
    · apply BVPred.bitblast_Inv_of_Inv
      exact hinv.1
    · exact (Cache.Inv_cast cache (BVPred.bitblast_aig_IsPrefix ..) hinv).2
  · rw [← hres]
    apply Cache.Inv_cast
    · apply IsPrefix.rfl
    · exact hinv
  · rw [← hres]
    dsimp only
    apply Cache.Inv_cast
    · apply LawfulOperator.isPrefix_aig (f := mkNotCached)
    · apply goCache_Inv_of_Inv
      exact hinv
  · rw [← hres]
    dsimp only
    apply Cache.Inv_cast
    · apply LawfulOperator.isPrefix_aig (f := mkIfCached)
    · apply goCache_Inv_of_Inv
      apply goCache_Inv_of_Inv
      apply goCache_Inv_of_Inv
      exact hinv
  next g lhs rhs =>
    cases g
    all_goals
      rw [← hres]
      dsimp only
      apply Cache.Inv_cast
      · apply LawfulOperator.isPrefix_aig
      · apply goCache_Inv_of_Inv
        apply goCache_Inv_of_Inv
        exact hinv
termination_by (sizeOf expr, 0)
decreasing_by all_goals (subst_vars; decreasing_tactic)

theorem goCache_eval_eq_eval (expr : BVLogicalExpr) (aig : AIG BVBit) (assign : BVExpr.Assignment)
    (cache : Cache aig) (hinv : Cache.Inv assign aig cache) :
    ⟦(goCache aig expr cache).result, assign.toAIGAssignment⟧ = expr.eval assign := by
  generalize hres : goCache aig expr cache = res
  unfold goCache at hres
  split at hres
  next heq =>
    rw [← hres]
    apply Cache.denote_eq_eval_of_get?_eq_some_of_Inv
    · exact heq
    · exact hinv
  · rw [← hres]
    apply go_eval_eq_eval
    exact hinv
termination_by (sizeOf expr, 1)

theorem go_eval_eq_eval (expr : BVLogicalExpr) (aig : AIG BVBit) (assign : BVExpr.Assignment)
    (cache : Cache aig) (hinv : Cache.Inv assign aig cache) :
    ⟦(go aig expr cache).result, assign.toAIGAssignment⟧ = expr.eval assign := by
  generalize hres : go aig expr cache = res
  unfold go at hres
  split at hres
  · rw [← hres]
    dsimp only
    rw [eval_literal, BVPred.denote_bitblast]
    exact hinv.1
  · rw [← hres]
    simp
  next expr =>
    rw [← hres]
    simp [goCache_eval_eq_eval expr _ _ _ hinv]
  · rw [← hres]
    simp only [Ref.cast_eq, denote_mkIfCached, denote_projected_entry, eval_ite,
      Bool.ite_eq_cond_iff]
    apply ite_congr
    · rw [goCache_denote_mem_prefix (hstart := ?h)]
      case h =>
        apply goCache_lt_size_of_lt_aig_size
        exact Ref.hgate _
      rw [goCache_denote_mem_prefix (hstart := Ref.hgate _)]
      rw [goCache_eval_eq_eval]
      exact hinv
    · intro h
      rw [goCache_denote_mem_prefix (hstart := Ref.hgate _)]
      apply goCache_eval_eq_eval
      apply goCache_Inv_of_Inv
      exact hinv
    · intro h
      apply goCache_eval_eq_eval
      apply goCache_Inv_of_Inv
      apply goCache_Inv_of_Inv
      exact hinv
  next g lhs rhs =>
    cases g
    all_goals
      rw [← hres]
      simp [Gate.eval]
      congr 1
      · rw [goCache_denote_mem_prefix (hstart := Ref.hgate _)]
        apply goCache_eval_eq_eval
        exact hinv
      · apply goCache_eval_eq_eval
        apply goCache_Inv_of_Inv
        exact hinv
termination_by (sizeOf expr, 0)
decreasing_by all_goals (subst_vars; decreasing_tactic)

end

end bitblastWithCache

theorem denote_bitblast (expr : BVLogicalExpr) (assign : BVExpr.Assignment) :
    ⟦bitblast expr, assign.toAIGAssignment⟧ = expr.eval assign := by
  unfold bitblast bitblastWithCache
  rw [bitblastWithCache.goCache_eval_eq_eval]
  apply Cache.Inv_empty

theorem unsat_of_bitblast (expr : BVLogicalExpr) : expr.bitblast.Unsat → expr.Unsat :=  by
  intro h assign
  rw [← denote_bitblast]
  apply h

end BVLogicalExpr

end Std.Tactic.BVDecide
