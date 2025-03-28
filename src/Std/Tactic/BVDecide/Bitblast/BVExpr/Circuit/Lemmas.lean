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

theorem go_Inv_of_Inv (expr : BVLogicalExpr) (aig : AIG BVBit) (assign : BVExpr.Assignment)
    (bvCache : BVExpr.Cache aig) (logCache : Cache aig) (hinv1 : BVExpr.Cache.Inv assign aig bvCache) :
    BVExpr.Cache.Inv assign (go aig expr bvCache logCache).result.val.aig (go aig expr bvCache logCache).bvCache := by
  sorry
  /-
  induction expr generalizing aig with
  | const =>
    simp only [go]
    apply BVExpr.Cache.Inv_cast
    apply LawfulOperator.isPrefix_aig (f := mkConstCached)
    exact hinv
  | atom =>
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
      exact hinv -/

mutual

theorem go_eval_eq_eval (expr : BVLogicalExpr) (aig : AIG BVBit) (assign : BVExpr.Assignment)
    (bvCache : BVExpr.Cache aig) (hinv : BVExpr.Cache.Inv assign aig bvCache)
    (logCache : Cache aig) :
    ⟦(go aig expr bvCache logCache).result, assign.toAIGAssignment⟧ = expr.eval assign := by
  sorry
  /-
  induction expr generalizing aig with
  | const => simp [go]
  | atom =>
    simp only [go, eval_atom]
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
    -/

end

end bitblast

theorem denote_bitblast (expr : BVLogicalExpr) (assign : BVExpr.Assignment) :
    ⟦bitblast expr, assign.toAIGAssignment⟧ = expr.eval assign := by
  unfold bitblast
  sorry
  --rw [bitblast.go_eval_eq_eval]
  --apply BVExpr.Cache.Inv_empty

theorem unsat_of_bitblast (expr : BVLogicalExpr) : expr.bitblast.Unsat → expr.Unsat :=  by
  intro h assign
  rw [← denote_bitblast]
  apply h

end BVLogicalExpr

end Std.Tactic.BVDecide
