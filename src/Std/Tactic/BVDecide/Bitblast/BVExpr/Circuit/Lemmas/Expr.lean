/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Basic
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Const
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Var
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Not
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.ShiftLeft
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.ShiftRight
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Add
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Append
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Replicate
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Extract
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.RotateLeft
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.RotateRight
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Mul
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Udiv
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Umod
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Expr

/-!
This module contains the verification of the `BitVec` expressions (`BVExpr`) bitblaster from
`Impl.Expr`.
-/

namespace Std.Tactic.BVDecide

open Std.Sat
open Std.Sat.AIG

namespace BVExpr

namespace Cache

abbrev Inv (assign : Assignment) (aig : AIG BVBit) (cache : Cache aig) : Prop :=
  ∀ k (h1 : k ∈ cache.map), ∀ (i : Nat) (h2 : i < k.w),
    ⟦aig, ⟨(cache.map.get k h1)[i].1, (cache.map.get k h1)[i].2, cache.hbound ..⟩, assign.toAIGAssignment⟧
      =
    (k.expr.eval assign).getLsbD i

theorem Inv_empty (aig : AIG BVBit) : Inv assign aig Cache.empty := sorry

theorem Inv_cast (cache : Cache aig1) (hle : aig1.decls.size ≤ aig2.decls.size)
    (hinv : Inv assign aig1 cache):
    Inv assign aig2 (cache.cast hle) := sorry

theorem Inv_insert (cache : Cache aig) (expr : BVExpr w) (refs : AIG.RefVec aig w)
    (hinv : Inv assign aig cache)
    (hrefs : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, refs.get idx hidx, assign.toAIGAssignment⟧ = (expr.eval assign).getLsbD idx) :
    Inv assign aig (cache.insert expr refs) := sorry

theorem denote_eq_eval_of_get?_eq_some_of_Inv (cache : Cache aig) (expr : BVExpr w)
    (refs : AIG.RefVec aig w) (hsome : cache.get? expr = some refs) (hinv : Inv assign aig cache) :
    ∀ (i : Nat) (h : i < w),
      ⟦aig,  refs.get i h, assign.toAIGAssignment⟧ = (expr.eval assign).getLsbD i := sorry

end Cache

namespace bitblast

theorem goCache_val_eq_bitblast (aig : AIG BVBit) (expr : BVExpr w) :
    (goCache aig expr .empty).result.val = bitblast aig expr := by
  rfl

/-

theorem go_denote_eq (aig : AIG BVBit) (expr : BVExpr w) (assign : Assignment) :
    ∀ (idx : Nat) (hidx : idx < w),
        ⟦(go aig expr).val.aig, (go aig expr).val.vec.get idx hidx, assign.toAIGAssignment⟧
          =
        (expr.eval assign).getLsbD idx := by
  intro idx hidx
  induction expr generalizing aig idx with
  | append lhs rhs hw lih rih =>
    rename_i lw rw
    subst hw
    simp only [go, denote_blastAppend, RefVec.get_cast, Ref.cast_eq, eval_append,
      BitVec.getLsbD_append]
    split
    · next hsplit => rw [rih]
    · next hsplit => rw [go_denote_mem_prefix, lih]
  | replicate n expr hw ih =>
    subst hw
    simp [go, ih, hidx, ← BitVec.getLsbD_eq_getElem]
  | @extract w start len inner ih =>
    simp only [go, denote_blastExtract, Bool.if_false_right, eval_extract,
      BitVec.getLsbD_extractLsb', hidx, decide_true, Bool.true_and]
    split
    · next hsplit =>
      rw [ih]
    · apply Eq.symm
      apply BitVec.getLsbD_ge
      omega
  | shiftLeft lhs rhs lih rih =>
    simp only [go, eval_shiftLeft]
    apply denote_blastShiftLeft
    · intros
      dsimp only
      rw [go_denote_mem_prefix]
      rw [← lih (aig := aig)]
      · simp
      · assumption
      · simp [Ref.hgate]
    · intros
      rw [← rih]
  | shiftRight lhs rhs lih rih =>
    simp only [go, eval_shiftRight]
    apply denote_blastShiftRight
    · intros
      dsimp only
      rw [go_denote_mem_prefix]
      rw [← lih (aig := aig)]
      · simp
      · assumption
      · simp [Ref.hgate]
    · intros
      rw [← rih]
  | arithShiftRight lhs rhs lih rih =>
    simp only [go, eval_arithShiftRight]
    apply denote_blastArithShiftRight
    · intros
      dsimp only
      rw [go_denote_mem_prefix]
      rw [← lih (aig := aig)]
      · simp
      · assumption
      · simp [Ref.hgate]
    · intros
      rw [← rih]
-/

theorem go_denote_mem_prefix (aig : AIG BVBit) (expr : BVExpr w) (assign : Assignment)
    (cache : Cache aig) (start : Nat) (hstart) :
    ⟦
      (go aig expr cache).result.val.aig,
      ⟨start, inv, by apply Nat.lt_of_lt_of_le; exact hstart; apply (go aig expr cache).result.property⟩,
      assign.toAIGAssignment
    ⟧
      =
    ⟦aig, ⟨start, inv, hstart⟩, assign.toAIGAssignment⟧ := by
  apply denote.eq_of_isPrefix (entry := ⟨aig, start, inv, hstart⟩)
  apply IsPrefix.of
  · intros
    apply go_decl_eq
  · intros
    apply (go aig expr cache).result.property

theorem goCache_denote_mem_prefix (aig : AIG BVBit) (expr : BVExpr w) (assign : Assignment)
    (cache : Cache aig) (start : Nat) (hstart) :
    ⟦
      (goCache aig expr cache).result.val.aig,
      ⟨start, inv, by apply Nat.lt_of_lt_of_le; exact hstart; apply (goCache aig expr cache).result.property⟩,
      assign.toAIGAssignment
    ⟧
      =
    ⟦aig, ⟨start, inv, hstart⟩, assign.toAIGAssignment⟧ := by
  apply denote.eq_of_isPrefix (entry := ⟨aig, start, inv, hstart⟩)
  apply IsPrefix.of
  · intros
    apply goCache_decl_eq
  · intros
    apply (goCache aig expr cache).result.property

mutual


theorem goCache_Inv_of_Inv (cache : Cache aig) (hinv : Cache.Inv assign aig cache) :
    ∀ (expr : BVExpr w),
        Cache.Inv assign (goCache aig expr cache).result.val.aig (goCache aig expr cache).cache := by
  intro expr
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
    · intro idx hidx
      rw [go_denote_eq]
      exact hinv

theorem go_Inv_of_Inv (cache : Cache aig) (hinv : Cache.Inv assign aig cache) :
    ∀ (expr : BVExpr w),
        Cache.Inv assign (go aig expr cache).result.val.aig (go aig expr cache).cache := sorry

theorem goCache_denote_eq (aig : AIG BVBit) (expr : BVExpr w) (assign : Assignment)
    (cache : Cache aig) (hinv : Cache.Inv assign aig cache) :
    ∀ (idx : Nat) (hidx : idx < w),
        ⟦(goCache aig expr cache).result.val.aig, (goCache aig expr cache).result.val.vec.get idx hidx, assign.toAIGAssignment⟧
          =
        (expr.eval assign).getLsbD idx := by
  intro idx hidx
  generalize hres : goCache aig expr cache = res
  unfold goCache at hres
  split at hres
  · next heq =>
    rw [← hres]
    apply Cache.denote_eq_eval_of_get?_eq_some_of_Inv
    · exact heq
    · exact hinv
  · rw [← hres]
    rw [go_denote_eq]
    exact hinv

theorem go_denote_eq (aig : AIG BVBit) (expr : BVExpr w) (assign : Assignment)
    (cache : Cache aig) (hinv : Cache.Inv assign aig cache) :
    ∀ (idx : Nat) (hidx : idx < w),
        ⟦(go aig expr cache).result.val.aig, (go aig expr cache).result.val.vec.get idx hidx, assign.toAIGAssignment⟧
          =
        (expr.eval assign).getLsbD idx := by
  intro idx hidx
  generalize hres : go aig expr cache = res
  unfold go at hres
  split at hres
  · rw [← hres]
    simp
  · rw [← hres]
    simp
  · dsimp only at hres
    split at hres
    · rw [← hres]
      simp
      congr 1
      · rw [goCache_denote_mem_prefix]
        rw [goCache_denote_eq]
        exact hinv
      · rw [goCache_denote_eq]
        apply goCache_Inv_of_Inv
        exact hinv
    · rw [← hres]
      simp
      congr 1
      · rw [goCache_denote_mem_prefix]
        rw [goCache_denote_eq]
        exact hinv
      · rw [goCache_denote_eq]
        apply goCache_Inv_of_Inv
        exact hinv
    · rw [← hres]
      simp
      congr 1
      · rw [goCache_denote_mem_prefix]
        rw [goCache_denote_eq]
        exact hinv
      · rw [goCache_denote_eq]
        apply goCache_Inv_of_Inv
        exact hinv
    · rw [← hres]
      simp
      rw [denote_blastAdd]
      · intro idx hidx
        rw [goCache_denote_mem_prefix]
        simp
        rw [goCache_denote_eq]
        · exact hinv
        · simp [Ref.hgate]
      · intro idx hidx
        rw [goCache_denote_eq]
        apply goCache_Inv_of_Inv
        exact hinv
    · rw [← hres]
      simp
      rw [denote_blastMul]
      · intro idx hidx
        rw [goCache_denote_mem_prefix]
        simp
        rw [goCache_denote_eq]
        · exact hinv
        · simp [Ref.hgate]
      · intro idx hidx
        rw [goCache_denote_eq]
        apply goCache_Inv_of_Inv
        exact hinv
    · rw [← hres]
      simp
      rw [denote_blastUdiv]
      · intro idx hidx
        rw [goCache_denote_mem_prefix]
        simp
        rw [goCache_denote_eq]
        · exact hinv
        · simp [Ref.hgate]
      · intro idx hidx
        rw [goCache_denote_eq]
        apply goCache_Inv_of_Inv
        exact hinv
    · rw [← hres]
      simp
      rw [denote_blastUmod]
      · intro idx hidx
        rw [goCache_denote_mem_prefix]
        simp
        rw [goCache_denote_eq]
        · exact hinv
        · simp [Ref.hgate]
      · intro idx hidx
        rw [goCache_denote_eq]
        apply goCache_Inv_of_Inv
        exact hinv
  · dsimp only at hres
    split at hres
    · rw [← hres]
      simp [hidx]
      rw [goCache_denote_eq]
      · apply BitVec.getLsbD_eq_getElem
      · exact hinv
    · rw [← hres]
      simp [hidx]
      split
      all_goals
      · rw [goCache_denote_eq]
        · apply BitVec.getLsbD_eq_getElem
        · exact hinv
    · rw [← hres]
      simp [hidx]
      split
      all_goals
      · rw [goCache_denote_eq]
        · apply BitVec.getLsbD_eq_getElem
        · exact hinv
    · rw [← hres]
      simp [hidx, BitVec.getElem_sshiftRight]
      split
      · rw [goCache_denote_eq]
        · apply BitVec.getLsbD_eq_getElem
        · exact hinv
      · rw [goCache_denote_eq]
        · simp [BitVec.msb_eq_getLsbD_last]
        · exact hinv
  · rw [← hres]
    simp [BitVec.getLsbD_append, ]
    split
    · rw [goCache_denote_eq]
      · sorry
      · apply goCache_Inv_of_Inv
        exact hinv
    · sorry
  · sorry
  · rw [← hres]
    simp [hidx]
    split
    · rw [goCache_denote_eq]
      exact hinv
    · symm
      apply BitVec.getLsbD_ge
      omega
  · sorry
  · sorry
  · sorry

end


end bitblast

@[simp]
theorem denote_bitblast (aig : AIG BVBit) (expr : BVExpr w) (assign : Assignment) :
    ∀ (idx : Nat) (hidx : idx < w),
        ⟦(bitblast aig expr).aig, (bitblast aig expr).vec.get idx hidx, assign.toAIGAssignment⟧
          =
        (expr.eval assign).getLsbD idx
    := by
  intros
  rw [← bitblast.goCache_val_eq_bitblast]
  rw [bitblast.goCache_denote_eq]
  apply Cache.Inv_empty

end BVExpr

end Std.Tactic.BVDecide
