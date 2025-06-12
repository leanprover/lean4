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
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Reverse
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Clz
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
    ⟦aig, ⟨(cache.map.get k h1)[i].gate, (cache.map.get k h1)[i].invert, cache.hbound ..⟩, assign.toAIGAssignment⟧
      =
    (k.expr.eval assign).getLsbD i

theorem Inv_empty (aig : AIG BVBit) : Inv assign aig Cache.empty := by
  intro k hk
  simp [Cache.empty] at hk

theorem Inv_cast (cache : Cache aig1) (hpref : IsPrefix aig1.decls aig2.decls)
    (hinv : Inv assign aig1 cache):
    Inv assign aig2 (cache.cast hpref.size_le) := by
  unfold Cache.cast
  intro k hk i h2
  specialize hinv k hk i h2
  rw [← hinv]
  apply denote.eq_of_isPrefix (entry := ⟨aig1, _, _, _⟩)
  exact hpref

theorem Inv_insert (cache : Cache aig) (expr : BVExpr w) (refs : AIG.RefVec aig w)
    (hinv : Inv assign aig cache)
    (hrefs : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, refs.get idx hidx, assign.toAIGAssignment⟧ = (expr.eval assign).getLsbD idx) :
    Inv assign aig (cache.insert expr refs) := by
  intro k hk i hi
  by_cases heq : ⟨w, expr⟩ = k
  · rcases k with ⟨kw, kexpr⟩
    simp only [Key.mk.injEq] at heq
    rcases heq with ⟨hkeq, hexpr⟩
    subst hkeq
    replace hexpr := eq_of_heq hexpr
    subst hexpr
    have : ((cache.insert expr refs).map.get ⟨w, expr⟩ hk) = refs.refs := by
      unfold Cache.insert
      apply Std.DHashMap.get_insert_self
    specialize hrefs i hi
    rw [← hrefs]
    congr 3
    all_goals
      rw [getElem_congr_coll]
      exact this
  · have hmem : k ∈ cache.map := by
      unfold Cache.insert at hk
      apply Std.DHashMap.mem_of_mem_insert
      · exact hk
      · simp [heq]
    have : ((cache.insert expr refs).map.get k hk) = cache.map.get k hmem := by
      unfold Cache.insert
      rw [Std.DHashMap.get_insert]
      simp [heq]
    specialize hinv k hmem i hi
    rw [← hinv]
    congr 3
    all_goals
      rw [getElem_congr_coll]
      exact this

theorem get?_eq_some_iff (cache : Cache aig) (expr : BVExpr w) :
    cache.get? expr = some refs ↔ cache.map.get? ⟨w, expr⟩ = some refs.refs := by
  cases refs
  unfold Cache.get?
  split <;> simp_all

theorem denote_eq_eval_of_get?_eq_some_of_Inv (cache : Cache aig) (expr : BVExpr w)
    (refs : AIG.RefVec aig w) (hsome : cache.get? expr = some refs) (hinv : Inv assign aig cache) :
    ∀ (i : Nat) (h : i < w),
      ⟦aig,  refs.get i h, assign.toAIGAssignment⟧ = (expr.eval assign).getLsbD i := by
  intro i h
  rcases refs with ⟨refs, _⟩
  rw [get?_eq_some_iff] at hsome
  have hmem : ⟨w, expr⟩ ∈ cache.map := by
    rw [Std.DHashMap.mem_iff_contains, Std.DHashMap.contains_eq_isSome_get?]
    simp [hsome]
  have : refs = cache.map.get ⟨w, expr⟩ hmem := by
    rw [Std.DHashMap.get?_eq_some_get (h := hmem)] at hsome
    simp only [Option.some.injEq] at hsome
    rw [hsome]
  specialize hinv ⟨w, expr⟩ hmem i h
  rw [← hinv]
  subst this
  congr

end Cache

namespace bitblast

theorem goCache_val_eq_bitblast (aig : AIG BVBit) (expr : BVExpr w) (cache : Cache aig) :
    goCache aig expr cache = bitblast aig ⟨expr, cache⟩ := by
  rfl

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

set_option maxHeartbeats 400000

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
termination_by expr => (sizeOf expr, 1, sizeOf aig)

theorem go_Inv_of_Inv (cache : Cache aig) (hinv : Cache.Inv assign aig cache) :
    ∀ (expr : BVExpr w),
        Cache.Inv assign (go aig expr cache).result.val.aig (go aig expr cache).cache := by
  intro expr
  generalize hres : go aig expr cache = res
  unfold go at hres
  split at hres
  · rw [← hres]
    apply Cache.Inv_cast
    · apply LawfulVecOperator.isPrefix_aig (f := blastVar)
    · exact hinv
  · rw [← hres]
    apply Cache.Inv_cast
    · apply IsPrefix.rfl
    · exact hinv
  · next op lhsExpr rhsExpr =>
    dsimp only at hres
    match op with
    | .and | .or | .xor =>
      dsimp only at hres
      rw [← hres]
      apply Cache.Inv_cast
      · apply RefVec.IsPrefix_zip
      · apply goCache_Inv_of_Inv
        apply goCache_Inv_of_Inv
        exact hinv
    | .add | .mul | .udiv | .umod =>
      dsimp only at hres
      rw [← hres]
      apply Cache.Inv_cast
      · apply LawfulVecOperator.isPrefix_aig
      · apply goCache_Inv_of_Inv
        apply goCache_Inv_of_Inv
        exact hinv
  · dsimp only at hres
    split at hres
    all_goals
      rw [← hres]
      dsimp only
      apply Cache.Inv_cast
      · apply LawfulVecOperator.isPrefix_aig
      · apply goCache_Inv_of_Inv
        exact hinv
  · rw [← hres]
    dsimp only
    apply Cache.Inv_cast
    · apply LawfulVecOperator.isPrefix_aig
    · apply goCache_Inv_of_Inv
      apply goCache_Inv_of_Inv
      exact hinv
  · rw [← hres]
    dsimp only
    apply Cache.Inv_cast
    · apply LawfulVecOperator.isPrefix_aig
    · apply goCache_Inv_of_Inv
      exact hinv
  · rw [← hres]
    dsimp only
    apply Cache.Inv_cast
    · apply LawfulVecOperator.isPrefix_aig
    · apply goCache_Inv_of_Inv
      exact hinv
  · rw [← hres]
    dsimp only
    apply Cache.Inv_cast
    · apply LawfulVecOperator.isPrefix_aig
    · apply goCache_Inv_of_Inv
      apply goCache_Inv_of_Inv
      exact hinv
  · rw [← hres]
    dsimp only
    apply Cache.Inv_cast
    · apply LawfulVecOperator.isPrefix_aig
    · apply goCache_Inv_of_Inv
      apply goCache_Inv_of_Inv
      exact hinv
  · rw [← hres]
    dsimp only
    apply Cache.Inv_cast
    · apply LawfulVecOperator.isPrefix_aig
    · apply goCache_Inv_of_Inv
      apply goCache_Inv_of_Inv
      exact hinv
termination_by expr => (sizeOf expr, 0, 0)

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
termination_by (sizeOf expr, 0, w)


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
      simp only [RefVec.denote_zip, RefVec.get_cast, Ref.cast_eq, denote_mkAndCached, eval_bin,
        BVBinOp.eval_and, BitVec.getLsbD_and]
      congr 1
      · rw [goCache_denote_mem_prefix]
        rw [goCache_denote_eq]
        exact hinv
      · rw [goCache_denote_eq]
        apply goCache_Inv_of_Inv
        exact hinv
    · rw [← hres]
      simp only [RefVec.denote_zip, RefVec.get_cast, Ref.cast_eq, denote_mkOrCached, eval_bin,
        BVBinOp.eval_or, BitVec.getLsbD_or]
      congr 1
      · rw [goCache_denote_mem_prefix]
        rw [goCache_denote_eq]
        exact hinv
      · rw [goCache_denote_eq]
        apply goCache_Inv_of_Inv
        exact hinv
    · rw [← hres]
      simp only [RefVec.denote_zip, RefVec.get_cast, Ref.cast_eq, denote_mkXorCached, eval_bin,
        BVBinOp.eval_xor, BitVec.getLsbD_xor]
      congr 1
      · rw [goCache_denote_mem_prefix]
        rw [goCache_denote_eq]
        exact hinv
      · rw [goCache_denote_eq]
        apply goCache_Inv_of_Inv
        exact hinv
    · rw [← hres]
      simp only [eval_bin, BVBinOp.eval_add]
      rw [denote_blastAdd]
      · intro idx hidx
        rw [goCache_denote_mem_prefix]
        simp only [RefVec.get_cast, Ref.cast_eq]
        rw [goCache_denote_eq]
        · exact hinv
        · simp [Ref.hgate]
      · intro idx hidx
        rw [goCache_denote_eq]
        apply goCache_Inv_of_Inv
        exact hinv
    · rw [← hres]
      simp only [eval_bin, BVBinOp.eval_mul]
      rw [denote_blastMul]
      · intro idx hidx
        rw [goCache_denote_mem_prefix]
        simp only [RefVec.get_cast, Ref.cast_eq]
        rw [goCache_denote_eq]
        · exact hinv
        · simp [Ref.hgate]
      · intro idx hidx
        rw [goCache_denote_eq]
        apply goCache_Inv_of_Inv
        exact hinv
    · rw [← hres]
      simp only [eval_bin, BVBinOp.eval_udiv]
      rw [denote_blastUdiv]
      · intro idx hidx
        rw [goCache_denote_mem_prefix]
        simp only [RefVec.get_cast, Ref.cast_eq]
        rw [goCache_denote_eq]
        · exact hinv
        · simp [Ref.hgate]
      · intro idx hidx
        rw [goCache_denote_eq]
        apply goCache_Inv_of_Inv
        exact hinv
    · rw [← hres]
      simp only [eval_bin, BVBinOp.eval_umod]
      rw [denote_blastUmod]
      · intro idx hidx
        rw [goCache_denote_mem_prefix]
        simp only [RefVec.get_cast, Ref.cast_eq]
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
      simp only [denote_blastNot, eval_un, BVUnOp.eval_not, hidx, BitVec.getLsbD_eq_getElem,
        BitVec.getElem_not, Bool.not_eq_eq_eq_not, Bool.not_not]
      rw [goCache_denote_eq]
      · apply BitVec.getLsbD_eq_getElem
      · exact hinv
    · rw [← hres]
      simp only [denote_blastRotateLeft, eval_un, BVUnOp.eval_rotateLeft, hidx,
        BitVec.getLsbD_eq_getElem, BitVec.getElem_rotateLeft]
      split
      all_goals
      · rw [goCache_denote_eq]
        · apply BitVec.getLsbD_eq_getElem
        · exact hinv
    · rw [← hres]
      simp only [denote_blastRotateRight, eval_un, BVUnOp.eval_rotateRight, hidx,
        BitVec.getLsbD_eq_getElem, BitVec.getElem_rotateRight]
      split
      all_goals
      · rw [goCache_denote_eq]
        · apply BitVec.getLsbD_eq_getElem
        · exact hinv
    · rw [← hres]
      simp only [denote_blastArithShiftRightConst, eval_un, BVUnOp.eval_arithShiftRightConst, hidx,
        BitVec.getLsbD_eq_getElem, BitVec.getElem_sshiftRight]
      split
      · rw [goCache_denote_eq]
        · apply BitVec.getLsbD_eq_getElem
        · exact hinv
      · rw [goCache_denote_eq]
        · simp [BitVec.msb_eq_getLsbD_last]
        · exact hinv
    · rw [← hres]
      simp only [denote_blastReverse, eval_un, BVUnOp.eval_reverse, hidx, BitVec.getLsbD_eq_getElem,
        BitVec.getElem_reverse, BitVec.getMsbD_eq_getLsbD, decide_true, Bool.true_and]
      rw [goCache_denote_eq]
      exact hinv
    · rw [← hres]
      simp only [eval_un, BVUnOp.eval_clz]
      rw [BitVec.clzAuxRec_eq_clz_of_eq (x := eval assign _) (by omega), denote_blastClz]
      intro idx hidx
      rw [goCache_denote_eq]
      exact hinv
  · next h =>
    subst h
    rw [← hres]
    simp only [denote_blastAppend, RefVec.get_cast, Ref.cast_eq, eval_append, BitVec.getLsbD_append]
    split
    · rw [goCache_denote_eq]
      apply goCache_Inv_of_Inv
      exact hinv
    · rw [goCache_denote_mem_prefix]
      rw [goCache_denote_eq]
      exact hinv
  · next h =>
    subst h
    rw [← hres]
    simp only [denote_blastReplicate, eval_replicate, hidx, BitVec.getLsbD_eq_getElem,
      BitVec.getElem_replicate]
    split
    · next h =>
      simp only [h, Nat.zero_mul, Nat.not_lt_zero] at hidx
    · rw [goCache_denote_eq]
      · apply BitVec.getLsbD_eq_getElem
      · exact hinv
  · rw [← hres]
    simp only [denote_blastExtract, eval_extract, hidx, BitVec.getLsbD_eq_getElem,
      BitVec.getElem_extractLsb']
    split
    · rw [goCache_denote_eq]
      exact hinv
    · symm
      apply BitVec.getLsbD_of_ge
      omega
  · rw [eval_shiftLeft, ← hres, denote_blastShiftLeft]
    · intro idx hidx
      rw [goCache_denote_mem_prefix]
      · simp only [RefVec.get_cast, Ref.cast_eq]
        rw [goCache_denote_eq]
        exact hinv
      · simp [Ref.hgate]
    · intro idx hidx
      rw [goCache_denote_eq]
      apply goCache_Inv_of_Inv
      exact hinv
  · rw [eval_shiftRight, ← hres, denote_blastShiftRight]
    · intro idx hidx
      rw [goCache_denote_mem_prefix]
      · simp only [RefVec.get_cast, Ref.cast_eq]
        rw [goCache_denote_eq]
        exact hinv
      · simp [Ref.hgate]
    · intro idx hidx
      rw [goCache_denote_eq]
      apply goCache_Inv_of_Inv
      exact hinv
  · rw [eval_arithShiftRight, ← hres, denote_blastArithShiftRight]
    · intro idx hidx
      rw [goCache_denote_mem_prefix]
      · simp only [RefVec.get_cast, Ref.cast_eq]
        rw [goCache_denote_eq]
        exact hinv
      · simp [Ref.hgate]
    · intro idx hidx
      rw [goCache_denote_eq]
      apply goCache_Inv_of_Inv
      exact hinv
termination_by idx => (sizeOf expr, 0, idx)

end

end bitblast

theorem bitblast_aig_IsPrefix (aig : AIG BVBit) (input : WithCache (BVExpr w) aig) :
    IsPrefix aig.decls (bitblast aig input).result.val.aig.decls := by
  apply IsPrefix.of
  · intros
    apply bitblast_decl_eq
  · intros
    apply (bitblast aig input).result.property

theorem bitblast_denote_mem_prefix (aig : AIG BVBit) (input : WithCache (BVExpr w) aig)
    (assign : Assignment) (start : Nat) (hstart) :
    ⟦
      (bitblast aig input).result.val.aig,
      ⟨start, inv, by apply Nat.lt_of_lt_of_le; exact hstart; apply (bitblast aig input).result.property⟩,
      assign.toAIGAssignment
    ⟧
      =
    ⟦aig, ⟨start, inv, hstart⟩, assign.toAIGAssignment⟧ := by
  apply denote.eq_of_isPrefix (entry := ⟨aig, start, inv, hstart⟩)
  apply bitblast_aig_IsPrefix

theorem bitblast_Inv_of_Inv (input : WithCache (BVExpr w) aig)
    (hinv : Cache.Inv assign aig input.cache) :
    Cache.Inv assign (bitblast aig input).result.val.aig (bitblast aig input).cache := by
  unfold bitblast
  apply bitblast.goCache_Inv_of_Inv
  exact hinv

theorem denote_bitblast (aig : AIG BVBit) (input : WithCache (BVExpr w) aig) (assign : Assignment)
    (hinv : Cache.Inv assign aig input.cache) :
    ∀ (idx : Nat) (hidx : idx < w),
        ⟦(bitblast aig input).result.val.aig, (bitblast aig input).result.val.vec.get idx hidx, assign.toAIGAssignment⟧
          =
        (input.val.eval assign).getLsbD idx
    := by
  intros
  rw [← bitblast.goCache_val_eq_bitblast]
  rw [bitblast.goCache_denote_eq]
  exact hinv

end BVExpr

end Std.Tactic.BVDecide
