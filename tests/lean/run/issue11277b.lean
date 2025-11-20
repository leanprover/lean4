/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Var
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.ShiftRight
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Append
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Replicate
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Extract
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.RotateLeft
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.RotateRight
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Mul
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Umod
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Reverse
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Clz

public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Var
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.ShiftRight
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Append
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Replicate
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Extract
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.RotateLeft
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.RotateRight
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Mul
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Umod
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Reverse
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Clz

set_option Elab.async false

@[expose] public section

/-!
This module contains the implementation of a bitblaster for `BitVec` expressions (`BVExpr`).
That is, expressions that evaluate to `BitVec` again. Its used as a building block in bitblasting
general `BitVec` problems with boolean substructure.
-/

namespace Std.Tactic.BVDecide

open Std.Sat

namespace BVExpr

structure Cache.Key where
  w : Nat
  expr : BVExpr w
  deriving DecidableEq

instance : Hashable Cache.Key where
  -- The width is already mixed into the hash of `key.expr` which is completely cached.
  hash key := hash key.expr

structure Cache (aig : AIG BVBit) where
  map : Std.DHashMap Cache.Key (fun k => Vector AIG.Fanin k.w)
  hbound : ∀ k (h1 : k ∈ map), ∀ (h2 : i < k.1), (map.get k h1)[i].gate < aig.decls.size

@[inline]
def Cache.empty : Cache aig :=
  ⟨{}, by simp⟩

@[inline]
def Cache.insert (cache : Cache aig) (expr : BVExpr w) (refs : AIG.RefVec aig w) :
    Cache aig :=
  let ⟨map, hbound⟩ := cache
  have := by
    intro i k hk h2
    rw [Std.DHashMap.get_insert]
    split
    next heq =>
      rcases k with ⟨w, expr⟩
      simp only [beq_iff_eq, Key.mk.injEq] at heq
      rcases heq with ⟨heq1, heq2⟩
      symm at heq1
      subst heq1
      have := refs.hrefs h2
      rw [getElem_congr_coll]
      · exact this
      · simp
    · apply hbound
  ⟨map.insert ⟨w, expr⟩ refs.refs, this⟩

@[inline]
def Cache.get? (cache : Cache aig) (expr : BVExpr w) : Option (AIG.RefVec aig w) :=
  match h : cache.map.get? ⟨w, expr⟩ with
  | some refs =>
    have : ⟨w, expr⟩ ∈ cache.map := by
      rw [Std.DHashMap.mem_iff_contains, Std.DHashMap.contains_eq_isSome_get?]
      simp [h]
    have : cache.map.get ⟨w, expr⟩ this = refs := by
      rw [Std.DHashMap.get?_eq_some_get (h := this)] at h
      simpa using h
    have := by
      intro i hi
      rw [← this]
      apply cache.hbound
    some ⟨refs, this⟩
  | none => none

@[inline]
def Cache.cast (cache : Cache aig1) (h : aig1.decls.size ≤ aig2.decls.size) :
    Cache aig2 :=
  let ⟨map, hbound⟩ := cache
  have := by
    intro i k hk h2
    apply Nat.lt_of_lt_of_le
    · apply hbound
    · exact h
  ⟨map, this⟩

structure WithCache (α : Type u) (aig : AIG BVBit) where
  val : α
  cache : Cache aig

structure Return (aig : AIG BVBit) (w : Nat) where
  result : AIG.ExtendingRefVecEntry aig w
  cache : Cache result.val.aig

set_option maxHeartbeats 400000 in
def bitblast (aig : AIG BVBit) (input : WithCache (BVExpr w) aig) : Return aig w :=
  let ⟨expr, cache⟩ := input
  goCache aig expr cache
where
  goCache {w : Nat} (aig : AIG BVBit) (expr : BVExpr w) (cache : Cache aig) : Return aig w :=
    match cache.get? expr with
    | some vec =>
      ⟨⟨⟨aig, vec⟩, Nat.le_refl ..⟩, cache⟩
    | none =>
      let ⟨result, cache⟩ := go aig expr cache
      ⟨result, cache.insert expr result.val.vec⟩
  termination_by (sizeOf expr, 1)

  go {w : Nat} (aig : AIG BVBit) (expr : BVExpr w) (cache : Cache aig) : Return aig w :=
    match expr with
    -- | x@(.var a) =>
    | (.var a) =>
      let res := bitblast.blastVar aig ⟨a⟩
      have := AIG.LawfulVecOperator.le_size (f := bitblast.blastVar) ..
      let cache := cache.cast this
      ⟨⟨res, this⟩, cache⟩
    | .const val =>
      let res := bitblast.blastConst aig val
      ⟨⟨⟨aig, res⟩, by simp⟩, cache⟩
    | .bin lhsExpr op rhsExpr =>
      let ⟨⟨⟨aig, lhs⟩, hlaig⟩, cache⟩ := goCache aig lhsExpr cache
      let ⟨⟨⟨aig, rhs⟩, hraig⟩, cache⟩ := goCache aig rhsExpr cache
      let lhs := lhs.cast <| by
        dsimp only at hlaig hraig
        omega
      match op with
      | .and =>
         let res := AIG.RefVec.zip aig ⟨lhs, rhs⟩ AIG.mkAndCached
         have := by
           apply AIG.RefVec.zip_le_size_of_le_aig_size
           dsimp only at hlaig hraig
           omega
         ⟨⟨res, this⟩, cache.cast (AIG.RefVec.zip_le_size ..)⟩
      | .or =>
         let res := AIG.RefVec.zip aig ⟨lhs, rhs⟩ AIG.mkOrCached
         have := by
           apply AIG.RefVec.zip_le_size_of_le_aig_size
           dsimp only at hlaig hraig
           omega
         ⟨⟨res, this⟩, cache.cast (AIG.RefVec.zip_le_size ..)⟩
      | .xor =>
         let res := AIG.RefVec.zip aig ⟨lhs, rhs⟩ AIG.mkXorCached
         have := by
           apply AIG.RefVec.zip_le_size_of_le_aig_size
           dsimp only at hlaig hraig
           omega
         ⟨⟨res, this⟩, cache.cast (AIG.RefVec.zip_le_size ..)⟩
      | .add =>
        let res := bitblast.blastAdd aig ⟨lhs, rhs⟩
        have := by
          apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := bitblast.blastAdd)
          dsimp only at hlaig hraig
          omega
        ⟨⟨res, this⟩, cache.cast (AIG.LawfulVecOperator.le_size (f := bitblast.blastAdd) ..)⟩
      | .mul =>
        let res := bitblast.blastMul aig ⟨lhs, rhs⟩
        have := by
          apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := bitblast.blastMul)
          dsimp only at hlaig hraig
          omega
        ⟨⟨res, this⟩, cache.cast (AIG.LawfulVecOperator.le_size (f := bitblast.blastMul) ..)⟩
      | .udiv =>
        let res := bitblast.blastUdiv aig ⟨lhs, rhs⟩
        have := by
          apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := bitblast.blastUdiv)
          dsimp only at hlaig hraig
          omega
        ⟨⟨res, this⟩, cache.cast (AIG.LawfulVecOperator.le_size (f := bitblast.blastUdiv) ..)⟩
      | .umod =>
        let res := bitblast.blastUmod aig ⟨lhs, rhs⟩
        have := by
          apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := bitblast.blastUmod)
          dsimp only at hlaig hraig
          omega
        ⟨⟨res, this⟩, cache.cast (AIG.LawfulVecOperator.le_size (f := bitblast.blastUmod) ..)⟩
    | .un op expr =>
      let ⟨⟨⟨eaig, evec⟩, heaig⟩, cache⟩ := goCache aig expr cache
      match op with
      | .not =>
        let res := bitblast.blastNot eaig evec
        have := by
          apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := bitblast.blastNot)
          dsimp only at heaig
          omega
        ⟨⟨res, this⟩, cache.cast (AIG.LawfulVecOperator.le_size (f := bitblast.blastNot) ..)⟩
      | .rotateLeft distance =>
        let res := bitblast.blastRotateLeft eaig ⟨evec, distance⟩
        have := by
          apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := bitblast.blastRotateLeft)
          dsimp only at heaig
          assumption
        ⟨⟨res, this⟩, cache.cast (AIG.LawfulVecOperator.le_size (f := bitblast.blastRotateLeft) ..)⟩
      | .rotateRight distance =>
        let res := bitblast.blastRotateRight eaig ⟨evec, distance⟩
        have := by
          apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := bitblast.blastRotateRight)
          dsimp only at heaig
          assumption
        ⟨⟨res, this⟩, cache.cast (AIG.LawfulVecOperator.le_size (f := bitblast.blastRotateRight) ..)⟩
      | .arithShiftRightConst distance =>
        let res := bitblast.blastArithShiftRightConst eaig ⟨evec, distance⟩
        have := by
          apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := bitblast.blastArithShiftRightConst)
          dsimp only at heaig
          assumption
        ⟨⟨res, this⟩, cache.cast (AIG.LawfulVecOperator.le_size (f := bitblast.blastArithShiftRightConst) ..)⟩
      | .reverse =>
        let res := bitblast.blastReverse eaig evec
        have := by
          apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := bitblast.blastReverse)
          dsimp only at heaig
          omega
        ⟨⟨res, this⟩, cache.cast (AIG.LawfulVecOperator.le_size (f := bitblast.blastReverse) ..)⟩
      | .clz =>
        let res := bitblast.blastClz eaig evec
        have := by
          apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := bitblast.blastClz)
          omega
        ⟨⟨res, this⟩, cache.cast (AIG.LawfulVecOperator.le_size (f := bitblast.blastClz) ..)⟩
    | .append lhs rhs h =>
      let ⟨⟨⟨aig, lhs⟩, hlaig⟩, cache⟩ := goCache aig lhs cache
      let ⟨⟨⟨aig, rhs⟩, hraig⟩, cache⟩ := goCache aig rhs cache
      let lhs := lhs.cast <| by
        dsimp only at hlaig hraig
        omega
      let res := bitblast.blastAppend aig ⟨lhs, rhs, by rw [Nat.add_comm, h]⟩
      have := by
        apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := bitblast.blastAppend)
        dsimp only at hlaig hraig
        omega
      ⟨⟨res, this⟩, cache.cast (AIG.LawfulVecOperator.le_size (f := bitblast.blastAppend) ..)⟩
    | .replicate n expr h =>
      let ⟨⟨⟨aig, expr⟩, haig⟩, cache⟩ := goCache aig expr cache
      let res := bitblast.blastReplicate aig ⟨n, expr, h⟩
      have := by
        apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := bitblast.blastReplicate)
        dsimp only at haig
        assumption
      ⟨⟨res, this⟩, cache.cast (AIG.LawfulVecOperator.le_size (f := bitblast.blastReplicate) ..)⟩
    | .extract start len expr =>
      let ⟨⟨⟨eaig, evec⟩, heaig⟩, cache⟩ := goCache aig expr cache
      let res := bitblast.blastExtract eaig ⟨evec, start⟩
      have := by
        apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := bitblast.blastExtract)
        dsimp only at heaig
        exact heaig
      ⟨⟨res, this⟩, cache.cast (AIG.LawfulVecOperator.le_size (f := bitblast.blastExtract) ..)⟩
    | .shiftLeft lhs rhs =>
      let ⟨⟨⟨aig, lhs⟩, hlaig⟩, cache⟩ := goCache aig lhs cache
      let ⟨⟨⟨aig, rhs⟩, hraig⟩, cache⟩ := goCache aig rhs cache
      let lhs := lhs.cast <| by
        dsimp only at hlaig hraig
        omega
      let res := bitblast.blastShiftLeft aig ⟨_, lhs, rhs⟩
      have := by
        apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := bitblast.blastShiftLeft)
        dsimp only at hlaig hraig
        omega
      ⟨⟨res, this⟩, cache.cast (AIG.LawfulVecOperator.le_size (f := bitblast.blastShiftLeft) ..)⟩
    | .shiftRight lhs rhs =>
      let ⟨⟨⟨aig, lhs⟩, hlaig⟩, cache⟩ := goCache aig lhs cache
      let ⟨⟨⟨aig, rhs⟩, hraig⟩, cache⟩ := goCache aig rhs cache
      let lhs := lhs.cast <| by
        dsimp only at hlaig hraig
        omega
      let res := bitblast.blastShiftRight aig ⟨_, lhs, rhs⟩
      have := by
        apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := bitblast.blastShiftRight)
        dsimp only at hlaig hraig
        omega
      ⟨⟨res, this⟩, cache.cast (AIG.LawfulVecOperator.le_size (f := bitblast.blastShiftRight) ..)⟩
    | .arithShiftRight lhs rhs =>
      let ⟨⟨⟨aig, lhs⟩, hlaig⟩, cache⟩ := goCache aig lhs cache
      let ⟨⟨⟨aig, rhs⟩, hraig⟩, cache⟩ := goCache aig rhs cache
      let lhs := lhs.cast <| by
        dsimp only at hlaig hraig
        omega
      let res := bitblast.blastArithShiftRight aig ⟨_, lhs, rhs⟩
      have := by
        apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := bitblast.blastArithShiftRight)
        dsimp only at hlaig hraig
        omega
      ⟨⟨res, this⟩, cache.cast (AIG.LawfulVecOperator.le_size (f := bitblast.blastArithShiftRight) ..)⟩
  termination_by (sizeOf expr, 0)


namespace bitblast

mutual

theorem goCache_decl_eq (aig : AIG BVBit) (expr : BVExpr w) (cache : Cache aig) :
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

theorem go_decl_eq (aig : AIG BVBit) (expr : BVExpr w) (cache : Cache aig) :
    ∀ (idx : Nat) (h1) (h2), (go aig expr cache).result.val.aig.decls[idx]'h2 = aig.decls[idx]'h1 := by
  intro idx h1 h2
  unfold go
  split
  · rw [AIG.LawfulVecOperator.decl_eq (f := blastVar)]
  · simp
  next op lhsExpr rhsExpr =>
    have hl := (goCache aig lhsExpr cache).result.property
    have hr := (goCache (goCache aig lhsExpr cache).1.1.aig rhsExpr (goCache aig lhsExpr cache).cache).result.property
    match op with
    | .and | .or | .xor =>
      rw [AIG.RefVec.zip_decl_eq]
      rw [goCache_decl_eq, goCache_decl_eq]
      · exact Nat.lt_of_lt_of_le h1 hl
      · apply Nat.lt_of_lt_of_le
        · exact h1
        · apply Nat.le_trans <;> assumption
    | .add | .mul | .udiv | .umod =>
      rw [AIG.LawfulVecOperator.decl_eq]
      rw [goCache_decl_eq, goCache_decl_eq]
      · exact Nat.lt_of_lt_of_le h1 hl
      · apply Nat.lt_of_lt_of_le
        · exact h1
        · apply Nat.le_trans <;> assumption
  next op expr =>
    match op with
    | .not | .rotateLeft .. | .rotateRight .. | .arithShiftRightConst .. | .reverse | .clz =>
      rw [AIG.LawfulVecOperator.decl_eq]
      rw [goCache_decl_eq]
      have := (goCache aig expr cache).result.property
      exact Nat.lt_of_lt_of_le h1 this
  next lhsExpr rhsExpr h =>
    have hl := (goCache aig lhsExpr cache).result.property
    have hr := (goCache (goCache aig lhsExpr cache).1.1.aig rhsExpr (goCache aig lhsExpr cache).cache).result.property
    rw [AIG.LawfulVecOperator.decl_eq]
    rw [goCache_decl_eq, goCache_decl_eq]
    · exact Nat.lt_of_lt_of_le h1 hl
    · apply Nat.lt_of_lt_of_le
      · exact h1
      · apply Nat.le_trans <;> assumption
  next inner _ =>
    rw [AIG.LawfulVecOperator.decl_eq (f := blastReplicate)]
    rw [goCache_decl_eq]
    have := (goCache aig inner cache).result.property
    exact Nat.lt_of_lt_of_le h1 this
  next hi lo inner =>
    rw [AIG.LawfulVecOperator.decl_eq (f := blastExtract)]
    rw [goCache_decl_eq]
    have := (goCache aig inner cache).result.property
    exact Nat.lt_of_lt_of_le h1 this
  next rhsExpr lhsExpr =>
    have hl := (goCache aig lhsExpr cache).result.property
    have hr := (goCache (goCache aig lhsExpr cache).1.1.aig rhsExpr (goCache aig lhsExpr cache).cache).result.property
    rw [AIG.LawfulVecOperator.decl_eq (f := blastShiftLeft)]
    rw [goCache_decl_eq, goCache_decl_eq]
    · exact Nat.lt_of_lt_of_le h1 hl
    · apply Nat.lt_of_lt_of_le
      · exact h1
      · apply Nat.le_trans <;> assumption
  next rhsExpr lhsExpr =>
    have hl := (goCache aig lhsExpr cache).result.property
    have hr := (goCache (goCache aig lhsExpr cache).1.1.aig rhsExpr (goCache aig lhsExpr cache).cache).result.property
    rw [AIG.LawfulVecOperator.decl_eq (f := blastShiftRight)]
    rw [goCache_decl_eq, goCache_decl_eq]
    · exact Nat.lt_of_lt_of_le h1 hl
    · apply Nat.lt_of_lt_of_le
      · exact h1
      · apply Nat.le_trans <;> assumption
  next rhsExpr lhsExpr =>
    have hl := (goCache aig lhsExpr cache).result.property
    have hr := (goCache (goCache aig lhsExpr cache).1.1.aig rhsExpr (goCache aig lhsExpr cache).cache).result.property
    rw [AIG.LawfulVecOperator.decl_eq (f := blastArithShiftRight)]
    rw [goCache_decl_eq, goCache_decl_eq]
    · exact Nat.lt_of_lt_of_le h1 hl
    · apply Nat.lt_of_lt_of_le
      · exact h1
      · apply Nat.le_trans <;>  assumption
termination_by (sizeOf expr, 0)

end

end bitblast

theorem bitblast_decl_eq (aig : AIG BVBit) (input : WithCache (BVExpr w) aig) :
    ∀ (idx : Nat) (h1) (h2), (bitblast aig input).result.val.aig.decls[idx]'h2 = aig.decls[idx]'h1 := by
  intros
  unfold bitblast
  apply bitblast.goCache_decl_eq

theorem bitblast_le_size (aig : AIG BVBit) (input : WithCache (BVExpr w) aig) :
    aig.decls.size ≤ (bitblast aig input).result.val.aig.decls.size := by
  exact (bitblast aig input).result.property

theorem bitblast_lt_size_of_lt_aig_size (aig : AIG BVBit) (input : WithCache (BVExpr w) aig)
    (h : x < aig.decls.size) :
    x < (bitblast aig input).result.val.aig.decls.size := by
  apply Nat.lt_of_lt_of_le
  · exact h
  · exact bitblast_le_size aig input

end BVExpr

end Std.Tactic.BVDecide


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
    · sorry
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
    · sorry
  · rw [← hres]
    apply Cache.Inv_cast
    · apply IsPrefix.rfl
    · sorry
  next op lhsExpr rhsExpr =>
    dsimp only at hres
    match op with
    | .and | .or | .xor =>
      dsimp only at hres
      rw [← hres]
      apply Cache.Inv_cast
      · apply RefVec.IsPrefix_zip
      · apply goCache_Inv_of_Inv
        sorry
    | .add | .mul | .udiv | .umod =>
      dsimp only at hres
      rw [← hres]
      apply Cache.Inv_cast
      · apply LawfulVecOperator.isPrefix_aig
      · apply goCache_Inv_of_Inv
        sorry
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
  next heq =>
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
      · rw [goCache_denote_mem_prefix (hstart := Ref.hgate _)]
        rw [goCache_denote_eq]
        exact hinv
      · rw [goCache_denote_eq]
        apply goCache_Inv_of_Inv
        exact hinv
    · rw [← hres]
      simp only [RefVec.denote_zip, RefVec.get_cast, Ref.cast_eq, denote_mkOrCached, eval_bin,
        BVBinOp.eval_or, BitVec.getLsbD_or]
      congr 1
      · rw [goCache_denote_mem_prefix (hstart := Ref.hgate _)]
        rw [goCache_denote_eq]
        exact hinv
      · rw [goCache_denote_eq]
        apply goCache_Inv_of_Inv
        exact hinv
    · rw [← hres]
      simp only [RefVec.denote_zip, RefVec.get_cast, Ref.cast_eq, denote_mkXorCached, eval_bin,
        BVBinOp.eval_xor, BitVec.getLsbD_xor]
      congr 1
      · rw [goCache_denote_mem_prefix (hstart := Ref.hgate _)]
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
        rw [goCache_denote_eq]
        · apply BitVec.getLsbD_eq_getElem
        · exact hinv
    · rw [← hres]
      simp only [denote_blastRotateRight, eval_un, BVUnOp.eval_rotateRight, hidx,
        BitVec.getLsbD_eq_getElem, BitVec.getElem_rotateRight]
      split
      all_goals
        rw [goCache_denote_eq]
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
      simp only [eval_un, BVUnOp.eval_clz, BitVec.clz]
      rw [denote_blastClz]
      intro idx hidx
      rw [goCache_denote_eq]
      exact hinv
  next h =>
    subst h
    rw [← hres]
    simp only [denote_blastAppend, RefVec.get_cast, Ref.cast_eq, eval_append, BitVec.getLsbD_append]
    split
    · rw [goCache_denote_eq]
      apply goCache_Inv_of_Inv
      exact hinv
    · rw [goCache_denote_mem_prefix (hstart := Ref.hgate _)]
      rw [goCache_denote_eq]
      exact hinv
  next h =>
    subst h
    rw [← hres]
    simp only [denote_blastReplicate, eval_replicate, hidx, BitVec.getLsbD_eq_getElem,
      BitVec.getElem_replicate]
    split
    next h =>
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

end BVExpr

end Std.Tactic.BVDecide

#exit
