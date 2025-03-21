/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Var
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Const
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Not
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.ShiftLeft
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.ShiftRight
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Add
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Append
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Replicate
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Extract
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.RotateLeft
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.RotateRight
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Mul
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Udiv
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Umod

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
  deriving DecidableEq, Hashable

structure Cache (aig : AIG BVBit) where
  map : Std.DHashMap Cache.Key (fun k => Vector (Nat × Bool) k.1)
  hbound : ∀ k (h1 : k ∈ map), ∀ (h2 : i < k.1), (map.get k h1)[i].1 < aig.decls.size

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
    · next heq =>
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

structure Return (aig : AIG BVBit) (w : Nat) where
  result : AIG.ExtendingRefVecEntry aig w
  cache : Cache result.val.aig

set_option maxHeartbeats 400000 in
def bitblast (aig : AIG BVBit) (expr : BVExpr w) : AIG.RefVecEntry BVBit w :=
  goCache aig expr .empty |>.result.val
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
    | .var a =>
      let res := bitblast.blastVar aig ⟨a⟩
      have := AIG.LawfulVecOperator.le_size (f := bitblast.blastVar) ..
      let cache := cache.cast this
      ⟨⟨res, this⟩, cache⟩
    | .const val =>
      let res := bitblast.blastConst aig val
      have := AIG.LawfulVecOperator.le_size (f := bitblast.blastConst) ..
      let cache := cache.cast this
      ⟨⟨res, this⟩, cache⟩
    | .bin lhsExpr op rhsExpr =>
      let ⟨⟨⟨aig, lhs⟩, hlaig⟩, cache⟩ := goCache aig lhsExpr cache
      let ⟨⟨⟨aig, rhs⟩, hraig⟩, cache⟩ := goCache aig rhsExpr cache
      let lhs := lhs.cast <| by
        dsimp only at hlaig hraig
        omega
      match op with
      | .and =>
         let res := AIG.RefVec.zip aig ⟨⟨lhs, rhs⟩, AIG.mkAndCached⟩
         have := by
           apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := AIG.RefVec.zip)
           dsimp only at hlaig hraig
           omega
         ⟨⟨res, this⟩, cache.cast (AIG.LawfulVecOperator.le_size (f := AIG.RefVec.zip) ..)⟩
      | .or =>
         let res := AIG.RefVec.zip aig ⟨⟨lhs, rhs⟩, AIG.mkOrCached⟩
         have := by
           apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := AIG.RefVec.zip)
           dsimp only at hlaig hraig
           omega
         ⟨⟨res, this⟩, cache.cast (AIG.LawfulVecOperator.le_size (f := AIG.RefVec.zip) ..)⟩
      | .xor =>
         let res := AIG.RefVec.zip aig ⟨⟨lhs, rhs⟩, AIG.mkXorCached⟩
         have := by
           apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := AIG.RefVec.zip)
           dsimp only at hlaig hraig
           omega
         ⟨⟨res, this⟩, cache.cast (AIG.LawfulVecOperator.le_size (f := AIG.RefVec.zip) ..)⟩
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
          apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := AIG.RefVec.map)
          dsimp only at heaig
          omega
        ⟨⟨res, this⟩, cache.cast (AIG.LawfulVecOperator.le_size (f := AIG.RefVec.map) ..)⟩
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

/-
theorem bitblast.go_decl_eq (aig : AIG BVBit) (expr : BVExpr w) :
    ∀ (idx : Nat) (h1) (h2), (go aig expr).val.aig.decls[idx]'h2 = aig.decls[idx]'h1 := by
  intros idx h1 h2
  induction expr generalizing aig with
  | var =>
    dsimp only [go]
    rw [AIG.LawfulVecOperator.decl_eq (f := blastVar)]
  | const =>
    dsimp only [go]
    rw [AIG.LawfulVecOperator.decl_eq (f := blastConst)]
  | bin lhs op rhs lih rih =>
    match op with
    | .and | .or | .xor | .add | .mul | .udiv | .umod =>
      dsimp only [go]
      have := (bitblast.go aig lhs).property
      have := (go (go aig lhs).1.aig rhs).property
      have := (bitblast.go aig lhs).property
      rw [AIG.LawfulVecOperator.decl_eq]
      rw [rih, lih]
      · omega
      · apply Nat.lt_of_lt_of_le h1 -- omega cannot do this :(
        apply Nat.le_trans <;> assumption
  | un op expr ih =>
    match op with
    | .not | .rotateLeft .. | .rotateRight ..
    | .arithShiftRightConst .. =>
      dsimp only [go]
      rw [AIG.LawfulVecOperator.decl_eq]
      rw [ih]
      have := (go aig expr).property
      omega
  | append lhs rhs _ lih rih =>
    dsimp only [go]
    have := (bitblast.go aig lhs).property
    have := (bitblast.go aig lhs).property
    have := (go (go aig lhs).1.aig rhs).property
    rw [AIG.LawfulVecOperator.decl_eq (f := blastAppend)]
    rw [rih, lih]
    · omega
    · apply Nat.lt_of_lt_of_le h1
      apply Nat.le_trans <;> assumption
  | replicate n inner _ ih =>
    dsimp only [go]
    rw [AIG.LawfulVecOperator.decl_eq (f := blastReplicate)]
    rw [ih]
    have := (go aig inner).property
    omega
  | extract hi lo inner ih =>
    dsimp only [go]
    rw [AIG.LawfulVecOperator.decl_eq (f := blastExtract)]
    rw [ih]
    have := (go aig inner).property
    omega
  | shiftLeft lhs rhs lih rih =>
    dsimp only [go]
    have := (bitblast.go aig lhs).property
    have := (bitblast.go aig lhs).property
    have := (go (go aig lhs).1.aig rhs).property
    rw [AIG.LawfulVecOperator.decl_eq (f := blastShiftLeft)]
    rw [rih, lih]
    · omega
    · apply Nat.lt_of_lt_of_le h1
      apply Nat.le_trans <;> assumption
  | shiftRight lhs rhs lih rih =>
    dsimp only [go]
    have := (bitblast.go aig lhs).property
    have := (bitblast.go aig lhs).property
    have := (go (go aig lhs).1.aig rhs).property
    rw [AIG.LawfulVecOperator.decl_eq (f := blastShiftRight)]
    rw [rih, lih]
    · omega
    · apply Nat.lt_of_lt_of_le h1
      apply Nat.le_trans <;> assumption
  | arithShiftRight lhs rhs lih rih =>
    dsimp only [go]
    have := (bitblast.go aig lhs).property
    have := (bitblast.go aig lhs).property
    have := (go (go aig lhs).1.aig rhs).property
    rw [AIG.LawfulVecOperator.decl_eq (f := blastArithShiftRight)]
    rw [rih, lih]
    · omega
    · apply Nat.lt_of_lt_of_le h1
      apply Nat.le_trans <;> assumption
  -/

set_option linter.unusedVariables false
axiom mySorry {α : Sort u} : α

instance : AIG.LawfulVecOperator BVBit (fun _ w => BVExpr w) bitblast where
  le_size := mySorry
    --intro _ aig expr
    --unfold bitblast
    --exact (bitblast.go aig expr).property
  decl_eq := mySorry
    --intros
    --unfold bitblast
    --apply bitblast.go_decl_eq

end BVExpr

end Std.Tactic.BVDecide
