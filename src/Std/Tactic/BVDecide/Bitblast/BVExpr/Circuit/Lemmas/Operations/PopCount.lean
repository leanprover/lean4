/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luisa Cicolini, Siddharth Bhat, Henrik Böving
-/
module

prelude
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Basic
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.PopCount
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Const
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Sub
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Eq
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.ZeroExtend
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Extract

@[expose] public section

/-!
This module contains the verification of the bitblaster for `BitVec.popCountAuxRec` from
`Impl.Operations.popCount`. We prove that the accumulator of the `go` function
at step`n` represents the portion of the `ite` nodes in the AIG constructed for
bits `0` until `n`.
-/

namespace Std.Tactic.BVDecide

open Std.Sat
open Std.Sat.AIG

variable [Hashable α] [DecidableEq α]

namespace BVExpr

namespace bitblast
namespace blastPopCount

theorem push_denote_eq {aigOld aigNew : AIG α} {n w : Nat}
  (acc : RefVecVec aigOld w n) (elem : AIG.RefVec aigNew w)
  (haig : aigOld.decls.size ≤ aigNew.decls.size)
  (assign : α → Bool) (l : List (BitVec w)) (bv : BitVec w)
  (hlen : l.length = n)
  (hvec : ∀ (idx1 : Nat) (hidx1 : idx1 < n),
    ∀ (idx2 : Nat) (hidx2 : idx2 < w),
      ⟦aigNew, ((acc.cast haig).vec.get ⟨idx1, hidx1⟩).get idx2 hidx2, assign⟧ =
      (l.get ⟨idx1, by omega⟩).getLsbD idx2)
  (helem : ∀ (idx1 : Nat) (hidx1 : idx1 < w),
    ⟦aigNew, elem.get idx1 hidx1, assign⟧ = (bv.getLsbD idx1))
  : ∀ (idx1 : Nat) (hidx1 : idx1 < n + 1),
    ∀ (idx2 : Nat) (hidx2 : idx2 < w),
      ⟦aigNew, ((acc.push elem haig).vec.get ⟨idx1, hidx1⟩).get idx2 hidx2, assign⟧ =
      ((l.concat bv).get ⟨idx1, by have := List.length_concat (as := l) (a := bv); omega⟩).getLsbD idx2 := by
  intros idx1 hidx1 idx2 hidx2
  by_cases hidxlt : idx1 < n
  · have : (acc.push elem haig).vec.get ⟨idx1, (by omega)⟩ =
      ((acc.cast haig).vec.get ⟨idx1, (by omega)⟩) := by
      unfold RefVecVec.push
      exact Vector.getElem_push_lt (x := elem) (i := idx1) (xs := (Vector.map (fun refVec => refVec.cast haig) acc.vec)) hidxlt
    simp only [this]
    have : (l.concat bv).get ⟨idx1, by simp [hlen]; omega⟩ = l.get ⟨idx1, by simp [hlen]; omega⟩ := by
      have hlen' := List.length_concat (as := l) (a := bv)
      have := List.getElem_append_left (as := l) (i := idx1) (bs := [bv]) (by simp [hlen]; omega) (h' := by simp; omega)
      simp [this]
    rw [this]
    simp [hvec]
  · have : idx1 = n := by omega
    simp only  [this] at *
    have : (acc.push elem haig).vec.get ⟨n, (by omega)⟩ = elem := by
      unfold RefVecVec.push
      exact Vector.getElem_push_last (x := elem) (n := n)
        (xs := (Vector.map (fun refVec => refVec.cast haig) acc.vec))
    simp only [this]
    have : (l.concat bv).get ⟨n, by simp [hlen]⟩ = bv := by
      have h2 := List.getElem_concat_length (l := l) (i := n) (a := bv) (by simp [hlen])
      specialize h2 (by simp [hlen])
      simp [h2]
    rw [this]
    simp [helem]

theorem blastExtractAndExtend_denote_eq (aig : AIG α) (xc : AIG.RefVec aig w) (x : BitVec w) (start : Nat)
    (hx : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, xc.get idx hidx, assign⟧ = x.getLsbD idx) :
  ∀ (idx : Nat) (hidx : idx < w),
    ⟦
      (blastExtractAndExtend aig xc start).aig,
      (blastExtractAndExtend aig xc start).vec.get idx hidx,
      assign
     ⟧ = (BitVec.zeroExtend w (BitVec.extractLsb start start x)).getLsbD idx := by
  intros idx hidx
  generalize hext: blastExtractAndExtend aig xc start = res
  unfold blastExtractAndExtend at hext
  dsimp at hext
  rw [← hext]
  simp [denote_blastZeroExtend]
  split
  · by_cases hidx0 : idx = 0
    · simp [hidx0]
      simp [show 0 < w by omega]
      apply hx
    · simp [hidx0]
  · intros
    simp [show w ≤ start + idx by omega]

theorem BitVec.extractAndExtendPopulateAux_get
    (i : Nat)
    (hi : i < w)
    (x : BitVec w)
    (hw : 0 < w) :
  let res := (BitVec.extractAndExtendPopulateAux 0 x [] (by omega) (by simp))
  res.val[i]'(by have := res.property; simp_all) = BitVec.setWidth w (BitVec.extractLsb' i 1 x) := by
  induction i
  · case zero =>
    sorry
  · case succ n ihn =>
    simp
    unfold BitVec.extractAndExtendPopulateAux
    simp
    sorry

theorem blastExtractAndExtendPopulate_denote_eq'
  (assign : α → Bool)
  (aigAcc : AIG α) (start w : Nat) (xc : AIG.RefVec aigAcc w) (x : BitVec w) (acc : RefVecVec aigAcc w start) (hw : start + 1 < w)
  (hacc' : ∀ (idx1 : Nat) (hidx1 : idx1 < start),
            ∀ (idx2 : Nat) (hidx2 : idx2 < w),
              let newElem := blastExtractAndExtend aigAcc xc (start)
              ⟦newElem.aig, ((acc.cast (by apply extractAndExtend_le_size)).vec.get ⟨idx1, hidx1⟩).get idx2 hidx2, assign⟧ =
              ((BitVec.extractAndExtendPopulateAux 0 x [] (by omega) (by simp)).val.get ⟨idx1, by simp [(BitVec.extractAndExtendPopulateAux 0 x [] (by omega) (by simp)).property]; exact Nat.lt_trans hidx1 (by omega)⟩).getLsbD idx2)
  (hx : ∀ (idx : Nat) (hidx : idx < w), ⟦aigAcc, xc.get idx hidx, assign⟧ = x.getLsbD idx)
   :
    ∀ (idx1 : Nat) (hidx1 : idx1 < start + 1),
      ∀ (idx2 : Nat) (hidx2 : idx2 < w),
      ⟦
        (blastExtractAndExtend aigAcc xc start).aig,
        (((acc.cast (aig2 := (blastExtractAndExtend aigAcc xc (start)).aig)
          (by apply extractAndExtend_le_size)).push (blastExtractAndExtend aigAcc xc (start)).vec (by omega)).vec.get ⟨idx1, by omega⟩).get idx2 hidx2,
        assign
      ⟧ =
        let bvRes := BitVec.extractAndExtendPopulateAux 0 x [] (by omega) (by simp)
      (bvRes.val.get ⟨idx1, by simp [bvRes.property]; omega⟩).getLsbD idx2 := by
  -- Introduce a variable `ext` for `blastExtractAndExtend`
  intros idx1 hidx1 idx2 hidx2
  let elem := blastExtractAndExtend aigAcc xc start
  let bvRes := BitVec.extractAndExtendPopulateAux 0 x [] (by omega) (by simp)
  let currList := bvRes.val.extract (start := 0) (stop := start)
  let currElem := bvRes.val.get ⟨start, by omega⟩
  rw [push_denote_eq (l := currList) (bv := currElem)]
  · simp
    by_cases h1 : idx1 = start
    · -- inspecting the last element of the list
      simp [h1]
      have h2 := List.getElem_concat_length (i := start) (a := currElem) (l := currList) (by simp [currList]; omega)
      specialize h2 (by simp [currList]; omega)
      simp [h2]
      let res' := BitVec.extractAndExtendPopulateAux 0 x [] (by omega) BitVec.extractAndExtendPopulateAux_get._proof_3
      have := BitVec.extractAndExtendPopulateAux_get (i := start) (x := x)
        (hi := by omega) (by omega)
      simp at this
      rw [this]
      simp only [currElem]
      simp
      rw [BitVec.extractAndExtendPopulateAux_get (i := start) (x := x) (by have := bvRes; omega) (by omega)]
      simp
    · -- inspecting an element that was already in the acc
      have hl := List.getElem_append_left (as := currList) (bs := [currElem]) (i := idx1) (h' := by simp; omega)
      rw [hl (by simp [currList];  omega)]
      let res := BitVec.extractAndExtendPopulateAux 0 x [] (by omega) BitVec.extractAndExtendPopulateAux_get._proof_3
      rw [BitVec.extractAndExtendPopulateAux_get (i := idx1) (x := x) (by have := res; omega) (by omega)]
      have : idx1 < start := by omega
      simp [currList]
      simp [bvRes]
      rw [BitVec.extractAndExtendPopulateAux_get (i := idx1) (x := x) (by have := bvRes; omega) (by omega)]
      simp
  · simp [currList]; omega
  · intros idx1 hidx1 idx2 hidx2
    simp [currList, bvRes]
    simp at hacc'
    specialize hacc' idx1 hidx1 idx2 hidx2
    have hproof1 : aigAcc.decls.size ≤ (blastExtractAndExtend aigAcc xc start).aig.decls.size := by apply extractAndExtend_le_size
    have hproof2 : (blastExtractAndExtend aigAcc xc start).aig.decls.size ≤ (blastExtractAndExtend aigAcc xc start).aig.decls.size := by omega
    have hcast' : ((acc.cast hproof1).cast hproof2) = acc.cast (by apply extractAndExtend_le_size) := by simp [RefVecVec.cast]
    rw [hcast']
    apply hacc'
  · intros idx hidx
    rw [blastExtractAndExtend_denote_eq (aig := aigAcc) (xc := xc) (x := x) (start := start) (assign := assign) (hx := hx)]
    ·
      simp
      by_cases h1 : idx = 0
      · -- this is the only bit that gets actually populated with a meaningful value
        simp [h1, show 0 < w by omega]
        simp [currElem]
        simp [bvRes]
        have :=  BitVec.extractAndExtendPopulateAux_get (i := start) (x := x) (by omega) (by omega)
        simp [this]
      · -- everythign else is the result of zExt
        simp [h1]
        simp [currElem, bvRes]
        have :=  BitVec.extractAndExtendPopulateAux_get (i := start) (x := x) (by omega) (by omega)
        simp [this]
        intros
        omega

theorem blastExtractAndExtendPopulate_denote_eq
  -- blastExtractAndExtendPopulate inputs
  (aig : AIG α) (start : Nat) (xc : AIG.RefVec aig w) (x : BitVec w) (acc : RefVecVec aig w start) (hw : start ≤ w)
  -- denotation
  (initVec : RefVecVec aig w 0 := {vec : Vector (AIG.RefVec aig w) 0 := Vector.emptyWithCapacity 0})
  (hx : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, xc.get idx hidx, assign⟧ = x.getLsbD idx)
  (assign : α → Bool) :
    ∀ (idx1 : Nat) (hidx1 : idx1 < w),
      ∀ (idx2 : Nat) (hidx2 : idx2 < w),
      ⟦
        (blastExtractAndExtendPopulate aig 0 xc initVec (by omega)).aig,
        ((blastExtractAndExtendPopulate aig 0 xc initVec (by omega)).vec.vec.get ⟨idx1,hidx1⟩).get idx2 hidx2,
        assign
      ⟧ =
      ((BitVec.extractAndExtendPopulateAux 0 x [] (by omega) (by simp)).val.get ⟨idx1, by
        have := (BitVec.extractAndExtendPopulateAux 0 x [] (by omega) (by simp)).property
        simp [this]
        omega
        ⟩).getLsbD idx2 := by
  intros idx1 hidx1 idx2 hidx2
  generalize hext: blastExtractAndExtendPopulate aig 0 xc initVec (by omega) = res
  unfold blastExtractAndExtendPopulate at hext
  dsimp at hext
  split at hext
  · case isTrue h =>
    rw [← hext]
    dsimp


    sorry
  · case isFalse h => omega

end blastPopCount

@[simp]
theorem denote_blastPopCount (aig : AIG α) (xc : RefVec aig w) (x : BitVec w) (assign : α → Bool)
      (hx : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, xc.get idx hidx, assign⟧ = x.getLsbD idx)
      :
      ∀ (idx : Nat) (hidx : idx < w),
        ⟦(blastPopCount aig xc).aig, (blastPopCount aig xc).vec.get idx hidx, assign⟧
          =
        (BitVec.popCountAuxRec x 0 0).getLsbD idx := by
  sorry

end bitblast
end BVExpr

end Std.Tactic.BVDecide
