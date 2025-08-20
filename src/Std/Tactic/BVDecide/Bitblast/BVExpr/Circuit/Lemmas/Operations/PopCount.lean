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

/-- Casting `RefVecVec` twice is the same as casting once. -/
theorem RefVecVec.cast_cast {aig1 aig2 : AIG α} (s : RefVecVec aig1 lenWords len) (h : aig1.decls.size ≤ aig2.decls.size) :
    (s.cast h).cast (aig2 := aig2) (by omega) = s.cast h := by
  simp [RefVecVec.cast]

/-- Getting the `idx`-th element of the `vec` of `RefVecVec` after setting it retrieves the same element. -/
theorem RefVecVec.get_set_eq {aigOld aigNew : AIG α} {w len : Nat} (idx : Nat) (s : RefVecVec aigOld w len) (elem : RefVec aigNew w)
      (h : idx < len) (h' : aigOld.decls.size ≤ aigNew.decls.size) :
    (RefVecVec.set idx s elem h' h).vec[idx] = elem := by
  simp [RefVecVec.set]

/-- After setting the `idx`-th element of the `vec` of `RefVecVec`, retrieving any element that is not at that index
    is the same as getting that element from the original vector. -/
theorem RefVecVec.get_set {aigOld aigNew : AIG α} {w len : Nat} (idx : Nat) (s : RefVecVec aigOld w len) (elem : RefVec aigNew w)
      (h : idx < len) (h' : aigOld.decls.size ≤ aigNew.decls.size) :
  ∀ (idx' : Nat) (_ : ¬idx' = idx) (hi' : idx' < len),
    (RefVecVec.set idx s elem h' h).vec[idx'] = (s.cast h').vec[idx'] := by
  intros idx1 hidx1 hidx1'
  simp only [RefVecVec.set, Vector.getElem_set, Vector.getElem_map, RefVecVec.cast, ite_eq_right_iff]
  intros
  omega

theorem denote_set {aigOld aigNew : AIG α} {n w : Nat}
  (acc : RefVecVec aigOld w n) (elem : AIG.RefVec aigNew w)
  (idxSet : Nat) (hidxSet : idxSet < n)
  (haig : aigOld.decls.size ≤ aigNew.decls.size)
  (assign : α → Bool) (l : List (BitVec w)) (bv : BitVec w)
  (hlen : l.length = n)
  (hvec : ∀ (idx1 : Nat) (hidx1 : idx1 < n),
    ∀ (idx2 : Nat) (hidx2 : idx2 < w),
      ⟦aigNew, ((acc.cast haig).vec[idx1]).get idx2 hidx2, assign⟧ =
      l[idx1].getLsbD idx2)
  (helem : ∀ (idx1 : Nat) (hidx1 : idx1 < w),
    ⟦aigNew, elem.get idx1 hidx1, assign⟧ = (bv.getLsbD idx1))
  : ∀ (idx1 : Nat) (hidx1 : idx1 < n),
    ∀ (idx2 : Nat) (hidx2 : idx2 < w),
      ⟦aigNew, ((acc.set idxSet elem haig (hidxSet)).vec[idx1]).get idx2 hidx2, assign⟧ =
      ((l.set idxSet bv)[idx1]'(by simp; omega)).getLsbD idx2 := by
  intros idx1 hidx1 idx2 hidx2
  by_cases heq : idxSet = idx1
  · simp [←heq, RefVecVec.get_set_eq idxSet acc elem hidxSet haig, helem]
  · simp only [ne_eq, heq, not_false_eq_true, List.getElem_set_ne]
    rw [RefVecVec.get_set idxSet acc elem hidxSet haig]
    · apply hvec
    · omega

-- theorem denote_cast {aigCurr aigNew : AIG α} {n w : Nat}
--   (acc : RefVecVec aigCurr w n)
--   (haig : aigCurr.decls.size ≤ aigNew.decls.size)
--   (assign : α → Bool) (l : List (BitVec w))
--   (hlen : l.length = n)
--   (hvec : ∀ (idx1 : Nat) (hidx1 : idx1 < n),
--     ∀ (idx2 : Nat) (hidx2 : idx2 < w),
--       ⟦aigCurr, (acc.vec.get ⟨idx1, hidx1⟩).get idx2 hidx2, assign⟧ = (l.get ⟨idx1, (by omega)⟩).getLsbD idx2)
--   : ∀ (idx1 : Nat) (hidx1 : idx1 < n),
--     ∀ (idx2 : Nat) (hidx2 : idx2 < w),
--       ⟦aigNew, (((acc.cast haig)).vec.get ⟨idx1, hidx1⟩).get idx2 hidx2, assign⟧ = l[idx1].getLsbD idx2 := by
--   simp at hvec
--   intros idx1 hidx1 idx2 hidx2
--   specialize hvec idx1 hidx1 idx2 hidx2
--   sorry

-- theorem denote_cast_cast {aigCurr aigNew : AIG α} {n w : Nat}
--   (acc : RefVecVec aigCurr w n)
--   (haig : aigCurr.decls.size ≤ aigNew.decls.size)
--   (haig' : aigNew.decls.size ≤ aigNew.decls.size)
--   (assign : α → Bool) (l : List (BitVec w))
--   (hlen : l.length = n)
--   (hvec : ∀ (idx1 : Nat) (hidx1 : idx1 < n),
--     ∀ (idx2 : Nat) (hidx2 : idx2 < w),
--       ⟦aigCurr, (acc.vec.get ⟨idx1, hidx1⟩).get idx2 hidx2, assign⟧ = (l.get ⟨idx1, (by omega)⟩).getLsbD idx2)
--   : ∀ (idx1 : Nat) (hidx1 : idx1 < n),
--     ∀ (idx2 : Nat) (hidx2 : idx2 < w),
--       ⟦aigNew, (((acc.cast haig).cast haig').vec.get ⟨idx1, hidx1⟩).get idx2 hidx2, assign⟧ = l[idx1].getLsbD idx2 := by
--   rw [RefVecVec.cast_eq]
--   intros idx1 hidx1 idx2 hidx2
--   rw [denote_cast (aigNew:=aigNew) (aigCurr:=aigCurr) (haig := haig) (hlen := by omega)]
--   apply hvec

theorem denote_blastExtractAndExtend (aig : AIG α) (xc : AIG.RefVec aig w) (x : BitVec w) (start : Nat)
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
  dsimp only [Lean.Elab.WF.paramLet] at hext
  rw [← hext]
  simp only [denote_blastZeroExtend, Nat.lt_one_iff, denote_blastExtract, dite_eq_ite,
    Bool.if_false_right, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_extract, Nat.sub_self, Nat.le_zero_eq]
  split
  · by_cases hidx0 : idx = 0
    · simp [hidx0, show 0 < w by omega, hx]
    · simp [hidx0]
  · intros
    simp [show w ≤ start + idx by omega]

theorem BitVec.extractAndExtendPopulateAux_get
  (i : Nat) (hi : i < w) (x : BitVec w) (hw : 0 < w) :
    let res := (BitVec.extractAndExtendPopulateAux 0 x [] (by intros i h h'; simp at h') (by omega) (by simp))
    res.val[i]'(by have := res.property; omega) = BitVec.setWidth w (BitVec.extractLsb' i 1 x) := by
  let out :=  (BitVec.extractAndExtendPopulateAux 0 x [] (by intros i h h'; simp at h') (by omega) (by simp))
  have := (out.property).right
  specialize this i hi (by omega)
  simp only [List.get_eq_getElem, BitVec.truncate_eq_setWidth, out] at this
  apply this

-- theorem denote_eq_blastExtractAndExtendPopulate
--   (assign : α → Bool)
--   (aig : AIG α) (start w : Nat) (xc : AIG.RefVec aig w) (x : BitVec w) (acc : RefVecVec aig w w) (hstart : start < w)
--   -- the bits added already denote to the corresponding entry in acc
--   (hacc : ∀ (idx1 : Nat) (hidx1 : idx1 < start),
--             ∀ (idx2 : Nat) (hidx2 : idx2 < w),
--               let newElem := blastExtractAndExtend aig xc start
--               ⟦newElem.aig, ((acc.cast (by apply extractAndExtend_le_size)).vec[idx1]).get idx2 hidx2, assign⟧ =
--               ((BitVec.extractAndExtendPopulateAux 0 x [] (by simp) (by omega) (by simp)).val.get
--                 ⟨idx1, by simp [(BitVec.extractAndExtendPopulateAux 0 x []
--                         (by intros i hi hl; simp at hl)
--                         (by omega) (by simp)).property]; exact Nat.lt_trans hidx1 (by omega)⟩).getLsbD idx2)
--   -- the remaining entries denote to 0
--   (hacc' : ∀ (idx1 : Nat) (hidx1 : start ≤ idx1) (hidx1' : idx1 < w),
--             ∀ (idx2 : Nat) (hidx2 : idx2 < w),
--               let newElem := blastExtractAndExtend aig xc start
--               ⟦newElem.aig, ((acc.cast (by apply extractAndExtend_le_size)).vec[idx1]).get idx2 hidx2, assign⟧ = (0#w).getLsbD idx2)
--   (hx : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, xc.get idx hidx, assign⟧ = x.getLsbD idx)
--    :
--     ∀ (idx1 : Nat) (hidx1 : idx1 < start + 1),
--       ∀ (idx2 : Nat) (hidx2 : idx2 < w),
--       let bit := blastExtractAndExtend aig xc (start)
--       let updated := acc.set start bit.vec (by apply extractAndExtend_le_size) hstart
--       ⟦
--         bit.aig,
--         (updated.vec[idx1]).get idx2 hidx2,
--         assign
--       ⟧ =
--         let bvRes := BitVec.extractAndExtendPopulateAux 0 x [] (by intros i hi hl; simp at hl) (by omega) (by simp)
--       (bvRes.val.get ⟨idx1, by simp [bvRes.property]; omega⟩).getLsbD idx2 := by
--   intros idx1 hidx1 idx2 hidx2
--   let bit := blastExtractAndExtend aig xc (start)
--   let updated := acc.set start bit.vec (by apply extractAndExtend_le_size) hstart
--   let bvRes := BitVec.extractAndExtendPopulateAux 0 x [] (by intros i hi hl; simp at hl) (by omega) (by simp)
--   let currList := bvRes.val.extract (start := 0) (stop := start)
--   let currElem := bvRes.val.get ⟨start, by omega⟩
--   simp only [List.get_eq_getElem, BitVec.truncate_eq_setWidth]
--   rw [denote_set (aigOld := aig) (aigNew := bit.aig) (acc := acc) (idxSet := start)
--           (hidxSet := hstart) (haig := by apply extractAndExtend_le_size) (assign := assign)
--           (l := bvRes) (hlen := by simp; omega) (bv := currElem)]
--   · simp [bvRes, currElem, bvRes]
--   · simp [bit]
--     intros jdx1 hjdx1 jdx2 hjdx2
--     by_cases hjdx1' : jdx1 < start
--     · specialize hacc jdx1 hjdx1' jdx2 hjdx2
--       apply hacc
--     · specialize hacc' jdx1 (by omega) (by omega) jdx2 hjdx2
--       simp at hacc'
--       by_cases hjdx1' : jdx1 = start
--       · simp [hjdx1']
--         have ⟨hlen, hprop⟩ := bvRes.property
--         specialize hprop start (by omega) (by omega)
--         simp at hprop
--         simp [hprop]




--         sorry
--       ·
--         sorry
--   ·
--     sorry




--   (assign : α → Bool) (l : List (BitVec w)) (bv : BitVec w)
--   (hlen : l.length = n)
--   (hvec : ∀ (idx1 : Nat) (hidx1 : idx1 < n),
--     ∀ (idx2 : Nat) (hidx2 : idx2 < w),
--       ⟦aigNew, ((acc.cast haig).vec[idx1]).get idx2 hidx2, assign⟧ =
--       l[idx1].getLsbD idx2)
--   (helem : ∀ (idx1 : Nat) (hidx1 : idx1 < w),
--     ⟦aigNew, elem.get idx1 hidx1, assign⟧ = (bv.getLsbD idx1))
--   : ∀ (idx1 : Nat) (hidx1 : idx1 < n),
--     ∀ (idx2 : Nat) (hidx2 : idx2 < w),
--       ⟦aigNew, ((acc.set idxSet elem haig (hidxSet)).vec[idx1]).get idx2 hidx2, assign⟧ =
--       ((l.set idxSet bv)[idx1]'(by simp; omega)).getLsbD idx2 := by
--   intros idx1 hidx1 idx2 hidx2
--   by_cases heq : idxSet = idx1
--   · simp [←heq, RefVecVec.get_set_eq idxSet acc elem hidxSet haig, helem]
--   · simp only [ne_eq, heq, not_false_eq_true, List.getElem_set_ne]
--     rw [RefVecVec.get_set idxSet acc elem hidxSet haig]
--     · apply hvec
--     · omega




  -- rw [denote_set]


--   intros idx1 hidx1 idx2 hidx2
--   let elem := blastExtractAndExtend aigAcc xc start
--   let bvRes := BitVec.extractAndExtendPopulateAux 0 x [] (by intros i hi hl; simp at hl) (by omega) (by simp)
--   let currList := bvRes.val.extract (start := 0) (stop := start)
--   let currElem := bvRes.val.get ⟨start, by omega⟩
--   rw [denote_push (l := currList) (bv := currElem)]
--   · simp
--     by_cases h1 : idx1 = start
--     · -- inspecting the last element of the list
--       simp [h1]
--       have h2 := List.getElem_concat_length (i := start) (a := currElem) (l := currList) (by simp [currList]; omega)
--       specialize h2 (by simp [currList]; omega)
--       simp [h2]
--       let res' := BitVec.extractAndExtendPopulateAux 0 x [] (by intros i hi hl; simp at hl) (by omega) (by simp)
--       have := BitVec.extractAndExtendPopulateAux_get (i := start) (x := x)
--         (hi := by omega) (by omega)
--       simp at this
--       rw [this]
--       simp only [currElem]
--       simp
--       rw [BitVec.extractAndExtendPopulateAux_get (i := start) (x := x) (by have := bvRes; omega) (by omega)]
--       simp
--     · -- inspecting an element that was already in the acc
--       have hl := List.getElem_append_left (as := currList) (bs := [currElem]) (i := idx1) (h' := by simp; omega)
--       rw [hl (by simp [currList];  omega)]
--       let res := BitVec.extractAndExtendPopulateAux 0 x [] (by intros i hi hl; simp at hl) (by omega) (by simp)
--       rw [BitVec.extractAndExtendPopulateAux_get (i := idx1) (x := x) (by have := res; omega) (by omega)]
--       have : idx1 < start := by omega
--       simp [currList]
--       simp [bvRes]
--       rw [BitVec.extractAndExtendPopulateAux_get (i := idx1) (x := x) (by have := bvRes; omega) (by omega)]
--       simp
--   · simp [currList]; omega
--   · intros idx1 hidx1 idx2 hidx2
--     simp [currList, bvRes]
--     simp at hacc'
--     specialize hacc' idx1 hidx1 idx2 hidx2
--     have hproof1 : aigAcc.decls.size ≤ (blastExtractAndExtend aigAcc xc start).aig.decls.size := by apply extractAndExtend_le_size
--     have hproof2 : (blastExtractAndExtend aigAcc xc start).aig.decls.size ≤ (blastExtractAndExtend aigAcc xc start).aig.decls.size := by omega
--     have hcast' : ((acc.cast hproof1).cast hproof2) = acc.cast (by apply extractAndExtend_le_size) := by simp [RefVecVec.cast]
--     rw [hcast']
--     apply hacc'
--   · intros idx hidx
--     rw [denote_blastExtractAndExtend (aig := aigAcc) (xc := xc) (x := x) (start := start) (assign := assign) (hx := hx)]
--     ·
--       simp
--       by_cases h1 : idx = 0
--       · -- this is the only bit that gets actually populated with a meaningful value
--         simp [h1, show 0 < w by omega]
--         simp [currElem]
--         simp [bvRes]
--         have :=  BitVec.extractAndExtendPopulateAux_get (i := start) (x := x) (by omega) (by omega)
--         simp [this]
--       · -- everythign else is the result of zExt
--         simp [h1]
--         simp [currElem, bvRes]
--         have :=  BitVec.extractAndExtendPopulateAux_get (i := start) (x := x) (by omega) (by omega)
--         simp [this]
--         intros
--         omega

-- theorem BitVec.addVecAux_prop

--   (oldParSumBv : List (BitVec w)) (newParSumBv : List (BitVec w))
--   (hlen : oldParSumBv.length = inputNodes)
--   (hlen' : newParSumBv.length = currNode/2)
--   (hle : currNode ≤ inputNodes)
--   (heven : currNode %2 = 0)
--   (hlt : i * 2 + 1 < oldParSumBv.length)
--   (hlt' : i < newParSumBv.length)
--   (res : {l : List (BitVec w) // (l.length = (inputNodes + 1)/2) ∧
--        (∀ i (hi : i < l.length) (hl : l.length = (inputNodes + 1)/2),
--         if hc : i*2 + 1 < oldParSumBv.length then
--           l.get ⟨i, by simp [hl]; omega⟩ = oldParSumBv.get ⟨i*2, by omega⟩ + oldParSumBv.get ⟨i*2 + 1, by omega⟩
--         else
--           l.get ⟨i, by simp [hl]; omega⟩ = oldParSumBv.get ⟨i*2, by omega⟩)
--         })
--   (hacc : ∀ (i_1 : Nat) (hi : i_1 < newParSumBv.length) (_ : newParSumBv.length = currNode / 2),
--             if hc : i_1 * 2 + 1 < oldParSumBv.length then
--               newParSumBv.get ⟨i_1, (by omega)⟩ = oldParSumBv.get ⟨i_1 * 2, (by omega)⟩ + oldParSumBv.get ⟨i_1 * 2 + 1, hc⟩
--                 else newParSumBv.get ⟨i_1, (by omega)⟩ = oldParSumBv.get ⟨i_1 * 2, (by omega)⟩) :
--     newParSumBv[i]'hlt' = (oldParSumBv[i * 2]'(by omega) + oldParSumBv[i * 2 + 1]'hlt):= by
--   have ⟨plen, pp⟩ := res.property
--   specialize pp i (by omega) (by omega)
--   simp [hlt] at pp
--   specialize hacc i (by omega) (by omega)
--   simp [hlt] at hacc
--   apply hacc

-- theorem denote_step_blastAddVec
--   -- blastAddVec input
--   (aigOld : AIG α) (currNode w: Nat) (hi : 1 < inputNodes) (hle : currNode < inputNodes)
--   (assign : α → Bool)
--   (oldParSum : RefVecVec aigOld w inputNodes) (newParSum : RefVecVec aigOld w (currNode/2))
--   (heven : currNode %2 = 0)  (hw : inputNodes ≤ w) (hw' : 1 < inputNodes)
--   (elem : RefVecEntry α w)
--   (helem' :
--     if hc : currNode + 1 < inputNodes then
--       elem = blastAdd aigOld (w := w) ⟨oldParSum.vec.get ⟨currNode, (by omega)⟩, oldParSum.vec.get ⟨currNode + 1, (by omega)⟩⟩
--     else
--       let zero := blastConst aigOld (w := w) 0
--       elem = blastAdd aigOld (w := w) ⟨oldParSum.vec.get ⟨currNode, (by omega)⟩, zero⟩)
--   -- BitVec input
--   (oldParSumBv : List (BitVec w)) (newParSumBv : List (BitVec w)) (elemBv : BitVec w)
--   (hlenOld : oldParSumBv.length = inputNodes) (hlenNew : newParSumBv.length = currNode/2)
--   (hacc : ∀ (i_1 : Nat) (hi : i_1 < newParSumBv.length),
--     newParSumBv.length = currNode / 2 →
--       if hc : i_1 * 2 + 1 < oldParSumBv.length then
--         newParSumBv.get ⟨i_1, hi⟩ = oldParSumBv.get ⟨i_1 * 2, (by omega)⟩ + oldParSumBv.get ⟨i_1 * 2 + 1, hc⟩
--       else newParSumBv.get ⟨i_1, hi⟩ = oldParSumBv.get ⟨i_1 * 2, (by omega)⟩)
--   -- newParSum denotes to newParSumBv
--   (hnew :
--     ∀ (idx1 : Nat) (hidx1 : idx1 < currNode/2),
--       ∀ (idx2 : Nat) (hidx2 : idx2 < w),
--         ⟦elem.aig, ((newParSum.cast (aig2 := elem.aig)
--                     (by split at helem' <;> (simp [helem']; apply AIG.LawfulVecOperator.le_size (f := blastAdd)))
--                     ).vec.get ⟨idx1, hidx1⟩).get idx2 hidx2, assign⟧ =
--           (newParSumBv.get ⟨idx1, by simp [hlenNew]; omega⟩ ).getLsbD idx2)
--   -- elem denotes to elemBv
--   (helem :
--     ∀ (idx1 : Nat) (hidx1 : idx1 < w),
--       ⟦elem.aig, elem.vec.get idx1 hidx1, assign⟧ = elemBv.getLsbD idx1
--     )
--         :
--     ∀ (idx1 : Nat) (hidx1 : idx1 < (currNode + 1)/2),
--       ∀ (idx2 : Nat) (hidx2 : idx2 < w),
--         ⟦elem.aig, ((newParSum.push elem.vec (by split at helem' <;> (simp [helem']; apply AIG.LawfulVecOperator.le_size (f := blastAdd)))).vec.get ⟨idx1, by omega⟩).get idx2 hidx2 , assign⟧ =
--           let bvRes := BitVec.addVecAux 0 inputNodes oldParSumBv [] (by omega) (by omega) (by omega) (by omega) hlenOld (by simp) (by simp)
--           (bvRes.val.get ⟨idx1, by have := bvRes; omega⟩).getLsbD idx2 := by
--     intros idx1 hidx1 idx2 hidx2
--     have := denote_push (assign := assign) (w := w) (n := currNode/2) (aigNew := elem.aig) (aigOld := aigOld)
--           (acc := newParSum) (elem := elem.vec) (l := newParSumBv) (bv := elemBv)
--           (by split at helem' <;> (simp [helem']; apply AIG.LawfulVecOperator.le_size (f := blastAdd))) (by omega)
--     rw [this]
--     · by_cases hlast : idx1 < newParSumBv.length
--       · simp
--         have := List.getElem_append_left (as := newParSumBv) (bs := [elemBv]) (i := idx1) (h := by omega) (h' := by simp; omega)
--         simp [this]
--         let bvRes := BitVec.addVecAux 0 inputNodes oldParSumBv [] (by omega) (by omega) hw hw' hlenOld (by simp) (by omega)
--         have ⟨len, p⟩ := bvRes.property
--         specialize p idx1 (by omega) (by omega)
--         split at p
--         · simp [bvRes] at p
--           simp [p]
--           let bvRes := BitVec.addVecAux 0 inputNodes oldParSumBv [] (by omega) (by omega) hw hw' hlenOld (by simp) (by omega)
--           have hle' : currNode ≤ inputNodes := by omega
--           have := BitVec.addVecAux_prop (i := idx1) (currNode := currNode) (inputNodes := inputNodes) (w := w) (oldParSumBv := oldParSumBv)
--                   (newParSumBv := newParSumBv) (by omega) (by omega)
--                   hle' heven (by omega) (by omega) (res := bvRes) hacc
--           simp [this]
--         · omega
--       · have := List.getElem_concat_length (i := idx1) (a := elemBv) (l := newParSumBv) (by omega)
--         specialize this (by omega)
--         simp
--         rw [this]
--         let bvRes := BitVec.addVecAux 0 inputNodes oldParSumBv [] (by omega) (by omega) hw hw' hlenOld (by omega) (by omega)
--         have := bvRes.property
--         omega
--     · intros idx1 hidx1 idx2 hidx2
--       apply hnew
--     · intros
--       apply helem

theorem denote_blastAddVec
  (assign : α → Bool)
  (aigCurr : AIG α) (usedNodes validNodes w: Nat)
  (oldParSum : RefVecVec aigCurr w inputNodes) (newParSum : RefVecVec aigCurr w inputNodes)
  (heven : usedNodes % 2 = 0) (hin : 1 < inputNodes) (hval : validNodes ≤ inputNodes)
  -- BitVec input
  (oldParSumBv : List (BitVec w)) (newParSumBv : List (BitVec w))
  (hlenOld : oldParSumBv.length = inputNodes) (hlenNew : newParSumBv.length = inputNodes)
  -- all the bitvectors in newParSumBv in the valid range are the result of summing two bitvecs in the
  -- old list, while the remaining ones are a copy of the elements in the old bitvec.
  (hacc : ∀ (j : Nat) (hj : j < newParSumBv.length) (hjo : j * 2 < oldParSumBv.length),
      if hlt : j < (validNodes + 1)/2 then
        if hc : j * 2 + 1 < oldParSumBv.length then
          newParSumBv.get ⟨j, hj⟩ = oldParSumBv.get ⟨j * 2, (by omega)⟩ + oldParSumBv.get ⟨j * 2 + 1, hc⟩
        else
          newParSumBv.get ⟨j, hj⟩ = oldParSumBv.get ⟨j * 2, (by omega)⟩
      else
        newParSumBv.get ⟨j, hj⟩ = oldParSumBv.get ⟨j, by omega⟩
  )
  -- newParSum denotes to newParSumBv
  (hnew :
    ∀ (idx1 : Nat) (hidx1 : idx1 < currNode/2),
      ∀ (idx2 : Nat) (hidx2 : idx2 < w),
        ⟦aigCurr, (newParSum.vec.get ⟨idx1, by simp [hleneq]; omega⟩).get idx2 hidx2, assign⟧ =
          (newParSumBv.get ⟨idx1, by simp [hlenNew]; omega⟩ ).getLsbD idx2)
  (hold :
    ∀ (idx1 : Nat) (hidx1 : idx1 < inputNodes),
      ∀ (idx2 : Nat) (hidx2 : idx2 < w),
        ⟦aigCurr, (oldParSum.vec.get ⟨idx1, by omega⟩).get idx2 hidx2, assign⟧ =
          (oldParSumBv.get ⟨idx1, by omega⟩ ).getLsbD idx2)
        :
    ∀ (idx1 : Nat) (hidx1 : idx1 < (inputNodes + 1)/2),
      ∀ (idx2 : Nat) (hidx2 : idx2 < w),
        let res := (blastAddVec aigCurr currNode (inputNodes := inputNodes) (oldParSum := oldParSum) (newLen := newLen)
                                (newParSum := newParSum) (by omega) (by omega) (by omega) (by omega) (by omega))
        ⟦res.aig, (res.vec.vec.get ⟨idx1, by omega⟩).get idx2 hidx2, assign⟧  =
          let bvRes := BitVec.addVecAux 0 inputNodes oldParSumBv [] (by omega) (by omega) (by omega) (by omega) hlenOld (by simp) (by simp)
          (bvRes.val.get ⟨idx1, by have := bvRes; omega⟩).getLsbD idx2 := by
    intros idx1 hidx1 idx2 hidx2
    by_cases hcondres : currNode < inputNodes
    · by_cases hlt' :  currNode + 2 < inputNodes
      · -- hlt' :  currNode + 2 < inputNodes
        generalize hres : (blastAddVec aigCurr currNode (inputNodes := inputNodes) (oldParSum := oldParSum)
                        (newParSum := newParSum) (by omega) (by omega) (by omega) (by omega) (by omega)) = res
        unfold blastAddVec at hres
        rw [← hres]
        rw [dite_cond_eq_true (by simp; omega)]
        rw [dite_cond_eq_true (by simp; omega)]
        simp
        let newRes := (blastAdd aigCurr ⟨oldParSum.vec.get ⟨currNode, (by omega)⟩, oldParSum.vec.get ⟨currNode + 1, (by omega)⟩⟩)
        let elemBv := oldParSumBv.get ⟨currNode, by omega⟩ + oldParSumBv.get ⟨currNode + 1, by omega⟩
        have hcast : currNode / 2 + 1 = (currNode + 2) / 2 := by omega
        have := denote_blastAddVec
                (assign := assign)
                (aigCurr := newRes.aig)
                (currNode := currNode + 2)
                (hi := hi) (hle := hlt')
                (oldParSum := oldParSum.cast (aig2 := newRes.aig) (by simp [newRes]; exact LawfulVecOperator.le_size aigCurr ..))
                (newParSum := ((newParSum.cast (aig2 := newRes.aig)
                                      (by simp [newRes]; exact LawfulVecOperator.le_size aigCurr ..))).push newRes.vec (by omega))
                (heven := by omega)
                (hw := hw) (hw' := hw')
                (oldParSumBv := oldParSumBv)
                (newParSumBv := newParSumBv.concat elemBv)
                (hlenOld := by omega)
                (hlenNew := by simp; omega)
                -- missing: hacc and hnew, to prove
        rw [this]
        · simp
        · -- hacc
          intros idx hidx hlen
          simp
          split
          · case _ hidx' =>
            by_cases hfin : idx < newParSumBv.length
            · rw [List.getElem_append_left (as := newParSumBv) (bs := [elemBv]) hfin]
              specialize hacc idx hfin
              simp [hlenNew, hidx'] at hacc
              exact hacc
            · simp [show idx = newParSumBv.length by omega] at *
              simp [elemBv]
              congr <;> omega
          · case _ hidx' => omega -- contra
        · -- hnew
          intros idx hidx1 idx2 hidx2
          simp
          have := denote_push
                    (acc := (newParSum.cast (aig2 := newRes.aig) (by simp [newRes]; exact LawfulVecOperator.le_size aigCurr ..)))
                    (elem := newRes.vec)
                    (haig := by omega)
                    (aigNew := newRes.aig)
                    (assign := assign)
                    (l := newParSumBv)
                    (bv := elemBv)
                    (hlen := by omega)
          rw [this]
          · simp
          · simp
            intros idx1 hidx1 idx2 hidx2
            have := denote_cast_cast
                        (aigCurr := aigCurr) (aigNew := newRes.aig) (acc := newParSum) (haig := by simp [newRes]; exact LawfulVecOperator.le_size aigCurr ..) (haig' := by omega)
                        (assign := assign) (l := newParSumBv) (hlen := by omega)
            rw [this]
            · intros idx1 hidx1 idx2 hidx2
              specialize hnew idx1 (by omega) idx2 (by omega)
              simp [hnew]
          · intro idx1 hidx1
            simp [newRes]
            have := denote_blastAdd
                    (input := ⟨oldParSum.vec.get ⟨currNode, (by omega)⟩, oldParSum.vec.get ⟨currNode + 1, by omega⟩⟩)
            rw [this]
            · intros idx hidx
              simp
              specialize hold currNode (by omega) idx (by omega)
              exact hold
            · intros idx hidx
              simp
              specialize hold (currNode + 1) (by omega) idx (by omega)
              exact hold
        · simp
          intros idx1 hidx1 idx1 hidx2
          have := denote_cast
                        (aigCurr := aigCurr) (aigNew := newRes.aig) (acc := oldParSum) (haig := by simp [newRes]; exact LawfulVecOperator.le_size aigCurr ..)
                        (assign := assign) (l := oldParSumBv) (hlen := by omega)
          rw [this]
          apply hold
      · -- ¬ hlt' :  currNode + 2 < inputNodes
        -- rw [← hres]
        by_cases hlt : currNode + 1 < inputNodes
        · unfold blastAddVec
          simp [hlt, hcondres]
          rw [dite_cond_eq_true (by simp; omega)]
          rw [dite_cond_eq_true (by simp; omega)]
          let res' := blastAdd aigCurr ⟨oldParSum.vec.get ⟨currNode, (by omega)⟩, oldParSum.vec.get ⟨currNode + 1, (by omega)⟩⟩;
          let aig := res'.aig;
          let add := res'.vec;
          let oldParSum := oldParSum.cast (aig2 := aig)
                            (by simp [aig, res']; exact LawfulVecOperator.le_size aigCurr (f := blastAdd) ..)
          let newParSum := newParSum.cast (aig2 := aig)
                            (by simp [aig, res']; exact LawfulVecOperator.le_size aigCurr (f := blastAdd) ..)
          let newVec := newParSum.push add (by simp [aig, res'])
          generalize hres : blastAddVec res'.aig (currNode + 2) inputNodes oldParSum newVec (by omega) (by omega) hw hw' (by omega) = res
          unfold blastAddVec at hres
          simp at hres
          by_cases hlt' :  currNode + 2 < inputNodes
          · omega
          · have : currNode + 2 = inputNodes := by omega
            simp [hlt'] at hres
            rw [← hres]
            simp [newVec]
            -- have : newLen = (currNode + 2) / 2 - 1 := by omega
            -- subst this
            simp_all
            have := denote_push
                    -- (acc := (newParSum.cast (aig2 := res'.aig) (by simp [res]; exact Nat.le_refl aig.decls.size)))
                    (elem := add)
                    (haig := by sorry)
                    (aigOld := aigCurr)
                    (aigNew := aig)
                    (assign := assign)
                    (l := newParSumBv)
                    (bv := oldParSumBv.get ⟨currNode, by omega⟩ + oldParSumBv.get ⟨currNode + 1, by omega⟩)
                    (hlen := by omega)

            sorry
        · -- ¬hlt'
          -- rw [dite_cond_eq_false (by simp; omega)]
          unfold blastAddVec
          simp
          rw [dite_cond_eq_true (by simp [hcondres])]
          rw [dite_cond_eq_false (by simp; omega)]
          have : currNode + 1 = inputNodes := by omega
          simp [this] at *
          let zero := blastConst aigCurr (w := w) 0
          let res' := blastAdd aigCurr ⟨oldParSum.vec.get ⟨currNode, (by omega)⟩, zero⟩;
          let aig := res'.aig;
          let add := res'.vec;
          let oldParSum := oldParSum.cast (aig2 := aig)
                            (by simp [aig, res']; exact LawfulVecOperator.le_size aigCurr (f := blastAdd) ..)
          let newParSum := newParSum.cast (aig2 := aig)
                            (by simp [aig, res']; exact LawfulVecOperator.le_size aigCurr (f := blastAdd) ..)
          let newVec := newParSum.push add (by simp [aig, res'])
          generalize hres : blastAddVec res'.aig (currNode + 2) inputNodes oldParSum newVec (by omega) (by omega) hw hw' (by omega) = res
          unfold blastAddVec at hres
          rw [← hres]
          simp [hlt'] at hres
          rw [dite_cond_eq_false (by simp; omega)]
          simp [newVec]

          sorry
    · omega

-- @[simp]
-- theorem denote_blastPopCount (aig : AIG α) (xc : RefVec aig w) (x : BitVec w) (assign : α → Bool)
--       (hx : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, xc.get idx hidx, assign⟧ = x.getLsbD idx)
--       :
--       ∀ (idx : Nat) (hidx : idx < w),
--         ⟦(blastPopCount aig xc).aig, (blastPopCount aig xc).vec.get idx hidx, assign⟧
--           =
--         (BitVec.popCountAuxRec x 0 0).getLsbD idx := by
--   sorry



end blastPopCount
end bitblast
end BVExpr

end Std.Tactic.BVDecide
