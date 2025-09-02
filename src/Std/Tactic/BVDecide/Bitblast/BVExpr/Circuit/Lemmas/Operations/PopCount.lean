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

namespace BVExpr

namespace bitblast
namespace blastPopCount

variable [Hashable α] [DecidableEq α]

-- /-- Casting `RefVecVec` twice is the same as casting once. -/
-- theorem RefVecVec.cast_cast {aig1 aig2 : AIG α} (s : RefVecVec aig1 lenWords len) (h : aig1.decls.size ≤ aig2.decls.size) :
--     (s.cast h).cast (aig2 := aig2) (by omega) = s.cast h := by
--   simp [RefVecVec.cast]

-- /-- Getting the `idx`-th element of the `vec` of `RefVecVec` after setting it retrieves the same element. -/
-- theorem RefVecVec.get_set_eq {aigOld aigNew : AIG α} {w len : Nat} (idx : Nat) (s : RefVecVec aigOld w len) (elem : RefVec aigNew w)
--       (h : idx < len) (h' : aigOld.decls.size ≤ aigNew.decls.size) :
--     (RefVecVec.set idx s elem h' h).vec[idx] = elem := by
--   simp [RefVecVec.set]

-- /-- After setting the `idx`-th element of the `vec` of `RefVecVec`, retrieving any element that is not at that index
--     is the same as getting that element from the original vector. -/
-- theorem RefVecVec.get_set {aigOld aigNew : AIG α} {w len : Nat} (idx : Nat) (s : RefVecVec aigOld w len) (elem : RefVec aigNew w)
--       (h : idx < len) (h' : aigOld.decls.size ≤ aigNew.decls.size) :
--   ∀ (idx' : Nat) (_ : ¬idx' = idx) (hi' : idx' < len),
--     (RefVecVec.set idx s elem h' h).vec[idx'] = (s.cast h').vec[idx'] := by
--   intros idx1 hidx1 hidx1'
--   simp only [RefVecVec.set, Vector.getElem_set, Vector.getElem_map, RefVecVec.cast, ite_eq_right_iff]
--   intros
--   omega


-- theorem BitVec.addVecAux_eq (usedNodes validNodes i : Nat) (extBits : List (BitVec w))
--       (heven : usedNodes % 2 = 0) (hin : 1 < w) (hval : validNodes ≤ w) (hi : i < w) (hi' : i * 2 < w)
--       (hlen : extBits.length = w) :
--       let res := BitVec.addVecAux 0 validNodes extBits extBits (by omega) hin hval hlen hlen
--       if h1: i < (validNodes+1)/2 then
--         if h2: i * 2 + 1 < w then
--             res.val[i] = extBits[i*2] + extBits[i*2+1]
--           else res.val[i] = extBits[i*2]
--             else res.val[i] = extBits[i] := by
--             sorry

-- theorem denote_set {aigOld aigNew : AIG α} {n w : Nat}
--   (acc : RefVecVec aigOld w n) (elem : AIG.RefVec aigNew w)
--   (idxSet : Nat) (hidxSet : idxSet < n)
--   (haig : aigOld.decls.size ≤ aigNew.decls.size)
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

-- -- theorem denote_cast {aigCurr aigNew : AIG α} {n w : Nat}
-- --   (acc : RefVecVec aigCurr w n)
-- --   (haig : aigCurr.decls.size ≤ aigNew.decls.size)
-- --   (assign : α → Bool) (l : List (BitVec w))
-- --   (hlen : l.length = n)
-- --   (hvec : ∀ (idx1 : Nat) (hidx1 : idx1 < n),
-- --     ∀ (idx2 : Nat) (hidx2 : idx2 < w),
-- --       ⟦aigCurr, (acc.vec.get ⟨idx1, hidx1⟩).get idx2 hidx2, assign⟧ = (l.get ⟨idx1, (by omega)⟩).getLsbD idx2)
-- --   : ∀ (idx1 : Nat) (hidx1 : idx1 < n),
-- --     ∀ (idx2 : Nat) (hidx2 : idx2 < w),
-- --       ⟦aigNew, (((acc.cast haig)).vec.get ⟨idx1, hidx1⟩).get idx2 hidx2, assign⟧ = l[idx1].getLsbD idx2 := by
-- --   simp at hvec
-- --   intros idx1 hidx1 idx2 hidx2
-- --   specialize hvec idx1 hidx1 idx2 hidx2
-- --   sorry

-- -- theorem denote_cast_cast {aigCurr aigNew : AIG α} {n w : Nat}
-- --   (acc : RefVecVec aigCurr w n)
-- --   (haig : aigCurr.decls.size ≤ aigNew.decls.size)
-- --   (haig' : aigNew.decls.size ≤ aigNew.decls.size)
-- --   (assign : α → Bool) (l : List (BitVec w))
-- --   (hlen : l.length = n)
-- --   (hvec : ∀ (idx1 : Nat) (hidx1 : idx1 < n),
-- --     ∀ (idx2 : Nat) (hidx2 : idx2 < w),
-- --       ⟦aigCurr, (acc.vec.get ⟨idx1, hidx1⟩).get idx2 hidx2, assign⟧ = (l.get ⟨idx1, (by omega)⟩).getLsbD idx2)
-- --   : ∀ (idx1 : Nat) (hidx1 : idx1 < n),
-- --     ∀ (idx2 : Nat) (hidx2 : idx2 < w),
-- --       ⟦aigNew, (((acc.cast haig).cast haig').vec.get ⟨idx1, hidx1⟩).get idx2 hidx2, assign⟧ = l[idx1].getLsbD idx2 := by
-- --   rw [RefVecVec.cast_eq]
-- --   intros idx1 hidx1 idx2 hidx2
-- --   rw [denote_cast (aigNew:=aigNew) (aigCurr:=aigCurr) (haig := haig) (hlen := by omega)]
-- --   apply hvec


-- -- theorem denote_blastExtractAndExtend (aig : AIG α) (xc : AIG.RefVec aig w) (x : BitVec w) (start : Nat)
-- --     (hx : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, xc.get idx hidx, assign⟧ = x.getLsbD idx) :
-- --   ∀ (idx : Nat) (hidx : idx < w),
-- --     ⟦
-- --       (blastExtractAndExtend aig xc start).aig,
-- --       (blastExtractAndExtend aig xc start).vec.get idx hidx,
-- --       assign
-- --      ⟧ = (BitVec.zeroExtend w (BitVec.extractLsb start start x)).getLsbD idx := by
-- --   intros idx hidx
--   generalize hext: blastExtractAndExtend aig xc start = res
--   unfold blastExtractAndExtend at hext
--   dsimp only [Lean.Elab.WF.paramLet] at hext
--   rw [← hext]
--   simp only [denote_blastZeroExtend, Nat.lt_one_iff, denote_blastExtract, dite_eq_ite,
--     Bool.if_false_right, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
--     BitVec.getLsbD_extract, Nat.sub_self, Nat.le_zero_eq]
--   split
--   · by_cases hidx0 : idx = 0
--     · simp [hidx0, show 0 < w by omega, hx]
--     · simp [hidx0]
--   · intros
--     simp [show w ≤ start + idx by omega]

-- theorem BitVec.extractAndExtendPopulateAux_get
--   (i : Nat) (hi : i < w) (x : BitVec w) (hw : 0 < w) :
--     let res := (BitVec.extractAndExtendPopulateAux 0 x [] (by intros i h h'; simp at h') (by omega) (by simp))
--     res.val[i]'(by have := res.property; omega) = BitVec.setWidth w (BitVec.extractLsb' i 1 x) := by
--   let out :=  (BitVec.extractAndExtendPopulateAux 0 x [] (by intros i h h'; simp at h') (by omega) (by simp))
--   have := (out.property).right
--   specialize this i hi (by omega)
--   simp only [List.get_eq_getElem, BitVec.truncate_eq_setWidth, out] at this
--   apply this

-- -- theorem denote_eq_blastExtractAndExtendPopulate
-- --   (assign : α → Bool)
-- --   (aig : AIG α) (start w : Nat) (xc : AIG.RefVec aig w) (x : BitVec w) (acc : RefVecVec aig w w) (hstart : start < w)
-- --   -- the bits added already denote to the corresponding entry in acc
-- --   (hacc : ∀ (idx1 : Nat) (hidx1 : idx1 < start),
-- --             ∀ (idx2 : Nat) (hidx2 : idx2 < w),
-- --               let newElem := blastExtractAndExtend aig xc start
-- --               ⟦newElem.aig, ((acc.cast (by apply extractAndExtend_le_size)).vec[idx1]).get idx2 hidx2, assign⟧ =
-- --               ((BitVec.extractAndExtendPopulateAux 0 x [] (by simp) (by omega) (by simp)).val.get
-- --                 ⟨idx1, by simp [(BitVec.extractAndExtendPopulateAux 0 x []
-- --                         (by intros i hi hl; simp at hl)
-- --                         (by omega) (by simp)).property]; exact Nat.lt_trans hidx1 (by omega)⟩).getLsbD idx2)
-- --   -- the remaining entries denote to 0
-- --   (hacc' : ∀ (idx1 : Nat) (hidx1 : start ≤ idx1) (hidx1' : idx1 < w),
-- --             ∀ (idx2 : Nat) (hidx2 : idx2 < w),
-- --               let newElem := blastExtractAndExtend aig xc start
-- --               ⟦newElem.aig, ((acc.cast (by apply extractAndExtend_le_size)).vec[idx1]).get idx2 hidx2, assign⟧ = (0#w).getLsbD idx2)
-- --   (hx : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, xc.get idx hidx, assign⟧ = x.getLsbD idx)
-- --    :
-- --     ∀ (idx1 : Nat) (hidx1 : idx1 < start + 1),
-- --       ∀ (idx2 : Nat) (hidx2 : idx2 < w),
-- --       let bit := blastExtractAndExtend aig xc (start)
-- --       let updated := acc.set start bit.vec (by apply extractAndExtend_le_size) hstart
-- --       ⟦
-- --         bit.aig,
-- --         (updated.vec[idx1]).get idx2 hidx2,
-- --         assign
-- --       ⟧ =
-- --         let bvRes := BitVec.extractAndExtendPopulateAux 0 x [] (by intros i hi hl; simp at hl) (by omega) (by simp)
-- --       (bvRes.val.get ⟨idx1, by simp [bvRes.property]; omega⟩).getLsbD idx2 := by
-- --   intros idx1 hidx1 idx2 hidx2
-- --   let bit := blastExtractAndExtend aig xc (start)
-- --   let updated := acc.set start bit.vec (by apply extractAndExtend_le_size) hstart
-- --   let bvRes := BitVec.extractAndExtendPopulateAux 0 x [] (by intros i hi hl; simp at hl) (by omega) (by simp)
-- --   let currList := bvRes.val.extract (start := 0) (stop := start)
-- --   let currElem := bvRes.val.get ⟨start, by omega⟩
-- --   simp only [List.get_eq_getElem, BitVec.truncate_eq_setWidth]
-- --   rw [denote_set (aigOld := aig) (aigNew := bit.aig) (acc := acc) (idxSet := start)
-- --           (hidxSet := hstart) (haig := by apply extractAndExtend_le_size) (assign := assign)
-- --           (l := bvRes) (hlen := by simp; omega) (bv := currElem)]
-- --   · simp [bvRes, currElem, bvRes]
-- --   · simp [bit]
-- --     intros jdx1 hjdx1 jdx2 hjdx2
-- --     by_cases hjdx1' : jdx1 < start
-- --     · specialize hacc jdx1 hjdx1' jdx2 hjdx2
-- --       apply hacc
-- --     · specialize hacc' jdx1 (by omega) (by omega) jdx2 hjdx2
-- --       simp at hacc'
-- --       by_cases hjdx1' : jdx1 = start
-- --       · simp [hjdx1']
-- --         have ⟨hlen, hprop⟩ := bvRes.property
-- --         specialize hprop start (by omega) (by omega)
-- --         simp at hprop
-- --         simp [hprop]




-- --         sorry
-- --       ·
-- --         sorry
-- --   ·
-- --     sorry




-- --   (assign : α → Bool) (l : List (BitVec w)) (bv : BitVec w)
-- --   (hlen : l.length = n)
-- --   (hvec : ∀ (idx1 : Nat) (hidx1 : idx1 < n),
-- --     ∀ (idx2 : Nat) (hidx2 : idx2 < w),
-- --       ⟦aigNew, ((acc.cast haig).vec[idx1]).get idx2 hidx2, assign⟧ =
-- --       l[idx1].getLsbD idx2)
-- --   (helem : ∀ (idx1 : Nat) (hidx1 : idx1 < w),
-- --     ⟦aigNew, elem.get idx1 hidx1, assign⟧ = (bv.getLsbD idx1))
-- --   : ∀ (idx1 : Nat) (hidx1 : idx1 < n),
-- --     ∀ (idx2 : Nat) (hidx2 : idx2 < w),
-- --       ⟦aigNew, ((acc.set idxSet elem haig (hidxSet)).vec[idx1]).get idx2 hidx2, assign⟧ =
-- --       ((l.set idxSet bv)[idx1]'(by simp; omega)).getLsbD idx2 := by
-- --   intros idx1 hidx1 idx2 hidx2
-- --   by_cases heq : idxSet = idx1
-- --   · simp [←heq, RefVecVec.get_set_eq idxSet acc elem hidxSet haig, helem]
-- --   · simp only [ne_eq, heq, not_false_eq_true, List.getElem_set_ne]
-- --     rw [RefVecVec.get_set idxSet acc elem hidxSet haig]
-- --     · apply hvec
-- --     · omega




--   -- rw [denote_set]


-- --   intros idx1 hidx1 idx2 hidx2
-- --   let elem := blastExtractAndExtend aigAcc xc start
-- --   let bvRes := BitVec.extractAndExtendPopulateAux 0 x [] (by intros i hi hl; simp at hl) (by omega) (by simp)
-- --   let currList := bvRes.val.extract (start := 0) (stop := start)
-- --   let currElem := bvRes.val.get ⟨start, by omega⟩
-- --   rw [denote_push (l := currList) (bv := currElem)]
-- --   · simp
-- --     by_cases h1 : idx1 = start
-- --     · -- inspecting the last element of the list
-- --       simp [h1]
-- --       have h2 := List.getElem_concat_length (i := start) (a := currElem) (l := currList) (by simp [currList]; omega)
-- --       specialize h2 (by simp [currList]; omega)
-- --       simp [h2]
-- --       let res' := BitVec.extractAndExtendPopulateAux 0 x [] (by intros i hi hl; simp at hl) (by omega) (by simp)
-- --       have := BitVec.extractAndExtendPopulateAux_get (i := start) (x := x)
-- --         (hi := by omega) (by omega)
-- --       simp at this
-- --       rw [this]
-- --       simp only [currElem]
-- --       simp
-- --       rw [BitVec.extractAndExtendPopulateAux_get (i := start) (x := x) (by have := bvRes; omega) (by omega)]
-- --       simp
-- --     · -- inspecting an element that was already in the acc
-- --       have hl := List.getElem_append_left (as := currList) (bs := [currElem]) (i := idx1) (h' := by simp; omega)
-- --       rw [hl (by simp [currList];  omega)]
-- --       let res := BitVec.extractAndExtendPopulateAux 0 x [] (by intros i hi hl; simp at hl) (by omega) (by simp)
-- --       rw [BitVec.extractAndExtendPopulateAux_get (i := idx1) (x := x) (by have := res; omega) (by omega)]
-- --       have : idx1 < start := by omega
-- --       simp [currList]
-- --       simp [bvRes]
-- --       rw [BitVec.extractAndExtendPopulateAux_get (i := idx1) (x := x) (by have := bvRes; omega) (by omega)]
-- --       simp
-- --   · simp [currList]; omega
-- --   · intros idx1 hidx1 idx2 hidx2
-- --     simp [currList, bvRes]
-- --     simp at hacc'
-- --     specialize hacc' idx1 hidx1 idx2 hidx2
-- --     have hproof1 : aigAcc.decls.size ≤ (blastExtractAndExtend aigAcc xc start).aig.decls.size := by apply extractAndExtend_le_size
-- --     have hproof2 : (blastExtractAndExtend aigAcc xc start).aig.decls.size ≤ (blastExtractAndExtend aigAcc xc start).aig.decls.size := by omega
-- --     have hcast' : ((acc.cast hproof1).cast hproof2) = acc.cast (by apply extractAndExtend_le_size) := by simp [RefVecVec.cast]
-- --     rw [hcast']
-- --     apply hacc'
-- --   · intros idx hidx
-- --     rw [denote_blastExtractAndExtend (aig := aigAcc) (xc := xc) (x := x) (start := start) (assign := assign) (hx := hx)]
-- --     ·
-- --       simp
-- --       by_cases h1 : idx = 0
-- --       · -- this is the only bit that gets actually populated with a meaningful value
-- --         simp [h1, show 0 < w by omega]
-- --         simp [currElem]
-- --         simp [bvRes]
-- --         have :=  BitVec.extractAndExtendPopulateAux_get (i := start) (x := x) (by omega) (by omega)
-- --         simp [this]
-- --       · -- everythign else is the result of zExt
-- --         simp [h1]
-- --         simp [currElem, bvRes]
-- --         have :=  BitVec.extractAndExtendPopulateAux_get (i := start) (x := x) (by omega) (by omega)
-- --         simp [this]
-- --         intros
-- --         omega

-- -- theorem BitVec.addVecAux_prop

-- --   (oldParSumBv : List (BitVec w)) (newParSumBv : List (BitVec w))
-- --   (hlen : oldParSumBv.length = inputNodes)
-- --   (hlen' : newParSumBv.length = currNode/2)
-- --   (hle : currNode ≤ inputNodes)
-- --   (heven : currNode %2 = 0)
-- --   (hlt : i * 2 + 1 < oldParSumBv.length)
-- --   (hlt' : i < newParSumBv.length)
-- --   (res : {l : List (BitVec w) // (l.length = (inputNodes + 1)/2) ∧
-- --        (∀ i (hi : i < l.length) (hl : l.length = (inputNodes + 1)/2),
-- --         if hc : i*2 + 1 < oldParSumBv.length then
-- --           l.get ⟨i, by simp [hl]; omega⟩ = oldParSumBv.get ⟨i*2, by omega⟩ + oldParSumBv.get ⟨i*2 + 1, by omega⟩
-- --         else
-- --           l.get ⟨i, by simp [hl]; omega⟩ = oldParSumBv.get ⟨i*2, by omega⟩)
-- --         })
-- --   (hacc : ∀ (i_1 : Nat) (hi : i_1 < newParSumBv.length) (_ : newParSumBv.length = currNode / 2),
-- --             if hc : i_1 * 2 + 1 < oldParSumBv.length then
-- --               newParSumBv.get ⟨i_1, (by omega)⟩ = oldParSumBv.get ⟨i_1 * 2, (by omega)⟩ + oldParSumBv.get ⟨i_1 * 2 + 1, hc⟩
-- --                 else newParSumBv.get ⟨i_1, (by omega)⟩ = oldParSumBv.get ⟨i_1 * 2, (by omega)⟩) :
-- --     newParSumBv[i]'hlt' = (oldParSumBv[i * 2]'(by omega) + oldParSumBv[i * 2 + 1]'hlt):= by
-- --   have ⟨plen, pp⟩ := res.property
-- --   specialize pp i (by omega) (by omega)
-- --   simp [hlt] at pp
-- --   specialize hacc i (by omega) (by omega)
-- --   simp [hlt] at hacc
-- --   apply hacc

-- -- theorem denote_step_blastAddVec
-- --   -- blastAddVec input
-- --   (aigOld : AIG α) (currNode w: Nat) (hi : 1 < inputNodes) (hle : currNode < inputNodes)
-- --   (assign : α → Bool)
-- --   (oldParSum : RefVecVec aigOld w inputNodes) (newParSum : RefVecVec aigOld w (currNode/2))
-- --   (heven : currNode %2 = 0)  (hw : inputNodes ≤ w) (hw' : 1 < inputNodes)
-- --   (elem : RefVecEntry α w)
-- --   (helem' :
-- --     if hc : currNode + 1 < inputNodes then
-- --       elem = blastAdd aigOld (w := w) ⟨oldParSum.vec.get ⟨currNode, (by omega)⟩, oldParSum.vec.get ⟨currNode + 1, (by omega)⟩⟩
-- --     else
-- --       let zero := blastConst aigOld (w := w) 0
-- --       elem = blastAdd aigOld (w := w) ⟨oldParSum.vec.get ⟨currNode, (by omega)⟩, zero⟩)
-- --   -- BitVec input
-- --   (oldParSumBv : List (BitVec w)) (newParSumBv : List (BitVec w)) (elemBv : BitVec w)
-- --   (hlenOld : oldParSumBv.length = inputNodes) (hlenNew : newParSumBv.length = currNode/2)
-- --   (hacc : ∀ (i_1 : Nat) (hi : i_1 < newParSumBv.length),
-- --     newParSumBv.length = currNode / 2 →
-- --       if hc : i_1 * 2 + 1 < oldParSumBv.length then
-- --         newParSumBv.get ⟨i_1, hi⟩ = oldParSumBv.get ⟨i_1 * 2, (by omega)⟩ + oldParSumBv.get ⟨i_1 * 2 + 1, hc⟩
-- --       else newParSumBv.get ⟨i_1, hi⟩ = oldParSumBv.get ⟨i_1 * 2, (by omega)⟩)
-- --   -- newParSum denotes to newParSumBv
-- --   (hnew :
-- --     ∀ (idx1 : Nat) (hidx1 : idx1 < currNode/2),
-- --       ∀ (idx2 : Nat) (hidx2 : idx2 < w),
-- --         ⟦elem.aig, ((newParSum.cast (aig2 := elem.aig)
-- --                     (by split at helem' <;> (simp [helem']; apply AIG.LawfulVecOperator.le_size (f := blastAdd)))
-- --                     ).vec.get ⟨idx1, hidx1⟩).get idx2 hidx2, assign⟧ =
-- --           (newParSumBv.get ⟨idx1, by simp [hlenNew]; omega⟩ ).getLsbD idx2)
-- --   -- elem denotes to elemBv
-- --   (helem :
-- --     ∀ (idx1 : Nat) (hidx1 : idx1 < w),
-- --       ⟦elem.aig, elem.vec.get idx1 hidx1, assign⟧ = elemBv.getLsbD idx1
-- --     )
-- --         :
-- --     ∀ (idx1 : Nat) (hidx1 : idx1 < (currNode + 1)/2),
-- --       ∀ (idx2 : Nat) (hidx2 : idx2 < w),
-- --         ⟦elem.aig, ((newParSum.push elem.vec (by split at helem' <;> (simp [helem']; apply AIG.LawfulVecOperator.le_size (f := blastAdd)))).vec.get ⟨idx1, by omega⟩).get idx2 hidx2 , assign⟧ =
-- --           let bvRes := BitVec.addVecAux 0 inputNodes oldParSumBv [] (by omega) (by omega) (by omega) (by omega) hlenOld (by simp) (by simp)
-- --           (bvRes.val.get ⟨idx1, by have := bvRes; omega⟩).getLsbD idx2 := by
-- --     intros idx1 hidx1 idx2 hidx2
-- --     have := denote_push (assign := assign) (w := w) (n := currNode/2) (aigNew := elem.aig) (aigOld := aigOld)
-- --           (acc := newParSum) (elem := elem.vec) (l := newParSumBv) (bv := elemBv)
-- --           (by split at helem' <;> (simp [helem']; apply AIG.LawfulVecOperator.le_size (f := blastAdd))) (by omega)
-- --     rw [this]
-- --     · by_cases hlast : idx1 < newParSumBv.length
-- --       · simp
-- --         have := List.getElem_append_left (as := newParSumBv) (bs := [elemBv]) (i := idx1) (h := by omega) (h' := by simp; omega)
-- --         simp [this]
-- --         let bvRes := BitVec.addVecAux 0 inputNodes oldParSumBv [] (by omega) (by omega) hw hw' hlenOld (by simp) (by omega)
-- --         have ⟨len, p⟩ := bvRes.property
-- --         specialize p idx1 (by omega) (by omega)
-- --         split at p
-- --         · simp [bvRes] at p
-- --           simp [p]
-- --           let bvRes := BitVec.addVecAux 0 inputNodes oldParSumBv [] (by omega) (by omega) hw hw' hlenOld (by simp) (by omega)
-- --           have hle' : currNode ≤ inputNodes := by omega
-- --           have := BitVec.addVecAux_prop (i := idx1) (currNode := currNode) (inputNodes := inputNodes) (w := w) (oldParSumBv := oldParSumBv)
-- --                   (newParSumBv := newParSumBv) (by omega) (by omega)
-- --                   hle' heven (by omega) (by omega) (res := bvRes) hacc
-- --           simp [this]
-- --         · omega
-- --       · have := List.getElem_concat_length (i := idx1) (a := elemBv) (l := newParSumBv) (by omega)
-- --         specialize this (by omega)
-- --         simp
-- --         rw [this]
-- --         let bvRes := BitVec.addVecAux 0 inputNodes oldParSumBv [] (by omega) (by omega) hw hw' hlenOld (by omega) (by omega)
-- --         have := bvRes.property
-- --         omega
-- --     · intros idx1 hidx1 idx2 hidx2
-- --       apply hnew
-- --     · intros
-- --       apply helem

-- theorem denote_blastAddVec
--   -- aig inputs
--   {α : Type}
--   [Hashable α] [DecidableEq α]
--   {assign : α → Bool}
--   (aig : AIG α)
--   (usedNodes validNodes w : Nat) (hvalid : validNodes ≤ w)
--   (hused : usedNodes % 2 = 0) (hw : 1 < w)
--   (oldParSum newParSum : RefVecVec aig w w)
--   -- bv inputs
--   (oldParSumBv newParSumBv : List (BitVec w))
--   (hlenOld : oldParSumBv.length = w) (hlenNew : newParSumBv.length = w)
--   -- the elements in newParSumBv with indices smaller than usedNodes/2 are the result of a sum
--   (hbvLt :
--     ∀ (i : Nat) (hlt : i < usedNodes/2) (hlt' : i*2 < w),
--       if h1: i*2 + 1 < w then
--           newParSumBv[i] = oldParSumBv[i*2] + oldParSumBv[i*2 + 1]
--       else
--           newParSumBv[i] = oldParSumBv[i*2]
--   )
--   -- the other elements in newParSumBv are a copy of the values in oldParSumBv
--   (hbvGt :
--     ∀ (i : Nat) (hlt : i < w) (hge : usedNodes/2 ≤ i),
--       newParSumBv[i] = oldParSumBv[i])
--   -- each element in newParSum denotes to the corresponding element in newParSumBv
--   (hold :
--     ∀ (i1 : Nat) (h1 : i1 < w),
--       ∀ (i2 : Nat) (h2 : i2 < w),
--         ⟦aig, (oldParSum.vec[i1]).get i2 h2, assign⟧ = oldParSumBv[i1].getLsbD i2)

--   (hold :
--     ∀ (i1 : Nat) (h1 : i1 < w),
--       ∀ (i2 : Nat) (h2 : i2 < w),
--         ⟦aig, (oldParSum.vec[i1]).get i2 h2, assign⟧ = oldParSumBv[i1].getLsbD i2)
--   :
--   ∀ (i1 : Nat) (h1 : i1 < w),
--     ∀ (i2 : Nat) (h2 : i2 < w),
--     let res := blastAddVec aig usedNodes validNodes oldParSum newParSum hvalid
--     ⟦res.aig,
--      (res.vec.vec[i1]).get i2 h2,
--       assign⟧ =
--     let bvRes := BitVec.addVecAux usedNodes validNodes oldParSumBv newParSumBv hused hw hvalid hlenOld hlenNew
--     (bvRes.val[i1]).getLsbD i2 := by
--   intros i1 h1 i2 h2
--   generalize hres1 : blastAddVec aig usedNodes validNodes oldParSum newParSum hvalid = res1
--   unfold blastAddVec at hres1
--   split at hres1
--   · case _ hsplit =>
--     simp
--     rw [← hres1]
--     by_cases hused2 : usedNodes + 2 < validNodes
--     · let rhs := if h : usedNodes + 1 < validNodes then
--           oldParSum.vec.get ⟨usedNodes + 1, (by omega)⟩ else blastConst aig 0
--       let res := blastAdd aig { lhs := oldParSum.vec.get ⟨usedNodes, (by omega)⟩, rhs := rhs };
--       let aigNew := res.aig;
--       have := denote_blastAddVec
--               (aig := aigNew)
--               (assign := assign)
--               (usedNodes := usedNodes + 2) (validNodes := validNodes) (hvalid := hvalid)
--               (hused := by omega) (hw := hw)
--               (oldParSum := oldParSum.cast (by simp [aigNew, res]; apply AIG.LawfulVecOperator.le_size (f := blastAdd) .. ))
--               (newParSum := RefVecVec.set ((usedNodes + 1) / 2) newParSum (res.vec)
--                                     (by simp [aigNew, res]; apply AIG.LawfulVecOperator.le_size (f := blastAdd) .. ) (by omega))
--               (oldParSumBv := oldParSumBv)
--               (newParSumBv := newParSumBv.set ((usedNodes + 1) / 2) (oldParSumBv[usedNodes] + oldParSumBv[usedNodes + 1]))
--       conv =>
--         rhs
--         unfold BitVec.addVecAux
--         simp only [show usedNodes < validNodes by omega, ↓reduceDIte,
--           show usedNodes + 1 < validNodes by omega, List.get_eq_getElem]
--       rw [this]
--       · intros j hj
--         split
--         · by_cases hjeq : j = (usedNodes)/2
--           · simp [hjeq,
--               show (usedNodes+1)/2 = usedNodes/2 by omega,
--               show (usedNodes)/2 *2 = usedNodes by omega]
--           · have : j < (usedNodes)/2 := by omega
--             specialize hbvLt j this
--             simp only [show j * 2 + 1 < w by omega, ↓reduceDIte] at hbvLt
--             simp only [ne_eq, show ¬(usedNodes + 1) / 2 = j by omega, not_false_eq_true,
--               List.getElem_set_ne]
--             exact hbvLt
--         · omega
--       · intros j hj hle
--         specialize hbvGt j hj (by omega)
--         simp only [ne_eq, show ¬(usedNodes + 1) / 2 = j by omega,
--           not_false_eq_true, List.getElem_set_ne]
--         exact hbvGt
--       · intros j1 hj1 j2 hj2
--         specialize hold j1 hj1 j2 hj2
--         simp [aigNew, res, RefVecVec.cast]
--         sorry
--     · by_cases hsplit' : usedNodes + 1 < validNodes
--       · let rhs := if h : usedNodes + 1 < validNodes then oldParSum.vec.get ⟨usedNodes + 1, (by omega)⟩
--                     else blastConst aig 0#w
--         let res := blastAdd aig { lhs := oldParSum.vec.get ⟨usedNodes, (by omega)⟩, rhs := rhs };
--         let aigNew := res.aig;
--         conv =>
--           rhs
--           unfold BitVec.addVecAux

--           simp [show usedNodes < validNodes by omega, hsplit', List.get_eq_getElem]
--         simp
--         let add := (blastAdd aig
--                 { lhs := oldParSum.vec.get ⟨usedNodes, (by omega)⟩,
--                   rhs :=
--                     rhs})
--         let res := (blastAddVec add.aig
--             (usedNodes + 2) validNodes (oldParSum.cast (by apply AIG.LawfulVecOperator.le_size (f := blastAdd) .. ))
--             (RefVecVec.set ((usedNodes + 1) / 2) newP~arSum add.vec
--               (by apply AIG.LawfulVecOperator.le_size (f := blastAdd) .. ) (by omega))) (by omega)
--         have := denote_blastAddVec
--                     (aig := add.aig)
--                     (assign := assign)
--                     (usedNodes := usedNodes + 2) (validNodes := validNodes) (hvalid := hvalid)
--                     (hused := by omega) (hw := hw)
--                     (oldParSum := oldParSum.cast (by apply AIG.LawfulVecOperator.le_size (f := blastAdd) .. ))
--                     (newParSum := RefVecVec.set ((usedNodes + 1) / 2) newParSum add.vec (by apply AIG.LawfulVecOperator.le_size (f := blastAdd) .. ) (by omega))
--                     (oldParSumBv := oldParSumBv)
--                     (newParSumBv := newParSumBv.set ((usedNodes + 1) / 2) (oldParSumBv[usedNodes] + oldParSumBv[usedNodes + 1]))
--         rw [this]
--         · intros j hj
--           split
--           · by_cases hjeq : j = (usedNodes)/2
--             · simp [hjeq,
--                 show (usedNodes+1)/2 = usedNodes/2 by omega,
--                 show (usedNodes)/2 *2 = usedNodes by omega]
--             · have : j < (usedNodes)/2 := by omega
--               specialize hbvLt j this
--               simp only [show j * 2 + 1 < w by omega, ↓reduceDIte] at hbvLt
--               simp only [ne_eq, show ¬(usedNodes + 1) / 2 = j by omega, not_false_eq_true,
--                 List.getElem_set_ne]
--               exact hbvLt
--           · omega
--         · intros j hj hle
--           specialize hbvGt j hj (by omega)
--           simp only [ne_eq, show ¬(usedNodes + 1) / 2 = j by omega,
--             not_false_eq_true, List.getElem_set_ne]
--           exact hbvGt
--         · intros
--           simp [add]

--           sorry
--         ·
--           sorry
--       · have : usedNodes + 1 = validNodes := by omega
--         rw [← this] at *
--         simp_all

--         let add := (blastAdd aig
--                 { lhs := oldParSum.vec.get ⟨usedNodes, (by omega)⟩,
--                   rhs :=
--                     if h : usedNodes + 1 < validNodes then oldParSum.vec.get ⟨usedNodes + 1, (by omega)⟩
--                     else blastConst aig 0#w })

--         let res := blastAddVec add.aig
--             (usedNodes + 2) validNodes (oldParSum.cast (by apply AIG.LawfulVecOperator.le_size (f := blastAdd) .. ))
--             (RefVecVec.set ((usedNodes + 1) / 2) newParSum add.vec
--               (by apply AIG.LawfulVecOperator.le_size (f := blastAdd) .. ) (by omega)) hvalid

--         conv =>
--           rhs
--           unfold BitVec.addVecAux
--           simp [show usedNodes + 1 = validNodes by omega, show usedNodes < validNodes by omega, hsplit', List.get_eq_getElem]

--         have := denote_blastAddVec
--                     (aig := add.aig)
--                     (assign := assign)
--                     (usedNodes := usedNodes + 2) (validNodes := validNodes) (hvalid := hvalid)
--                     (hused := by omega) (hw := hw)
--                     (oldParSum := oldParSum.cast (by apply AIG.LawfulVecOperator.le_size (f := blastAdd) .. ))
--                     (newParSum := RefVecVec.set ((usedNodes + 1) / 2) newParSum add.vec (by apply AIG.LawfulVecOperator.le_size (f := blastAdd) .. ) (by omega))
--                     (oldParSumBv := oldParSumBv)
--                     (newParSumBv := newParSumBv.set ((usedNodes + 1) / 2) (oldParSumBv[usedNodes]))
--                     (hlenOld := hlenOld) (hlenNew := by simp; omega)

--         rw [this]
--         · simp [show (usedNodes + 1)/2 = validNodes/2 by omega, BitVec.getLsbD_eq_getElem (i := i2) (by omega)]
--         · intros j hj hj'
--           split
--           · by_cases hjeq : j = (usedNodes)/2
--             · simp [hjeq,
--                 show (usedNodes+1)/2 = usedNodes/2 by omega,
--                 show (usedNodes)/2 *2 = usedNodes by omega]
--               sorry
--             · have : j < (usedNodes)/2 := by omega
--               specialize hbvLt j this (by omega)
--               simp only [show j * 2 + 1 < w by omega, ↓reduceDIte] at hbvLt
--               simp only [ne_eq, show ¬(usedNodes + 1) / 2 = j by omega, not_false_eq_true,
--                 List.getElem_set_ne]
--               exact hbvLt
--           · by_cases hjeq : j = (usedNodes + 1) / 2
--             · simp [hjeq,
--                 show (usedNodes+1)/2 = usedNodes/2 by omega,
--                 show (usedNodes)/2 *2 = usedNodes by omega]
--             · have : j < (usedNodes)/2 := by omega
--               specialize hbvLt j this (by omega)
--               simp only [show j * 2 + 1 < w by omega, ↓reduceDIte] at hbvLt
--               simp only [ne_eq, show ¬(usedNodes + 1) / 2 = j by omega, not_false_eq_true,
--                 List.getElem_set_ne]

--               sorry
--         · sorry
--         · sorry

--   · case _ hsplit =>
--     sorry
-- termination_by validNodes - usedNodes
-- -- theorem denote_blastAddVec
-- --   (assign : α → Bool)
-- --   (aigCurr : AIG α) (usedNodes validNodes w: Nat) (hu : usedNodes < validNodes)
-- --   (oldParSum : RefVecVec aigCurr w w) (newParSum : RefVecVec aigCurr w w)
-- --   (heven : usedNodes % 2 = 0) (hin : 1 < w) (hval : validNodes ≤ w)
-- --   -- BitVec input
-- --   (oldParSumBv : List (BitVec w)) (newParSumBv : List (BitVec w))
-- --   (hlenOld : oldParSumBv.length = w) (hlenNew : newParSumBv.length = w)
-- --   -- all the bitvectors in newParSumBv in the valid range are the result of summing two bitvecs in the
-- --   -- old list, while the remaining ones are a copy of the elements in the old bitvec.
-- --   -- the entries until usedNodes + 1)/2 in newParSum denote to newParSumBv
-- --   (haccBv : ∀ (idx1 : Nat) (hidx1 : idx1 < (usedNodes + 1)/2),
-- --         if h1 : idx*2 + 1 < w then
-- --           newParSumBv[idx1] = oldParSumBv[idx1*2] + oldParSumBv[idx1*2 + 1]
-- --         else
-- --           newParSumBv[idx1] = oldParSumBv[idx1*2]
-- --       )
-- --   (hnew :
-- --     ∀ (idx1 : Nat) (hidx1 : idx1 < (usedNodes + 1)/2) (hidx1' : idx1 < w),
-- --       ∀ (idx2 : Nat) (hidx2 : idx2 < w),
-- --         ⟦aigCurr, (newParSum.vec.get ⟨idx1, hidx1'⟩).get idx2 hidx2, assign⟧ =
-- --           (newParSumBv.get ⟨idx1, by omega⟩).getLsbD idx2)
-- --   -- the entries after (usedNodes + 1)/2 in newParSum denote to newParSumBv
-- --   (hnew' :
-- --     ∀ (idx1 : Nat) (hidx1 : (usedNodes + 1)/2 < idx1) (hidx1' : idx1 < w),
-- --       ∀ (idx2 : Nat) (hidx2 : idx2 < w),
-- --         ⟦aigCurr, (newParSum.vec.get ⟨idx1, hidx1'⟩).get idx2 hidx2, assign⟧ =
-- --           (oldParSumBv.get ⟨idx1, by omega⟩ ).getLsbD idx2)
-- --   -- oldParSum denotes to oldParSumBv
-- --   (hold :
-- --     ∀ (idx1 : Nat) (hidx1 : idx1 < w),
-- --       ∀ (idx2 : Nat) (hidx2 : idx2 < w),
-- --         ⟦aigCurr, (oldParSum.vec.get ⟨idx1, by omega⟩).get idx2 hidx2, assign⟧ =
-- --           (oldParSumBv.get ⟨idx1, by omega⟩ ).getLsbD idx2)
-- --         :
-- --     ∀ (idx1 : Nat) (hidx1 : idx1 < w),
-- --       ∀ (idx2 : Nat) (hidx2 : idx2 < w),
-- --         let res := (blastAddVec aigCurr usedNodes validNodes oldParSum newParSum (by omega))
-- --         ⟦res.aig, (res.vec.vec.get ⟨idx1, by omega⟩).get idx2 hidx2, assign⟧  =
-- --         let bvRes:= BitVec.addVecAux usedNodes validNodes newParSumBv oldParSumBv (by omega) hin hval hlenNew hlenOld
-- --         (bvRes.val[idx1]'(by simp [bvRes.property]; omega)).getLsbD idx2
-- --          := by
-- --     intros idx1 hidx1 idx2 hidx2
-- --     generalize hres : blastAddVec aigCurr usedNodes validNodes oldParSum newParSum hval = res
-- --     unfold blastAddVec at hres
-- --     split at hres
-- --     · case _ h =>
-- --         rw [← hres]
-- --         by_cases h1 : usedNodes + 1 < validNodes
-- --         ·
-- --           sorry
-- --         ·
-- --           sorry
-- --     · case _ h => omega

























--     by_cases hcondres : currNode < inputNodes
--     · by_cases hlt' :  currNode + 2 < inputNodes
--       · -- hlt' :  currNode + 2 < inputNodes
--         generalize hres : (blastAddVec aigCurr currNode (inputNodes := inputNodes) (oldParSum := oldParSum)
--                         (newParSum := newParSum) (by omega) (by omega) (by omega) (by omega) (by omega)) = res
--         unfold blastAddVec at hres
--         rw [← hres]
--         rw [dite_cond_eq_true (by simp; omega)]
--         rw [dite_cond_eq_true (by simp; omega)]
--         simp
--         let newRes := (blastAdd aigCurr ⟨oldParSum.vec.get ⟨currNode, (by omega)⟩, oldParSum.vec.get ⟨currNode + 1, (by omega)⟩⟩)
--         let elemBv := oldParSumBv.get ⟨currNode, by omega⟩ + oldParSumBv.get ⟨currNode + 1, by omega⟩
--         have hcast : currNode / 2 + 1 = (currNode + 2) / 2 := by omega
--         have := denote_blastAddVec
--                 (assign := assign)
--                 (aigCurr := newRes.aig)
--                 (currNode := currNode + 2)
--                 (hi := hi) (hle := hlt')
--                 (oldParSum := oldParSum.cast (aig2 := newRes.aig) (by simp [newRes]; exact LawfulVecOperator.le_size aigCurr ..))
--                 (newParSum := ((newParSum.cast (aig2 := newRes.aig)
--                                       (by simp [newRes]; exact LawfulVecOperator.le_size aigCurr ..))).push newRes.vec (by omega))
--                 (heven := by omega)
--                 (hw := hw) (hw' := hw')
--                 (oldParSumBv := oldParSumBv)
--                 (newParSumBv := newParSumBv.concat elemBv)
--                 (hlenOld := by omega)
--                 (hlenNew := by simp; omega)
--                 -- missing: hacc and hnew, to prove
--         rw [this]
--         · simp
--         · -- hacc
--           intros idx hidx hlen
--           simp
--           split
--           · case _ hidx' =>
--             by_cases hfin : idx < newParSumBv.length
--             · rw [List.getElem_append_left (as := newParSumBv) (bs := [elemBv]) hfin]
--               specialize hacc idx hfin
--               simp [hlenNew, hidx'] at hacc
--               exact hacc
-- --             · simp [show idx = newParSumBv.length by omega] at *
-- --               simp [elemBv]
-- --               congr <;> omega
-- --           · case _ hidx' => omega -- contra
-- --         · -- hnew
-- --           intros idx hidx1 idx2 hidx2
-- --           simp
-- --           have := denote_push
-- --                     (acc := (newParSum.cast (aig2 := newRes.aig) (by simp [newRes]; exact LawfulVecOperator.le_size aigCurr ..)))
-- --                     (elem := newRes.vec)
-- --                     (haig := by omega)
-- --                     (aigNew := newRes.aig)
-- --                     (assign := assign)
-- --                     (l := newParSumBv)
-- --                     (bv := elemBv)
-- --                     (hlen := by omega)
-- --           rw [this]
-- --           · simp
--           · simp
--             intros idx1 hidx1 idx2 hidx2
--             have := denote_cast_cast
--                         (aigCurr := aigCurr) (aigNew := newRes.aig) (acc := newParSum) (haig := by simp [newRes]; exact LawfulVecOperator.le_size aigCurr ..) (haig' := by omega)
--                         (assign := assign) (l := newParSumBv) (hlen := by omega)
--             rw [this]
--             · intros idx1 hidx1 idx2 hidx2
--               specialize hnew idx1 (by omega) idx2 (by omega)
--               simp [hnew]
--           · intro idx1 hidx1
--             simp [newRes]
--             have := denote_blastAdd
--                     (input := ⟨oldParSum.vec.get ⟨currNode, (by omega)⟩, oldParSum.vec.get ⟨currNode + 1, by omega⟩⟩)
--             rw [this]
--             · intros idx hidx
--               simp
--               specialize hold currNode (by omega) idx (by omega)
--               exact hold
--             · intros idx hidx
--               simp
--               specialize hold (currNode + 1) (by omega) idx (by omega)
--               exact hold
--         · simp
--           intros idx1 hidx1 idx1 hidx2
--           have := denote_cast
--                         (aigCurr := aigCurr) (aigNew := newRes.aig) (acc := oldParSum) (haig := by simp [newRes]; exact LawfulVecOperator.le_size aigCurr ..)
--                         (assign := assign) (l := oldParSumBv) (hlen := by omega)
--           rw [this]
--           apply hold
--       · -- ¬ hlt' :  currNode + 2 < inputNodes
--         -- rw [← hres]
--         by_cases hlt : currNode + 1 < inputNodes
--         · unfold blastAddVec
--           simp [hlt, hcondres]
--           rw [dite_cond_eq_true (by simp; omega)]
--           rw [dite_cond_eq_true (by simp; omega)]
--           let res' := blastAdd aigCurr ⟨oldParSum.vec.get ⟨currNode, (by omega)⟩, oldParSum.vec.get ⟨currNode + 1, (by omega)⟩⟩;
--           let aig := res'.aig;
--           let add := res'.vec;
--           let oldParSum := oldParSum.cast (aig2 := aig)
--                             (by simp [aig, res']; exact LawfulVecOperator.le_size aigCurr (f := blastAdd) ..)
--           let newParSum := newParSum.cast (aig2 := aig)
--                             (by simp [aig, res']; exact LawfulVecOperator.le_size aigCurr (f := blastAdd) ..)
--           let newVec := newParSum.push add (by simp [aig, res'])
--           generalize hres : blastAddVec res'.aig (currNode + 2) inputNodes oldParSum newVec (by omega) (by omega) hw hw' (by omega) = res
--           unfold blastAddVec at hres
--           simp at hres
--           by_cases hlt' :  currNode + 2 < inputNodes
--           · omega
--           · have : currNode + 2 = inputNodes := by omega
--             simp [hlt'] at hres
--             rw [← hres]
--             simp [newVec]
--             -- have : newLen = (currNode + 2) / 2 - 1 := by omega
--             -- subst this
--             simp_all
--             have := denote_push
--                     -- (acc := (newParSum.cast (aig2 := res'.aig) (by simp [res]; exact Nat.le_refl aig.decls.size)))
--                     (elem := add)
--                     (haig := by sorry)
--                     (aigOld := aigCurr)
--                     (aigNew := aig)
--                     (assign := assign)
--                     (l := newParSumBv)
--                     (bv := oldParSumBv.get ⟨currNode, by omega⟩ + oldParSumBv.get ⟨currNode + 1, by omega⟩)
--                     (hlen := by omega)

--             sorry
--         · -- ¬hlt'
--           -- rw [dite_cond_eq_false (by simp; omega)]
--           unfold blastAddVec
--           simp
--           rw [dite_cond_eq_true (by simp [hcondres])]
--           rw [dite_cond_eq_false (by simp; omega)]
--           have : currNode + 1 = inputNodes := by omega
--           simp [this] at *
--           let zero := blastConst aigCurr (w := w) 0
--           let res' := blastAdd aigCurr ⟨oldParSum.vec.get ⟨currNode, (by omega)⟩, zero⟩;
--           let aig := res'.aig;
--           let add := res'.vec;
--           let oldParSum := oldParSum.cast (aig2 := aig)
--                             (by simp [aig, res']; exact LawfulVecOperator.le_size aigCurr (f := blastAdd) ..)
--           let newParSum := newParSum.cast (aig2 := aig)
--                             (by simp [aig, res']; exact LawfulVecOperator.le_size aigCurr (f := blastAdd) ..)
--           let newVec := newParSum.push add (by simp [aig, res'])
--           generalize hres : blastAddVec res'.aig (currNode + 2) inputNodes oldParSum newVec (by omega) (by omega) hw hw' (by omega) = res
--           unfold blastAddVec at hres
--           rw [← hres]
--           simp [hlt'] at hres
--           rw [dite_cond_eq_false (by simp; omega)]
--           simp [newVec]

--           sorry
--     · omega

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
