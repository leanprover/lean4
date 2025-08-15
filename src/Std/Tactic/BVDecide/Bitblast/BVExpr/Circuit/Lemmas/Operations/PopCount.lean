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
  (i : Nat) (hi : i < w) (x : BitVec w) (hw : 0 < w) :
    let res := (BitVec.extractAndExtendPopulateAux 0 x [] (by intros i h h'; simp at h') (by omega) (by simp))
    res.val[i]'(by have := res.property; omega) = BitVec.setWidth w (BitVec.extractLsb' i 1 x) := by
  let out :=  (BitVec.extractAndExtendPopulateAux 0 x [] (by intros i h h'; simp at h') (by omega) (by simp))
  have := (out.property).right
  specialize this i hi (by omega)
  simp only
  simp [out] at this
  simp [this]

theorem blastExtractAndExtendPopulate_denote_eq'
  (assign : α → Bool)
  (aigAcc : AIG α) (start w : Nat) (xc : AIG.RefVec aigAcc w) (x : BitVec w) (acc : RefVecVec aigAcc w start) (hw : start + 1 < w)
  (hacc' : ∀ (idx1 : Nat) (hidx1 : idx1 < start),
            ∀ (idx2 : Nat) (hidx2 : idx2 < w),
              let newElem := blastExtractAndExtend aigAcc xc (start)
              ⟦newElem.aig, ((acc.cast (by apply extractAndExtend_le_size)).vec.get ⟨idx1, hidx1⟩).get idx2 hidx2, assign⟧ =
              ((BitVec.extractAndExtendPopulateAux 0 x [] (by simp) (by omega) (by simp)).val.get
                ⟨idx1, by simp [(BitVec.extractAndExtendPopulateAux 0 x []
                        (by intros i hi hl; simp at hl)
                        (by omega) (by simp)).property]; exact Nat.lt_trans hidx1 (by omega)⟩).getLsbD idx2)
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
        let bvRes := BitVec.extractAndExtendPopulateAux 0 x [] (by intros i hi hl; simp at hl) (by omega) (by simp)
      (bvRes.val.get ⟨idx1, by simp [bvRes.property]; omega⟩).getLsbD idx2 := by
  -- Introduce a variable `ext` for `blastExtractAndExtend`
  intros idx1 hidx1 idx2 hidx2
  let elem := blastExtractAndExtend aigAcc xc start
  let bvRes := BitVec.extractAndExtendPopulateAux 0 x [] (by intros i hi hl; simp at hl) (by omega) (by simp)
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
      let res' := BitVec.extractAndExtendPopulateAux 0 x [] (by intros i hi hl; simp at hl) (by omega) (by simp)
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
      let res := BitVec.extractAndExtendPopulateAux 0 x [] (by intros i hi hl; simp at hl) (by omega) (by simp)
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

theorem BitVec.addVecAux_prop
  (oldParSumBv : List (BitVec w)) (newParSumBv : List (BitVec w))
  (hlen : oldParSumBv.length = inputNodes)
  (hlen' : newParSumBv.length = currNode/2)
  (hle : currNode ≤ inputNodes)
  (heven : currNode %2 = 0)
  (hlt : i * 2 + 1 < oldParSumBv.length)
  (hlt' : i < newParSumBv.length)
  (res : {l : List (BitVec w) // (l.length = (inputNodes + 1)/2) ∧
       (∀ i (hi : i < l.length) (hl : l.length = (inputNodes + 1)/2),
        if hc : i*2 + 1 < oldParSumBv.length then
          l.get ⟨i, by simp [hl]; omega⟩ = oldParSumBv.get ⟨i*2, by omega⟩ + oldParSumBv.get ⟨i*2 + 1, by omega⟩
        else
          l.get ⟨i, by simp [hl]; omega⟩ = oldParSumBv.get ⟨i*2, by omega⟩)
        })
  (hacc : ∀ (i_1 : Nat) (hi : i_1 < newParSumBv.length) (_ : newParSumBv.length = currNode / 2),
            if hc : i_1 * 2 + 1 < oldParSumBv.length then
              newParSumBv.get ⟨i_1, (by omega)⟩ = oldParSumBv.get ⟨i_1 * 2, (by omega)⟩ + oldParSumBv.get ⟨i_1 * 2 + 1, hc⟩
                else newParSumBv.get ⟨i_1, (by omega)⟩ = oldParSumBv.get ⟨i_1 * 2, (by omega)⟩) :
    newParSumBv[i]'hlt' = (oldParSumBv[i * 2]'(by omega) + oldParSumBv[i * 2 + 1]'hlt):= by
  have ⟨plen, pp⟩ := res.property
  specialize pp i (by omega) (by omega)
  simp [hlt] at pp
  specialize hacc i (by omega) (by omega)
  simp [hlt] at hacc
  apply hacc

theorem blastAddVec_denote_step
  -- blastAddVec input
  (aigOld : AIG α) (currNode w: Nat) (hi : 1 < inputNodes) (hle : currNode < inputNodes)
  (oldParSum : RefVecVec aigOld w inputNodes) (newParSum : RefVecVec aigOld w (currNode/2))
  (heven : currNode %2 = 0)  (hw : inputNodes ≤ w) (hw' : 1 < inputNodes)
  (elem : RefVecEntry α w)
  (helem' :
    if hc : currNode + 1 < inputNodes then
      elem = blastAdd aigOld (w := w) ⟨oldParSum.vec.get ⟨currNode, (by omega)⟩, oldParSum.vec.get ⟨currNode + 1, (by omega)⟩⟩
    else
      let zero := blastConst aigOld (w := w) 0
      elem = blastAdd aigOld (w := w) ⟨oldParSum.vec.get ⟨currNode, (by omega)⟩, zero⟩)
  -- BitVec input
  (oldParSumBv : List (BitVec w)) (newParSumBv : List (BitVec w)) (elemBv : BitVec w)
  (hlenOld : oldParSumBv.length = inputNodes) (hlenNew : newParSumBv.length = currNode/2)
  (hacc : ∀ (i_1 : Nat) (hi : i_1 < newParSumBv.length),
    newParSumBv.length = currNode / 2 →
      if hc : i_1 * 2 + 1 < oldParSumBv.length then
        newParSumBv.get ⟨i_1, hi⟩ = oldParSumBv.get ⟨i_1 * 2, (by omega)⟩ + oldParSumBv.get ⟨i_1 * 2 + 1, hc⟩
      else newParSumBv.get ⟨i_1, hi⟩ = oldParSumBv.get ⟨i_1 * 2, (by omega)⟩)
  -- newParSum denotes to newParSumBv
  (hnew :
    ∀ (idx1 : Nat) (hidx1 : idx1 < currNode/2),
      ∀ (idx2 : Nat) (hidx2 : idx2 < w),
        ⟦elem.aig, ((newParSum.cast (aig2 := elem.aig)
                    (by split at helem' <;> (simp [helem']; apply AIG.LawfulVecOperator.le_size (f := blastAdd)))
                    ).vec.get ⟨idx1, hidx1⟩).get idx2 hidx2, assign⟧ =
          (newParSumBv.get ⟨idx1, by simp [hlenNew]; omega⟩ ).getLsbD idx2)
  -- elem denotes to elemBv
  (helem :
    ∀ (idx1 : Nat) (hidx1 : idx1 < w),
      ⟦elem.aig, elem.vec.get idx1 hidx1, assign⟧ = elemBv.getLsbD idx1
    )
        :
    ∀ (idx1 : Nat) (hidx1 : idx1 < (currNode + 1)/2),
      ∀ (idx2 : Nat) (hidx2 : idx2 < w),
        ⟦elem.aig, ((newParSum.push elem.vec (by split at helem' <;> (simp [helem']; apply AIG.LawfulVecOperator.le_size (f := blastAdd)))).vec.get ⟨idx1, by omega⟩).get idx2 hidx2 , assign⟧ =
          let bvRes := BitVec.addVecAux 0 inputNodes oldParSumBv [] (by omega) (by omega) (by omega) (by omega) hlenOld (by simp) (by simp)
          (bvRes.val.get ⟨idx1, by have := bvRes; omega⟩).getLsbD idx2 := by
    intros idx1 hidx1 idx2 hidx2
    have := push_denote_eq (assign := assign) (w := w) (n := currNode/2) (aigNew := elem.aig) (aigOld := aigOld)
          (acc := newParSum) (elem := elem.vec) (l := newParSumBv) (bv := elemBv)
          (by split at helem' <;> (simp [helem']; apply AIG.LawfulVecOperator.le_size (f := blastAdd))) (by omega)
    rw [this]
    · by_cases hlast : idx1 < newParSumBv.length
      · simp
        have := List.getElem_append_left (as := newParSumBv) (bs := [elemBv]) (i := idx1) (h := by omega) (h' := by simp; omega)
        simp [this]
        let bvRes := BitVec.addVecAux 0 inputNodes oldParSumBv [] (by omega) (by omega) hw hw' hlenOld (by simp) (by omega)
        have ⟨len, p⟩ := bvRes.property
        specialize p idx1 (by omega) (by omega)
        split at p
        · simp [bvRes] at p
          simp [p]
          let bvRes := BitVec.addVecAux 0 inputNodes oldParSumBv [] (by omega) (by omega) hw hw' hlenOld (by simp) (by omega)
          have hle' : currNode ≤ inputNodes := by omega
          have := BitVec.addVecAux_prop (i := idx1) (currNode := currNode) (inputNodes := inputNodes) (w := w) (oldParSumBv := oldParSumBv)
                  (newParSumBv := newParSumBv) (by omega) (by omega)
                  hle' heven (by omega) (by omega) (res := bvRes) hacc
          simp [this]
        · omega
      · have := List.getElem_concat_length (i := idx1) (a := elemBv) (l := newParSumBv) (by omega)
        specialize this (by omega)
        simp
        rw [this]
        let bvRes := BitVec.addVecAux 0 inputNodes oldParSumBv [] (by omega) (by omega) hw hw' hlenOld (by omega) (by omega)
        have := bvRes.property
        omega
    · intros idx1 hidx1 idx2 hidx2
      apply hnew
    · intros
      apply helem

theorem blastAddVec_denote
  -- blastAddVec input
  (aig : AIG α) (currNode w: Nat) (hi : 1 < inputNodes) (hle : currNode < inputNodes)
  (oldParSum : RefVecVec aig w inputNodes) (newParSum : RefVecVec aig w (currNode/2))
  (heven : currNode %2 = 0)  (hw : inputNodes ≤ w) (hw' : 1 < inputNodes)

  (oldParSumBv : List (BitVec w)) (newParSumBv : List (BitVec w)) (elemBv : BitVec w)
  (hlenOld : oldParSumBv.length = inputNodes) (hlenNew : newParSumBv.length = currNode/2)
  (hold :
    ∀ (idx1 : Nat) (hidx1 : idx1 < inputNodes),
      ∀ (idx2 : Nat) (hidx2 : idx2 < w),
        ⟦aig, (oldParSum.vec.get ⟨idx1, hidx1⟩).get idx2 hidx2, assign⟧ =
          (oldParSumBv.get ⟨idx1, by simp [hlenOld]; omega⟩ ).getLsbD idx2)
        :
    ∀ (idx1 : Nat) (hidx1 : idx1 < (currNode + 1)/2),
      ∀ (idx2 : Nat) (hidx2 : idx2 < w),
        let outpuVec : Vector (AIG.RefVec aig w) 0 := Vector.emptyWithCapacity 0
        let outpuRefVec : RefVecVec aig w 0 := {vec := outpuVec}
        let res := blastAddVec aig (currNode := 0) (inputNodes := inputNodes) (oldParSum := oldParSum)
                                    (newParSum := outpuRefVec) (by omega) (by omega) (by omega) (by omega)
        ⟦res.aig, (res.vec.vec.get ⟨idx1, by omega⟩).get idx2 hidx2 , assign⟧  =
          let bvRes := BitVec.addVecAux 0 inputNodes oldParSumBv [] (by omega) (by omega) (by omega) (by omega) hlenOld (by simp) (by simp)
          (bvRes.val.get ⟨idx1, by have := bvRes; omega⟩).getLsbD idx2 := by
    intros idx1 hidx1 idx2 hidx2
    let outpuVec : Vector (AIG.RefVec aig w) 0 := Vector.emptyWithCapacity 0
    let outpuRefVec : RefVecVec aig w 0 := {vec := outpuVec}
    generalize hres : blastAddVec aig 0 inputNodes oldParSum outpuRefVec (by omega) (by omega) hw hw' = res
    unfold blastAddVec at hres
    -- dsimp only [show 0 < inputNodes by omega, Nat.reduceAdd, Nat.reduceDiv, Nat.zero_add, hi,
      -- Lean.Elab.WF.paramLet, BitVec.ofNat_eq_ofNat] at hres
    split at hres
    · case _ hres =>
      rw [hres]

      sorry
    -- let outpuVec : Vector (AIG.RefVec aig w) 0 := Vector.emptyWithCapacity 0
    -- let outpuRefVec : RefVecVec aig w 0 := {vec := outpuVec}
    -- have := blastAddVec_denote_step (aigOld := aig) (assign := assign)
    --       (inputNodes := inputNodes) (currNode := 0) (w := w) (hi := by omega)
    --       (hle := by omega) (oldParSum := oldParSum) (newParSum := outpuRefVec)
    --       (heven := by omega) (hw := by omega) (hw' := by omega) (elem := lastElem)
    --       (helem' := by sorry) (newParSumBv := newParSumBv) (elemBv := sorry)
    --       (oldParSumBv := oldParSumBv) (hlenOld := by omega) (hlenNew := by simp_all; sorry)
    · sorry

  -- intros idx1 hidx1 idx2 hidx2

  -- unfold blastAddVec
  -- let lastElem :=
  --   if hc2 : 0 + 1 < inputNodes then
  --     blastAdd aig { lhs := oldParSum.vec.get ⟨0, (by omega)⟩, rhs := oldParSum.vec.get ⟨1, hc2⟩ }
  --   else
  --     let zero := blastConst aig 0;
  --     blastAdd aig { lhs := oldParSum.vec.get ⟨0, (by omega)⟩, rhs := zero };
  -- have := blastAddVec_denote_step (aigOld := aig) (assign := assign)
  --         (inputNodes := inputNodes) (currNode := 0) (w := w) (hi := by omega)
  --         (hle := by omega) (oldParSum := oldParSum) (newParSum := outpuRefVec)
  --         (heven := by omega) (hw := by omega) (hw' := by omega) (elem := lastElem)
  --         (helem' := by sorry) (newParSumBv := newParSumBv) (elemBv := sorry)
  --         (oldParSumBv := oldParSumBv) (hlenOld := by omega) (hlenNew := by simp_all; sorry)


theorem denote_blastAddVec
  (assign : α → Bool)
  -- hypotheses necessary for BitVec.addVecAux

  (aig : AIG α) (start w : Nat) (xc : AIG.RefVec aig w) (x : BitVec w) (acc : RefVecVec aig w start) (hw : start + 1 < w)
  (hle : inputNodes ≤ w) (hlt : 1 < inputNodes) (heven : currNode % 2 = 0)
  (oldParSumBv : { l : List (BitVec w) // l.length = inputNodes ∧
                    ∀ (i : Nat) (hi : i < inputNodes) (hl : l.length = inputNodes), l.get ⟨i, (by omega)⟩ = BitVec.zeroExtend w (BitVec.extractLsb' i 1 x) })
  -- denote inputs
  (oldParSum : RefVecVec aig w inputNodes) (newParSum : RefVecVec aig w (currNode/2))
  -- (hacc' : ∀ (idx1 : Nat) (hidx1 : idx1 < start),
  --           ∀ (idx2 : Nat) (hidx2 : idx2 < w),
  --             let newElem := blastExtractAndExtend aigAcc xc (start)
  --             ⟦newElem.aig, ((acc.cast (by apply extractAndExtend_le_size)).vec.get ⟨idx1, hidx1⟩).get idx2 hidx2, assign⟧ =
  --             ((BitVec.addVecAux 0 x [] (by simp) (by omega) (by simp)).val.get
  --               ⟨idx1, by simp [(BitVec.addVecAux 0 x []
  --                       (by intros i hi hl; simp at hl)
  --                       (by omega) (by simp)).property]; exact Nat.lt_trans hidx1 (by omega)⟩).getLsbD idx2)
  (output : Vector (AIG.RefVec aig w) 0)
  (houtput : output = Vector.emptyWithCapacity 0)
  (outputRefVec : RefVecVec aig w 0 )
  (houtputRefVec : outputRefVec = {vec := output})
  (parSum : RefVecVec aig w inputNodes)
  (hx : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, xc.get idx hidx, assign⟧ = x.getLsbD idx)
   :
    ∀ (idx1 : Nat) (hidx1 : idx1 < (inputNodes + 1)/2),
      ∀ (idx2 : Nat) (hidx2 : idx2 < w),
      let res := blastAddVec aig (currNode := 0) (inputNodes := inputNodes) (oldParSum := parSum) (newParSum := outputRefVec) (heven := by omega) (by omega) (by omega) (by omega)
      ⟦
        res.aig,
        ((res).vec.vec.get ⟨idx1, hidx1⟩).get idx2 hidx2,
        assign
      ⟧ =
      let bvRes := BitVec.addVecAux (w := w) (currNode := 0) (inputNodes := inputNodes) (oldParSum := oldParSumBv.val)
          (newParSum := []) (heven := by simp) (hle := by omega) (hw := hle) (hw' := hlt)
          (hlen := by have ⟨hlen,hp⟩:= oldParSumBv.property; exact hlen) (hlen' := by simp)
          (by intros i hi hl; simp at hi)
      (bvRes.val.get ⟨idx1, by have ⟨hlen,hp⟩:= bvRes.property; omega⟩).getLsbD idx2 := by
    intros idx1 hidx1 idx2 hidx2
    generalize hres : blastAddVec aig (currNode := 0) (inputNodes := inputNodes) (oldParSum := parSum) (newParSum := outputRefVec) (by omega) (by omega) (by omega) (by omega) = res
    unfold blastAddVec at hres
    simp [show 1 < inputNodes by omega, show 0 < inputNodes by omega] at hres

    -- split at hres
    -- · case _ hc =>
    --   rw [← hres]
    --   simp
    --   have := blastAddVec_denote_even (aigOld := aig) (assign := assign) (inputNodes := inputNodes) (currNode := currNode) (w := w)
    --           (hi := by omega) (oldParSum := oldParSum) (newParSum := newParSum) (by omega) (by omega) (by omega) (by omega)


    sorry
    -- · sorry


@[simp]
theorem denote_blastPopCount (aig : AIG α) (xc : RefVec aig w) (x : BitVec w) (assign : α → Bool)
      (hx : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, xc.get idx hidx, assign⟧ = x.getLsbD idx)
      :
      ∀ (idx : Nat) (hidx : idx < w),
        ⟦(blastPopCount aig xc).aig, (blastPopCount aig xc).vec.get idx hidx, assign⟧
          =
        (BitVec.popCountAuxRec x 0 0).getLsbD idx := by
  sorry



end blastPopCount
end bitblast
end BVExpr

end Std.Tactic.BVDecide
