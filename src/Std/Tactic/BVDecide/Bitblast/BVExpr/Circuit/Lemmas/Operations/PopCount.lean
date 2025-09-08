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
at step`n` represents the portion of the extracted and zero-extended nodes in the AIG constructed for
a certain bit.
-/

namespace Std.Tactic.BVDecide

open Std.Sat
open Std.Sat.AIG

namespace BVExpr

namespace bitblast
namespace blastPopCount

variable [Hashable α] [DecidableEq α]

theorem denote_append {aig : AIG α} {n m : Nat} (assign : α → Bool)
  (acc : AIG.RefVec aig n) (elem : AIG.RefVec aig m)
  (l : BitVec n) (bv : BitVec m)
  (hvec : ∀ (idx1 : Nat) (hidx1 : idx1 < n),
      ⟦aig, acc.get idx1 hidx1, assign⟧ = l.getLsbD idx1)
  (helem : ∀ (idx1 : Nat) (hidx1 : idx1 < m),
      ⟦aig, elem.get idx1 hidx1, assign⟧ = (bv.getLsbD idx1))
  : ∀ (idx1 : Nat) (hidx1 : idx1 < n + m),
      ⟦aig, (RefVec.append (lhs := acc) (rhs := elem)).get idx1 hidx1, assign⟧ =
      (BitVec.append (msbs := bv) (lsbs := l)).getLsbD idx1 := by
  intros idx1 hidx1
  simp only [RefVec.get_append, BitVec.append_eq, BitVec.getLsbD_append]
  by_cases hidx : idx1 < n
  · simp [hidx]
    apply hvec
  · simp [hidx]
    apply helem

theorem denote_blastExtractAndExtend (aig : AIG α) (xc : AIG.RefVec aig w) (x : BitVec w) (start : Nat)
    (hx : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, xc.get idx hidx, assign⟧ = x.getLsbD idx) :
  ∀ (idx : Nat) (hidx : idx < w),
    ⟦
      (blastExtractAndExtend aig xc start).aig,
      (blastExtractAndExtend aig xc start).vec.get idx hidx,
      assign
     ⟧ = (BitVec.zeroExtend w (BitVec.extractLsb' start 1 x)).getLsbD idx := by
  intros idx hidx
  generalize hext: blastExtractAndExtend aig xc start = res
  unfold blastExtractAndExtend at hext
  dsimp only [Lean.Elab.WF.paramLet] at hext
  rw [← hext]
  simp only [denote_blastZeroExtend, Nat.lt_one_iff, denote_blastExtract, dite_eq_ite,
    Bool.if_false_right, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_extractLsb']
  split
  · by_cases hidx0 : idx = 0
    · simp [hidx0, show 0 < w by omega, hx]
    · simp [hidx0]
  · intros
    simp [show w ≤ start + idx by omega]

theorem blastExtractAndExtend_denote_mem_prefix {w : Nat} (aig : AIG α) (curr : Nat)
    (xc : RefVec aig w) hstart :
    ⟦
      (blastExtractAndExtend aig xc curr).aig,
      ⟨start, inv, by apply Nat.lt_of_lt_of_le; exact hstart; apply extractAndExtend_le_size⟩,
      assign
    ⟧
      =
    ⟦aig, ⟨start, inv, hstart⟩, assign⟧ := by
  apply denote.eq_of_isPrefix (entry := ⟨aig, start, inv, hstart⟩)
  apply IsPrefix.of
  · intros
    apply extractAndExtend_decl_eq
  · intros
    apply extractAndExtend_le_size

theorem BitVec.getLsbD_extractAndExtend_of_le_of_lt (w idx currIdx : Nat) (hw : 0 < w) (x : BitVec w)
    (hlt : idx < w * (currIdx + 1)) (hle : w * currIdx ≤ idx) :
    (BitVec.zeroExtend w (BitVec.extractLsb' currIdx 1 x)).getLsbD (idx - w * currIdx) =
    (BitVec.extractAndExtendPopulateAux 0 x 0#0 (by omega)).getLsbD idx := by
  induction currIdx generalizing w
  · case zero =>
    simp
    unfold BitVec.extractAndExtendPopulateAux
    simp
    sorry
  ·
    sorry


theorem denote_blastExtractAndExtendPopulate
  (assign : α → Bool)
  (aig : AIG α) (currIdx w : Nat) (xc : AIG.RefVec aig w) (x : BitVec w)
  (acc : AIG.RefVec aig (w * currIdx)) (hlt : currIdx ≤ w)
  -- the bits added already denote to the corresponding entry in acc
  (hacc : ∀ (idx : Nat) (hidx : idx < w * currIdx),
              ⟦aig, acc.get idx hidx, assign⟧ =
              (BitVec.extractAndExtendPopulateAux 0 x 0#0 (by omega)).getLsbD idx )
  (hx : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, xc.get idx hidx, assign⟧ = x.getLsbD idx)
   :
    ∀ (idx : Nat) (hidx : idx < w * w),
      ⟦
        (blastExtractAndExtendPopulate aig currIdx xc acc hlt).aig,
        (blastExtractAndExtendPopulate aig currIdx xc acc hlt).vec.get idx hidx,
        assign
      ⟧ =
        (BitVec.extractAndExtendPopulateAux 0 x 0#0 (by omega)).getLsbD idx := by
  intros idx hidx
  generalize hgen : blastExtractAndExtendPopulate aig currIdx xc acc hlt = gen
  unfold blastExtractAndExtendPopulate at hgen
  split at hgen
  · case _ h =>
    rw [← hgen]
    let res := blastExtractAndExtend aig xc currIdx
    have hcast : w + w * currIdx = w * (currIdx + 1) := by simp [Nat.mul_add]; omega
    have := denote_blastExtractAndExtendPopulate
            (assign := assign)
            (aig := res.aig)
            (currIdx := currIdx + 1)
            (w := w)
            (xc := xc.cast (by simp [res]; apply extractAndExtend_le_size))
            (x := x)
            (acc := (acc.cast (by simp [res]; apply extractAndExtend_le_size)).append res.vec)
            (hlt := by omega)
    rw [this]
    · intros idx hidx
      simp only [res, RefVec.get_append]
      by_cases hidx' : idx < w * currIdx
      · rw [dite_cond_eq_true (by simp [hidx'])]
        specialize hacc idx hidx'
        rw [blastExtractAndExtend_denote_mem_prefix (xc := xc)]
        apply hacc
      · rw [dite_cond_eq_false (by simp [hidx'])]
        rw [denote_blastExtractAndExtend (xc := xc) (x := x)]
        · simp at hidx'
          rw [BitVec.getLsbD_extractAndExtend_of_le_of_lt (hlt := hidx) (hle := hidx')]
          omega
        · intros j hj
          apply hx
    · intros i hi
      simp only [res]
      rw [blastExtractAndExtend_denote_mem_prefix (xc := xc)]
      apply hx
  · case _ h =>
    rw [← hgen]
    have : currIdx = w := by omega
    simp [this] at *
    specialize hacc idx hidx
    rw [← hacc]
    congr
    · omega
    · simp_all
      exact
        eqRec_heq
          (blastExtractAndExtendPopulate._proof_6 currIdx
            (blastExtractAndExtendPopulate._proof_5 currIdx hlt h))
          acc
    · simp_all

theorem blastAddVec_denote_mem_prefix {w : Nat} (aig : AIG α)
    (oldParSum : AIG.RefVec aig (validNodes * w)) (newParSum : AIG.RefVec aig ((usedNodes / 2) * w)) hstart
    (hval : validNodes ≤ w) (hused : usedNodes ≤ validNodes + 1) (hmod : usedNodes % 2 = 0)
     :
    ⟦
      (blastAddVec aig usedNodes validNodes oldParSum newParSum hval hused hmod).aig,
      ⟨start, inv, by apply Nat.lt_of_lt_of_le; exact hstart; apply addVec_le_size⟩,
      assign
    ⟧
      =
    ⟦aig, ⟨start, inv, hstart⟩, assign⟧ := by
  apply denote.eq_of_isPrefix (entry := ⟨aig, start, inv, hstart⟩)
  apply IsPrefix.of
  · intros
    apply addVec_decl_eq
  · intros
    apply addVec_le_size


theorem BitVec.getLsbD_addVecAux_of_lt (w usedNodes validNodes idx : Nat)
    (hw : 1 < w)
    (hval : validNodes ≤ w)
    (oldParSumBv : BitVec (validNodes * w))
    (bvl : BitVec (usedNodes / 2 * w))
    (bvel : BitVec w)
    (hbvl : bvl = BitVec.extractLsb' 0 (usedNodes / 2 * w)
                          (let hcastZero : 0 = 0 / 2 * w := by omega
                                (BitVec.addVecAux 0 validNodes hw oldParSumBv (hcastZero▸0#0) (by intros; omega) (by omega) (by omega) (by omega)).val))
    (hbvel : bvel = BitVec.extractLsb' (usedNodes / 2 * w) w
                          (let hcastZero : 0 = 0 / 2 * w := by omega
                                (BitVec.addVecAux 0 validNodes hw oldParSumBv (hcastZero▸0#0) (by intros; omega) (by omega) (by omega) (by omega)).val))
    (hlt : idx < (usedNodes / 2 * w) + w) :
    let hcastZero : 0 = 0 / 2 * w := by omega
    (bvel ++ bvl).getLsbD idx = (BitVec.addVecAux 0 validNodes hw oldParSumBv (hcastZero ▸ 0#0) (by intros; omega) hval (by omega) (by omega)).val.getLsbD idx := by
  let hcastZero : 0 = 0 / 2 * w := by omega
  have ⟨_, proof⟩ := (BitVec.addVecAux 0 validNodes hw oldParSumBv (hcastZero ▸ 0#0) (by intros; omega) hval (by omega) (by omega))
  sorry


theorem BitVec.getLsbD_addVecAux_eq_add (w usedNodes validNodes : Nat)
  (hw : 1 < w)
  (oldParSumBv : BitVec (validNodes * w))
  (hval : validNodes ≤ w) (hused : usedNodes < validNodes) :
  ∀ currIdx (hcurr : currIdx < w),
    ∀ i (hi : i < w),
    let rhs := if h : currIdx * 2 + 1 < validNodes then
                  BitVec.extractLsb' ((currIdx * 2 + 1) * w) w oldParSumBv
                else 0#w
    let lhs := BitVec.extractLsb' (currIdx * 2 * w) w oldParSumBv
    (lhs + rhs).getLsbD i =
    let hcastZero : 0 = 0 / 2 * w := by omega
    (BitVec.addVecAux 0 validNodes hw oldParSumBv (hcastZero ▸ 0#0) (by intros; omega) hval (by omega) (by omega)).val.getLsbD (i + currIdx * w) := by sorry






-- lhsbv : BitVec w := BitVec.extractLsb' (usedNodes * w) w bvRes
-- rhsbv : BitVec w := if usedNodes + 1 < w then BitVec.extractLsb' ((usedNodes + 1) * w) w bvRes else 0#w
-- ⊢ (lhsbv + rhsbv)[idx1] =
--   (BitVec.addVecAux 0 validNodes oldParSumBv (hcastZero ▸ 0#0) hval ⋯ ⋯).getLsbD (usedNodes / 2 * w + idx1)


theorem denote_blastAddVec
  (aig : AIG α) (usedNodes validNodes : Nat) (hw : 1 < w)
  (oldParSum : AIG.RefVec aig (validNodes * w)) (newParSum : AIG.RefVec aig ((usedNodes / 2) * w))
  (hval : validNodes ≤ w) (hused : usedNodes ≤ validNodes + 1) (hmod : usedNodes % 2 = 0)
  (oldParSumBv : BitVec (validNodes * w))
  -- the bits added already denote to the corresponding entry in acc
  (hold : ∀ (idx : Nat) (hidx : idx < validNodes * w),
          ⟦aig, oldParSum.get idx hidx, assign⟧ = oldParSumBv.getLsbD idx)
  (hnew : ∀ (idx : Nat) (hidx : idx < (usedNodes / 2) * w),
          ⟦aig, newParSum.get idx hidx, assign⟧ =
      have hcastZero : 0 = 0 / 2 * w := by omega
      (BitVec.addVecAux 0 validNodes hw oldParSumBv (hcastZero▸0#0) (by intros; omega) (by omega) (by omega) (by omega)).val.getLsbD idx ) :
    ∀ (idx : Nat) (hidx : idx < (validNodes + 1) / 2 * w),
      ⟦
        (blastAddVec aig usedNodes validNodes oldParSum newParSum hval hused hmod).aig,
        (blastAddVec aig usedNodes validNodes oldParSum newParSum hval hused hmod).vec.get idx hidx,
        assign
      ⟧ =
        have hcastZero : 0 = 0 / 2 * w := by omega
      (BitVec.addVecAux 0 validNodes hw oldParSumBv (hcastZero▸0#0) (by intros; omega) (by omega) (by omega) (by omega)).val.getLsbD idx := by
  intros idx hidx
  generalize hgen : blastAddVec aig usedNodes validNodes oldParSum newParSum hval hused hmod = res
  unfold blastAddVec at hgen
  split at hgen
  · case _ hgen'  =>
    rw [← hgen]
    expose_names
    rw [denote_blastAddVec]
    · -- hold
      intros idx hidx
      specialize hold idx hidx
      rw [AIG.LawfulVecOperator.denote_mem_prefix (f := blastAdd)]
      rw [AIG.LawfulVecOperator.denote_mem_prefix (f := blastExtract)]
      · simp [hold]
      · simp
        exact (oldParSum.get idx hidx).hgate
    · -- hnew
      intros idx hidx

      · simp
        expose_names
        let res := (blastAdd (blastExtract aig { w := validNodes * w, vec := oldParSum, start := usedNodes * w }).aig
                    { lhs := (blastExtract aig { w := validNodes * w, vec := oldParSum, start := usedNodes * w }).vec,
                      rhs := (if usedNodes + 1 < validNodes then (blastExtract aig
                                  { w := validNodes * w, vec := oldParSum, start := (usedNodes + 1) * w }).vec
                                else blastConst aig 0#w).cast (by apply LawfulVecOperator.le_size (f := blastExtract))})

        have h1 : usedNodes / 2 * w + w = (usedNodes + 2) / 2 * w := by
            rw [show usedNodes / 2 * w + w = usedNodes / 2 * w + 1 * w by omega]
            rw [← Nat.add_mul]
            simp

        let elem := (blastAdd (blastExtract aig { w := validNodes * w, vec := oldParSum, start := usedNodes * w }).aig
                    { lhs := (blastExtract aig { w := validNodes * w, vec := oldParSum, start := usedNodes * w }).vec,
                      rhs :=
                        (if usedNodes + 1 < validNodes then
                              (blastExtract aig
                                  { w := validNodes * w, vec := oldParSum, start := (usedNodes + 1) * w }).vec
                            else blastConst aig 0#w).cast (by apply LawfulVecOperator.le_size (f := blastExtract))})

        have : (h1▸ ((newParSum.cast (by simp [elem]; apply LawfulVecOperator.le_size)).append elem.vec)).get idx hidx =
                      ((newParSum.cast (by simp [elem]; apply LawfulVecOperator.le_size)).append elem.vec).get idx (by simp_all) := by
                congr 2
                · omega
                · apply eqRec_heq h1
                · exact heq_of_eqRec_eq (congrArg (LT.lt idx) (id (Eq.symm h1))) rfl
        have hcastZero : 0 = 0 / 2 * w := by omega
        rw [this]
        have  : 0 = 0 / 2 * w := by omega
        let bvRes:= (BitVec.addVecAux 0 validNodes hw oldParSumBv (hcastZero ▸ 0#0) (by intros; omega) hval (by omega) (by omega))


        have := denote_append (assign := assign) (elem := elem.vec) (acc := newParSum.cast (by simp [elem]; apply LawfulVecOperator.le_size))
                  (l := bvRes.val.extractLsb' 0 (usedNodes / 2 * w)) (bv := bvRes.val.extractLsb' (usedNodes / 2 * w) w)
        rw [this]
        · simp
          by_cases hsplit : idx < usedNodes/2 * w
          · simp [bvRes]
            rw [BitVec.getLsbD_append]
            simp [hsplit]
          · rw [BitVec.getLsbD_append]
            simp [hsplit, show idx - usedNodes / 2 * w < w by omega]
            rw [show usedNodes / 2 * w + (idx - usedNodes / 2 * w) = idx by omega]
        · intros idx1 hidx1
          simp [elem]
          rw [AIG.LawfulVecOperator.denote_mem_prefix (f := blastAdd)]
          rw [AIG.LawfulVecOperator.denote_mem_prefix (f := blastExtract)]
          · specialize hnew idx1 hidx1
            simp [hnew]
            sorry
          · exact (newParSum.get idx1 hidx1).hgate
        · intros idx1 hidx1
          simp [elem]
          -- rw [denote_blastAdd]

          sorry
  · case _ hgen'  =>
    rw [← hgen]
    have hcast : usedNodes / 2 * w = (validNodes + 1) / 2 * w := by
      congr 1
      omega
    have : (hcast▸newParSum).get idx (by omega) = newParSum.get idx (by omega) := by
      congr 2
      · omega
      · simp_all
        exact eqRec_heq hcast newParSum
      · simp_all only [Nat.reduceDiv, BitVec.getLsbD_eq_getElem]
        rw [heq_eq_eq]
    conv =>
      lhs
      arg 2
      arg 2
      simp
      rw [this]
    simp
    specialize hnew idx (by omega)
    simp [hnew]


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
