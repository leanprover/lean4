/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luisa Cicolini, Siddharth Bhat, Henrik Böving
-/
module

prelude
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Basic
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Cpop
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Const
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Sub
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Append
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Eq
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.ZeroExtend
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Extract


import Init.Data.BitVec.Bootstrap
import Init.Omega
@[expose] public section


/-!
This module contains the verification of the bitblaster for `BitVec.cpop`, implemented in
`Impl.Operations.Cpop`.
-/

namespace Std.Tactic.BVDecide

open Std.Sat
open Std.Sat.AIG

variable [Hashable α] [DecidableEq α]

namespace BVExpr

namespace bitblast

theorem denote_blastExtractAndExtendBit (aig : AIG α) (xc : AIG.RefVec aig w) (x : BitVec w) (start : Nat)
    (hx : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, xc.get idx hidx, assign⟧ = x.getLsbD idx) :
    ∀ (idx : Nat) (hidx : idx < w),
      ⟦
        (blastExtractAndExtendBit aig xc start).aig,
        (blastExtractAndExtendBit aig xc start).vec.get idx hidx,
        assign
      ⟧ = (BitVec.extractAndExtendBit start w x).getLsbD idx := by
  intros idx hidx
  generalize hext: blastExtractAndExtendBit aig xc start = res
  unfold blastExtractAndExtendBit at hext
  dsimp only [Lean.Elab.WF.paramLet] at hext
  rw [← hext]
  simp only [denote_blastZeroExtend, Nat.lt_one_iff, denote_blastExtract,
    BitVec.getLsbD_extractAndExtendBit]
  split
  · split
    · simp [hx, show idx = 0 by omega, show 0 < w by omega]
    · simp [show 0 < w by omega, show w ≤ start by omega]
  · simp [show ¬ idx = 0 by omega]

theorem blastExtractAndExtendBit_denote_mem_prefix (aig : AIG α) (curr : Nat)
    (xc : RefVec aig w) (hstart : _) :
    ⟦
      (blastExtractAndExtendBit aig xc curr).aig,
      ⟨start, inv, by apply Nat.lt_of_lt_of_le; exact hstart; apply extractAndExtendBit_le_size⟩,
      assign
    ⟧ = ⟦aig, ⟨start, inv, hstart⟩, assign⟧ := by
  apply denote.eq_of_isPrefix (entry := ⟨aig, start, inv, hstart⟩)
  apply IsPrefix.of
  · intros
    apply extractAndExtendBit_decl_eq
  · intros
    apply extractAndExtendBit_le_size

theorem denote_append (assign : α → Bool) (aig : AIG α) (currIdx w : Nat) (x : BitVec w)
    (xc : AIG.RefVec aig w) (acc : AIG.RefVec aig (w * currIdx)) (hidx : idx < w * currIdx + w)
    (hacc : ∀ (idx : Nat) (hidx : idx < w * currIdx),
                ⟦aig, acc.get idx hidx, assign⟧ = (BitVec.extractAndExtend w x).getLsbD idx)
              (hx : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, xc.get idx hidx, assign⟧ = x.getLsbD idx) :
    ⟦
      (blastExtractAndExtendBit aig xc currIdx).aig,
      ((acc.cast (by apply extractAndExtendBit_le_size)).append (blastExtractAndExtendBit aig xc currIdx).vec).get idx hidx,
      assign
    ⟧ = (BitVec.extractAndExtend w x).getLsbD idx := by
  rw [RefVec.get_append]
  split
  · rw [blastExtractAndExtendBit_denote_mem_prefix (xc := xc)]
    apply hacc
    simp only [RefVec.get_cast, Ref.cast_eq]
    apply acc.hrefs (i := idx)
  · rw [BitVec.getLsbD_extractAndExtend (by omega)]
    have h := Nat.div_eq_of_lt_le (k := currIdx) (m := idx) (n := w)
              (by rw [Nat.mul_comm]; omega)
              (by rw [Nat.add_mul, Nat.mul_comm currIdx w]; omega)
    have h' := Nat.mod_eq_sub_mul_div (k := w) (x := idx)
    rw [h] at h'
    simp only [← h', ← Nat.div_eq_sub_mod_div (m := idx) (n := w), h]
    apply denote_blastExtractAndExtendBit (hx := hx)

theorem denote_blastExtractAndExtend (assign : α → Bool) (aig : AIG α) (currIdx w : Nat) (xc : AIG.RefVec aig w)
    (x : BitVec w) (acc : AIG.RefVec aig (w * currIdx)) (hlt : currIdx ≤ w)
    (hacc : ∀ (idx : Nat) (hidx : idx < w * currIdx),
                ⟦aig, acc.get idx hidx, assign⟧ = (BitVec.extractAndExtend w x).getLsbD idx)
    (hx : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, xc.get idx hidx, assign⟧ = x.getLsbD idx) :
    ∀ (idx : Nat) (hidx : idx < w * w),
      ⟦
        (blastextractAndExtend aig currIdx xc acc hlt).aig,
        (blastextractAndExtend aig currIdx xc acc hlt).vec.get idx hidx,
        assign
      ⟧ = (BitVec.extractAndExtend w x).getLsbD idx := by
  intros idx hidx
  generalize hgen : blastextractAndExtend aig currIdx xc acc hlt = gen
  unfold blastextractAndExtend at hgen
  split at hgen
  · case _ hlt =>
    rw [← hgen]
    simp only [Lean.Elab.WF.paramLet]
    apply denote_blastExtractAndExtend
    · intros idx hidx
      apply denote_append (hx := hx) (hacc := hacc)
    · intros i hi
      rw [blastExtractAndExtendBit_denote_mem_prefix (xc := xc)]
      apply hx
      simp [(xc.get i hi).hgate]
  · have hcurr : currIdx = w := by omega
    subst hcurr
    rw [← hgen, ← hacc idx hidx]

theorem denote_blastCpopLayer (aig : AIG α) (iterNum : Nat)
    (oldLayer : AIG.RefVec aig (len * w)) (newLayer : AIG.RefVec aig (iterNum * w))
    (oldLayerBv : BitVec (len * w)) (hold' : 2 * (iterNum - 1) < len)
    (hold : ∀ (idx : Nat) (hidx : idx < len * w),
            ⟦aig, oldLayer.get idx hidx, assign⟧ = oldLayerBv.getLsbD idx)
    (hnew : ∀ (idx : Nat) (hidx : idx < iterNum * w),
            ⟦aig, newLayer.get idx hidx, assign⟧ =
        (BitVec.cpopLayer (oldLayer := oldLayerBv) 0#(0 * w) (by simp; omega)).getLsbD idx) :
    ∀ (idx : Nat) (hidx : idx < (len + 1) / 2 * w),
      ⟦
        (blastCpopLayer aig iterNum oldLayer newLayer hold').aig,
        (blastCpopLayer aig iterNum oldLayer newLayer hold').vec.get idx hidx,
        assign
      ⟧ = (BitVec.cpopLayer oldLayerBv 0#(0 * w) (by omega)).getLsbD idx := by
  intros idx hidx
  generalize hgen : blastCpopLayer aig iterNum oldLayer newLayer hold' = res
  unfold blastCpopLayer at hgen
  split at hgen
  · rw [← hgen]
    simp only
    apply denote_blastCpopLayer (hold' := by omega)
    · intros idx hidx
      rw [AIG.LawfulVecOperator.denote_mem_prefix (f := blastAppend),
        AIG.LawfulVecOperator.denote_mem_prefix (f := blastAdd),
        AIG.LawfulVecOperator.denote_mem_prefix (f := blastExtract),
        AIG.LawfulVecOperator.denote_mem_prefix (f := blastExtract)]
      simp only [RefVec.cast_cast, RefVec.get_cast, Ref.cast_eq, hold]
      · exact (oldLayer.get idx hidx).hgate
      all_goals
        simp only [RefVec.cast_cast, RefVec.get_cast, Ref.cast_eq]
        apply LawfulVecOperator.lt_size_of_lt_aig_size
        apply Ref.hgate
    · intros idx hidx
      simp only [RefVec.cast_cast, denote_blastAppend, RefVec.get_cast, Ref.cast_eq]
      split
      · rw [AIG.LawfulVecOperator.denote_mem_prefix (f := blastAdd),
          AIG.LawfulVecOperator.denote_mem_prefix (f := blastExtract),
          AIG.LawfulVecOperator.denote_mem_prefix (f := blastExtract)]
        simp only [hnew]
        · exact (newLayer.get idx (by omega)).hgate
        all_goals
          apply LawfulVecOperator.lt_size_of_lt_aig_size
          apply Ref.hgate
      · have hiter : idx / w = iterNum := Nat.div_eq_of_lt_le (by omega) hidx
        subst hiter
        rw [BitVec.getLsbD_cpopLayer (oldLayer := oldLayerBv) (proof_addition := by intros; omega),
          ← Nat.div_eq_sub_mod_div (m := idx) (n := w)]
        simp only [show idx - idx / w * w = idx % w by exact Eq.symm Nat.mod_eq_sub_div_mul]
        apply denote_blastAdd
        · intros idx' hidx'
          simp only [RefVec.get_cast, Ref.cast_eq, hidx', BitVec.getLsbD_eq_getElem,
            BitVec.getElem_extractLsb']
          rw [AIG.LawfulVecOperator.denote_mem_prefix (f := blastExtract), denote_blastExtract]
          · split
            · simp [hold]
            · case _ hnot =>
              simp only [Nat.not_lt] at hnot
              exact Eq.symm (BitVec.getLsbD_of_ge oldLayerBv (2 * (idx / w) * w + idx') hnot)
          · simp [Ref.hgate]
        · intros idx'' hidx''
          simp only [denote_blastExtract, RefVec.get_cast, Ref.cast_eq, BitVec.getLsbD_extractLsb']
          split
          · rw [AIG.LawfulVecOperator.denote_mem_prefix (f := blastExtract)]
            · simp [hold, hidx'']
            · apply Ref.hgate
          · case _ hnot =>
            simp only [hidx'', decide_true, Bool.true_and, Bool.false_eq]
            simp only [Nat.not_lt] at hnot
            apply BitVec.getLsbD_of_ge oldLayerBv (ge := hnot)
  · have h : iterNum = (len + 1) / 2 := by omega
    subst h
    rw [← hgen, hnew]

theorem blastCpopLayer_denote_mem_prefix (aig : AIG α) (iterNum : Nat)  (hstart : _)
    (hold' : 2 * (iterNum - 1) < len)
    (oldLayer : AIG.RefVec aig (len * w)) (newLayer : AIG.RefVec aig (iterNum * w)) :
    ⟦
      (blastCpopLayer aig iterNum oldLayer newLayer hold').aig,
      ⟨start, inv, by apply Nat.lt_of_lt_of_le; exact hstart; apply blastCpopLayer_le_size⟩,
      assign
    ⟧ = ⟦aig, ⟨start, inv, hstart⟩, assign⟧ := by
  apply denote.eq_of_isPrefix (entry := ⟨aig, start, inv, hstart⟩)
  apply IsPrefix.of
  · intros
    apply blastCpopLayer_decl_eq
  · intros
    apply blastCpopLayer_le_size

theorem denote_blastCpopTree (aig : AIG α) (len : Nat)
    (l : AIG.RefVec aig (len * w)) (h : 0 < len) (bv : BitVec (len * w))
    (hpar : ∀ (idx : Nat) (hidx : idx < len * w), ⟦aig, l.get idx hidx, assign⟧ = bv.getLsbD idx) :
    ∀ (idx : Nat) (hidx : idx < w),
      ⟦
        (blastCpopTree aig l h).aig,
        (blastCpopTree aig l h).vec.get idx hidx,
        assign
      ⟧ = (BitVec.cpopTree bv).getLsbD idx := by
  intros idx hidx
  generalize hgen : blastCpopTree aig l h = res
  unfold blastCpopTree at hgen
  split at hgen
  · rw [← hgen]
    unfold BitVec.cpopTree
    simp only [Nat.reduceDiv, BitVec.ofNat_eq_ofNat, Lean.Elab.WF.paramLet,
      show ¬len = 0 by omega, reduceDIte, show ¬len = 1 by omega]
    apply denote_blastCpopTree
    apply denote_blastCpopLayer
    · simp [hpar]
    · simp
  · have : len = 1 := by omega
    subst this
    rw [← hgen, BitVec.cpopTree]
    simp only [Lean.Elab.WF.paramLet, Nat.succ_ne_self, reduceDIte, BitVec.getLsbD_cast]
    rw [← hpar]
    · congr
      · simp
      · apply eqRec_heq
      · apply proof_irrel_heq
    · omega

@[simp]
theorem denote_blastCpop (aig : AIG α) (xc : AIG.RefVec aig w) (x : BitVec w) (assign : α → Bool)
    (hx : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, xc.get idx hidx, assign⟧ = x.getLsbD idx) :
    ∀ (idx : Nat) (hidx : idx < w),
      ⟦
        (blastCpop aig xc).aig,
        (blastCpop aig xc).vec.get idx hidx,
        assign
      ⟧ = (BitVec.cpop x).getLsbD idx := by
    generalize hgen : blastCpop aig xc = res
    rw [BitVec.cpop_eq_cpopRec]
    unfold blastCpop at hgen
    split at hgen
    · simp only at hgen
      rw [← hgen]
      unfold BitVec.cpopRec
      simp only [BitVec.ofNat_eq_ofNat, show 1 < w by omega, reduceDIte, BitVec.getLsbD_cast]
      apply denote_blastCpopTree
      apply denote_blastExtractAndExtend
      · simp
      · exact hx
    · unfold BitVec.cpopRec
      split at hgen
      · rw [← hgen]
        simp [show w = 1 by omega, hx]
      · rw [← hgen]
        simp [show w = 0 by omega]

end bitblast
end BVExpr

end Std.Tactic.BVDecide
