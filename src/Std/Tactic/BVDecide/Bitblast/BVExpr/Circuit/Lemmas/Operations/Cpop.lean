/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luisa Cicolini
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
  · case _ h =>
    split
    · simp [h, hx, show 0 < w by omega]
    · simp [h, show 0 < w by omega, show w ≤ start by omega]
  · case _ h =>
    simp [h]

theorem blastExtractAndExtendBit_denote_mem_prefix (aig : AIG α) (curr : Nat) (xc : RefVec aig w) (hstart : _) :
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

theorem denote_blastExtractAndExtend (assign : α → Bool)  (aig : AIG α) (currIdx w : Nat) (xc : AIG.RefVec aig w)
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
    rw [← hgen, denote_blastExtractAndExtend]
    · intros idx hidx
      simp only [RefVec.get_append]
      split
      · rw [blastExtractAndExtendBit_denote_mem_prefix (xc := xc)]
        apply hacc
        simp only [RefVec.get_cast, Ref.cast_eq]
        apply acc.hrefs (i := idx)
      · rw [denote_blastExtractAndExtendBit (x := x) (hx := hx), BitVec.getLsbD_extractAndExtend (by omega)]
        have h' := Nat.div_eq_of_lt_le (k := currIdx) (m := idx) (n := w)
                  (by rw [Nat.mul_comm]; omega) (by rw [Nat.mul_comm]; omega)
        congr
        · rw [← h', Nat.div_eq_sub_mod_div]
        · rw [← h', ← Nat.mod_eq_sub_mul_div]
    · intros i hi
      rw [blastExtractAndExtendBit_denote_mem_prefix (xc := xc)]
      apply hx
      simp [(xc.get i hi).hgate]
  · have hcurr : currIdx = w := by omega
    subst hcurr
    rw [← hgen, ← hacc idx hidx]

theorem denote_blastCpopLayer (aig : AIG α) (iter_num : Nat)
    (old_layer : AIG.RefVec aig (old_length * w))
    (new_layer : AIG.RefVec aig (iter_num * w)) (hold' : 2 * (iter_num - 1) < old_length)
    (old_layer_bv : BitVec (old_length * w)) (hw : 0 < w)
    (hold : ∀ (idx : Nat) (hidx : idx < old_length * w),
            ⟦aig, old_layer.get idx hidx, assign⟧ = old_layer_bv.getLsbD idx)
    (hnew : ∀ (idx : Nat) (hidx : idx < iter_num * w),
            ⟦aig, new_layer.get idx hidx, assign⟧ =
        (BitVec.cpopLayer (old_layer := old_layer_bv) 0#(0 * w) (by simp; omega)).getLsbD idx) :
    ∀ (idx : Nat) (hidx : idx < (old_length + 1) / 2 * w),
      ⟦
        (blastCpopLayer aig iter_num old_layer new_layer hold').aig,
        (blastCpopLayer aig iter_num old_layer new_layer hold').vec.get idx hidx,
        assign
      ⟧ = (BitVec.cpopLayer old_layer_bv 0#(0 * w) (by omega)).getLsbD idx := by
  intros idx hidx
  generalize hgen : blastCpopLayer aig iter_num old_layer new_layer hold' = res
  unfold blastCpopLayer at hgen
  split at hgen
  · rw [← hgen, denote_blastCpopLayer (hold' := by omega)]
    · omega
    · intros idx hidx
      rw [AIG.LawfulVecOperator.denote_mem_prefix (f := blastAppend),
        AIG.LawfulVecOperator.denote_mem_prefix (f := blastAdd),
        AIG.LawfulVecOperator.denote_mem_prefix (f := blastExtract),
        AIG.LawfulVecOperator.denote_mem_prefix (f := blastExtract)]
      simp only [RefVec.cast_cast, RefVec.get_cast, Ref.cast_eq, hold]
      exact (old_layer.get idx hidx).hgate
      all_goals
        simp only [RefVec.cast_cast, RefVec.get_cast, Ref.cast_eq]
        apply LawfulVecOperator.lt_size_of_lt_aig_size
        apply Ref.hgate
    · intros idx hidx
      rw [RefVec.cast_cast, denote_blastAppend]
      split
      · rw [AIG.LawfulVecOperator.denote_mem_prefix (f := blastAdd),
        AIG.LawfulVecOperator.denote_mem_prefix (f := blastExtract),
        AIG.LawfulVecOperator.denote_mem_prefix (f := blastExtract)]
        simp [RefVec.cast_cast, RefVec.get_cast, Ref.cast_eq]
        sorry
        all_goals
          simp only [RefVec.cast_cast, RefVec.get_cast, Ref.cast_eq]
          apply Ref.hgate
      · have := Nat.mul_le_mul_right (n := 1) (m := 2 * iter_num + 1) (k := w) (by omega)
        simp only [Nat.one_mul] at this
        rw [denote_blastAdd (lhs := BitVec.extractLsb' (2 * iter_num * w) w old_layer_bv)
          (rhs := BitVec.extractLsb' ((2 * iter_num + 1) * w) w old_layer_bv),
          BitVec.getLsbD_cpopLayer (old_layer := old_layer_bv) (new_layer := 0#(0 *w))
          (proof_addition := by intros; omega)]
        · case _ h =>
          simp at h
          have hidx' : idx / w = iter_num := Nat.div_eq_of_lt_le h hidx
          congr
          · rw [← Nat.div_eq_sub_mod_div, ← Nat.div_eq_of_lt_le h hidx]
          · rw [← hidx', Nat.div_eq_sub_mod_div]
          · simp only
            rw [← hidx', Nat.mod_eq_sub_div_mul]
        · intros idx hidx
          simp
          rw [AIG.LawfulVecOperator.denote_mem_prefix (f := blastExtract)]
          · rw [denote_blastExtract]
            simp
            split
            · simp [hold, hidx]
            · simp [hidx, show old_length * w ≤ 2 * iter_num * w + idx by omega]
          · apply Ref.hgate
        · intros idx hidx
          simp
          split
          · rw [AIG.LawfulVecOperator.denote_mem_prefix (f := blastExtract)]
            · simp [hold, hidx]
            · simp [Ref.hgate]
          · simp only [hidx, decide_true, Bool.true_and, Bool.false_eq]
            apply BitVec.getLsbD_of_ge old_layer_bv ((2 * iter_num + 1) * w + idx)
            omega
  · have h : iter_num = (old_length + 1) / 2 := by omega
    subst h
    rw [← hgen, hnew]

theorem denote_blastCpopTree (aig : AIG α) (l_length : Nat) (l : AIG.RefVec aig (l_length * w)) (hw : 1 ≤ w)
    (h : 0 < l_length) (l_bv : BitVec (l_length * w))
    (hpar : ∀ (idx : Nat) (hidx : idx < l_length * w), ⟦aig, l.get idx hidx, assign⟧ = l_bv.getLsbD idx) :
    ∀ (idx : Nat) (hidx : idx < w),
      ⟦
        (blastCpopTree aig l h).aig,
        (blastCpopTree aig l h).vec.get idx hidx,
        assign
      ⟧ = (BitVec.cpopTree l_bv).getLsbD idx := by
  intros idx hidx
  generalize hgen : blastCpopTree aig l h = res
  unfold blastCpopTree at hgen
  split at hgen
  · rw [← hgen, denote_blastCpopTree ]
    · conv =>
        rhs
        unfold BitVec.cpopTree
        simp [show ¬ l_length = 1 by omega, show ¬ l_length = 0 by omega]
    · omega
    · intros idx hidx
      rw [denote_blastCpopLayer (old_layer_bv := l_bv)]
      · omega
      · intros idx hidx
        apply hpar
      · intros idx hidx
        simp at hidx
  · have : l_length = 1 := by omega
    subst this
    rw [← hgen, BitVec.cpopTree]
    simp only [Lean.Elab.WF.paramLet, Nat.succ_ne_self, ↓reduceDIte, BitVec.cast_eq]
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
      · exact Nat.one_le_of_lt (by omega)
      · apply denote_blastExtractAndExtend
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
