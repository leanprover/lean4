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
This module contains the verification of the bitblaster for `BitVec.hAdd` from
`Impl.Operations.Cpop`. We prove that the recursive addition of `w`-long words over
a `len * w`-long bitvector is equal to the addition using a parallel prefix sum circuit of the
same bitvector.
-/

namespace Std.Tactic.BVDecide

open Std.Sat
open Std.Sat.AIG

variable [Hashable α] [DecidableEq α]

namespace BVExpr

namespace bitblast

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
  simp only [denote_blastZeroExtend, Nat.lt_one_iff, denote_blastExtract,
    BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb']
  have hidx0 : idx = 0 ∨ 0 < idx := by omega
  rcases hidx0 with hidx0 | hidx0
  · simp [hidx0, show 0 < w by omega, hx]
    intros
    exact BitVec.getLsbD_of_ge x start (by omega)
  · intros
    simp [hidx, show ¬ idx = 0 by omega]

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

theorem denote_blastExtractAndExtendPopulate
  (assign : α → Bool)
  (aig : AIG α) (currIdx w : Nat) (xc : AIG.RefVec aig w) (x : BitVec w)
  (acc : AIG.RefVec aig (w * currIdx)) (hlt : currIdx ≤ w)
  -- the bits added already denote to the corresponding entry in acc
  (hacc : ∀ (idx : Nat) (hidx : idx < w * currIdx),
              ⟦aig, acc.get idx hidx, assign⟧ =
              (BitVec.extractAndExtendPopulate w x).getLsbD idx )
  (hx : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, xc.get idx hidx, assign⟧ = x.getLsbD idx)
   :
    ∀ (idx : Nat) (hidx : idx < w * w),
      ⟦
        (blastExtractAndExtendPopulate aig currIdx xc acc hlt).aig,
        (blastExtractAndExtendPopulate aig currIdx xc acc hlt).vec.get idx hidx,
        assign
      ⟧ =
        (BitVec.extractAndExtendPopulate w x).getLsbD idx := by
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
      have hidx' : idx < w * currIdx ∨ w * currIdx ≤ idx := by omega
      rcases hidx' with hidx' | hidx'
      · rw [dite_cond_eq_true (by simp [hidx'])]
        specialize hacc idx hidx'
        rw [blastExtractAndExtend_denote_mem_prefix (xc := xc)]
        apply hacc
        simp
        exact
          (acc.get idx
              (of_eq_true
                (of_eq_true
                  (Eq.trans (congrArg (fun x => x = True) (eq_true hidx')) (eq_self True))))).hgate
      · rw [dite_cond_eq_false (by simp [hidx'])]
        rw [denote_blastExtractAndExtend (xc := xc) (x := x)]
        · simp at hidx'
          rw [BitVec.getLsbD_extractAndExtend_of_le_of_lt (hlt := hidx) (hle := hidx') (_hcurr := by omega)]
          omega
        · intros j hj
          apply hx
    · intros i hi
      simp only [res]
      rw [blastExtractAndExtend_denote_mem_prefix (xc := xc)]
      apply hx
      simp
      exact (xc.get i hi).hgate
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


theorem denote_blastCpopLayer
  (aig : AIG α)
  (iter_num : Nat)
  (old_layer : AIG.RefVec aig (old_length * w))
  (new_layer : AIG.RefVec aig (iter_num * w))
  (hold' : 2 * (iter_num - 1) < old_length)
  (old_layer_bv : BitVec (old_length * w))
  (_hval : 0 < l_length)
  (hw : 0 < w)
  -- the bits added already denote to the corresponding entry in acc
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
      ⟧ =
      (BitVec.cpopLayer old_layer_bv 0#(0 * w) (by omega)).getLsbD idx := by
  intros idx hidx
  generalize hgen : blastCpopLayer aig iter_num old_layer new_layer hold' = res
  unfold blastCpopLayer at hgen
  split at hgen
  · case _ hgen' =>
    rw [← hgen, denote_blastCpopLayer ]
    · omega
    · omega
    · intros idx hidx
      rw [AIG.LawfulVecOperator.denote_mem_prefix, AIG.LawfulVecOperator.denote_mem_prefix,
        AIG.LawfulVecOperator.denote_mem_prefix, AIG.LawfulVecOperator.denote_mem_prefix]
      · simp [hold]
      · simp [Ref.hgate]
      · simp only [RefVec.cast_cast, RefVec.get_cast, Ref.cast_eq]
        exact (old_layer.get idx hidx).hgate
      · simp only [RefVec.cast_cast, RefVec.get_cast, Ref.cast_eq]
        exact (old_layer.get idx hidx).hgate
      · simp only [RefVec.cast_cast, RefVec.get_cast, Ref.cast_eq]
        apply LawfulVecOperator.lt_size_of_lt_aig_size
        exact (old_layer.get idx hidx).hgate
    · intros idx2 hidx2
      simp only [RefVec.cast_cast, denote_blastAppend, RefVec.get_cast, Ref.cast_eq]
      split
      · case _ hsplit =>
        rw [AIG.LawfulVecOperator.denote_mem_prefix, AIG.LawfulVecOperator.denote_mem_prefix ,
          AIG.LawfulVecOperator.denote_mem_prefix]
        · rw [hnew]
        · simp [Ref.hgate]
        · exact (new_layer.get idx2 (Eq.mpr_prop (Eq.refl (idx2 < iter_num * w)) hsplit)).hgate
        · exact (new_layer.get idx2 (Eq.mpr_prop (Eq.refl (idx2 < iter_num * w)) hsplit)).hgate
      · case _ hsplit1 =>
        have bvRes_proof := BitVec.extractLsb'_cpopLayer old_layer_bv 0#(0 * w) (by omega) (by omega)
        let lhs_bv := BitVec.extractLsb' (2 * iter_num * w) w old_layer_bv
        let rhs_bv := BitVec.extractLsb' ((2 * iter_num + 1) * w) w old_layer_bv
        rw [denote_blastAdd (rhs := rhs_bv) (lhs := lhs_bv)]
        · let k := idx2 - iter_num * w
          have hksum : idx2 = iter_num * w + k := by omega
          rw [hksum, show iter_num * w + k - iter_num * w = k by omega]
          specialize bvRes_proof (i := iter_num) (by omega)
          have hlsbd := BitVec.getLsbD_extractLsb' (x := BitVec.cpopLayer old_layer_bv 0#(0 * w) (by omega))
                                                   (start := iter_num * w) (len := w) (i := k)
          have hlt : k < w := by
            simp only [Nat.add_mul] at hidx2
            omega
          simp only [hlt, decide_true, Bool.true_and] at hlsbd
          simp only [lhs_bv, rhs_bv]
          rw [← hlsbd]
          congr
          exact BitVec.eq_of_toNat_eq (congrArg BitVec.toNat (id (Eq.symm bvRes_proof)))
        · intros idx hidx
          rw [BitVec.getLsbD_extractLsb', ← BitVec.getLsbD_extractLsb', AIG.LawfulVecOperator.denote_mem_prefix]
          · simp only [RefVec.get_cast, Ref.cast_eq, BitVec.getLsbD_extractLsb']
            rw [denote_blastExtract]
            split
            · simp [hidx, hold]
            · case _ hh =>
              simp only [Nat.not_lt] at hh
              simp [hh]
          · simp only [RefVec.get_cast, Ref.cast_eq]
            exact ((blastExtract aig
                        {w := old_length * w, vec := old_layer,
                          start := 2 * iter_num * w}).vec.get
                  idx hidx).hgate
        · intros idx1 hidx1
          simp only [rhs_bv]
          have : ((BitVec.extractLsb' ((2 * iter_num + 1) * w) w old_layer_bv).getLsbD idx1) =
              ((decide (idx1 < w) && old_layer_bv.getLsbD ((2 * iter_num + 1) * w + idx1))) := by
            simp [hidx1]
          rw [this, ← BitVec.getLsbD_extractLsb', denote_blastExtract]
          split
          · rw [RefVec.get_cast, Ref.cast_eq, BitVec.getLsbD_extractLsb',
              AIG.LawfulVecOperator.denote_mem_prefix]
            · simp [hold, hidx1]
            · apply (old_layer.get ((2 * iter_num + 1) * w + idx1) _).hgate
          · case _ hh =>
            simp only [Nat.not_lt] at hh
            simp [show old_length * w ≤ (2 * iter_num + 1) * w + idx1 by omega]
  · case _ hgen' =>
    have h : iter_num = (old_length + 1) / 2 := by omega
    subst h
    rw [← hgen, hnew]


theorem denote_blastCpopTree
  (aig : AIG α) (l_length : Nat)
  (l : AIG.RefVec aig (l_length * w)) (hw : 1 ≤ w)
  (h : 0 < l_length)
  (l_bv : BitVec (l_length * w))
  (hpar : ∀ (idx : Nat) (hidx : idx < l_length * w),
          ⟦aig, l.get idx hidx, assign⟧ = l_bv.getLsbD idx) :
    ∀ (idx : Nat) (hidx : idx < w),
      ⟦
        (blastCpopTree aig l h).aig,
        (blastCpopTree aig l h).vec.get idx hidx,
        assign
      ⟧ =
      (BitVec.cpopTree l_bv (by omega) (by omega)).getLsbD idx := by
  intros idx hidx
  generalize hgen : blastCpopTree aig l h = res
  unfold blastCpopTree at hgen
  split at hgen
  · rw [← hgen, denote_blastCpopTree]
    · conv =>
        rhs
        unfold BitVec.cpopTree
        simp [show ¬ l_length = 1 by omega]
    · omega
    · intros idx hidx
      rw [denote_blastCpopLayer (old_layer_bv := l_bv) (l_length := l_length)]
      · omega
      · omega
      · intros idx hidx
        apply hpar
      · intros idx hidx
        simp at hidx
  · rw [← hgen]
    simp only [show l_length = 1 by omega, ↓reduceDIte, BitVec.getLsbD_cast, BitVec.cpopTree]
    have hcast : l_length * w = w := by simp [show l_length = 1 by omega]
    have hcasteq: (hcast ▸ l).get idx hidx = l.get idx (by omega) := by
      congr 1
      · simp [show l_length = 1 by omega]
      · exact eqRec_heq hcast l
      · exact heq_of_eqRec_eq (congrArg (LT.lt idx) (id (Eq.symm hcast))) rfl
    simp [hcasteq, hpar]

@[simp]
theorem denote_blastCpop
(aig : AIG α) (xc : AIG.RefVec aig w)
      (x : BitVec w) (assign : α → Bool)
      (hx : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, xc.get idx hidx, assign⟧ = x.getLsbD idx) :
      ∀ (idx : Nat) (hidx : idx < w),
        ⟦(blastCpop aig xc).aig, (blastCpop aig xc).vec.get idx hidx, assign⟧
          = (BitVec.cpop x).getLsbD idx := by
    generalize hgen : blastCpop aig xc = res
    rw [BitVec.cpop_eq_cpopRec]
    unfold blastCpop at hgen
    split at hgen
    · case _ h1 =>
      simp only at hgen
      rw [← hgen]
      simp
      unfold BitVec.cpopRec
      simp [show 1 < w by omega]

      let ext := blastExtractAndExtendPopulate aig 0 xc (blastConst aig 0#0) (by omega)
      let ext_bv := (BitVec.extractAndExtendPopulate w x)
      have := denote_blastCpopTree (aig := ext.aig) (l := ext.vec) (by omega) (by omega) (l_bv := ext_bv) (assign := assign)
      apply this
      simp [ext, ext_bv]
      have := denote_blastExtractAndExtendPopulate (xc := xc) (x := x) (assign := assign)
      apply this
      simp
      exact hx
    · unfold BitVec.cpopRec
      split at hgen
      · case _ hw =>
        rw [← hgen]
        simp [hw, show ¬ 1 < w by omega, hx]
      · case _ hw =>
        rw [← hgen]
        simp [hw, show ¬ 1 < w by omega]

end bitblast
end BVExpr

end Std.Tactic.BVDecide
