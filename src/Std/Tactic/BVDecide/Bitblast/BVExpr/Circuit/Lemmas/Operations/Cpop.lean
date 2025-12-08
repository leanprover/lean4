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

variable [Hashable α] [DecidableEq α]

namespace BVExpr

namespace bitblast
namespace blastCpop


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
      by_cases hidx' : idx < w * currIdx
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

theorem denote_blastAddVec
  (aig : AIG α)
  (iter_num : Nat)
  (old_layer : AIG.RefVec aig (old_length * w))
  (new_layer : AIG.RefVec aig (iter_num * w))
  (hold' : 2 * (iter_num - 1) < old_length)
  (old_layer_bv : BitVec (old_length * w))
  (hval : 0 < l_length)
  (hw : 0 < w)
  -- the bits added already denote to the corresponding entry in acc
  (hold : ∀ (idx : Nat) (hidx : idx < old_length * w),
          ⟦aig, old_layer.get idx hidx, assign⟧ = old_layer_bv.getLsbD idx)
  (hnew : ∀ (idx : Nat) (hidx : idx < iter_num * w),
          ⟦aig, new_layer.get idx hidx, assign⟧ =
      (BitVec.pps_layer 0 (old_layer := old_layer_bv) 0#(0 * w) (by simp; omega) (by simp)).val.getLsbD idx) :
    ∀ (idx : Nat) (hidx : idx < (old_length + 1) / 2 * w),
      ⟦
        (blastAddVec aig iter_num old_layer new_layer hold').aig,
        (blastAddVec aig iter_num old_layer new_layer hold').vec.get idx hidx,
        assign
      ⟧ =
      (BitVec.pps_layer 0 old_layer_bv 0#(0 * w) (by omega) (by simp)).val.getLsbD idx := by
  intros idx hidx
  generalize hgen : blastAddVec aig iter_num old_layer new_layer hold' = res
  unfold blastAddVec at hgen
  split at hgen
  · case _ hgen' =>
    rw [← hgen]
    rw [denote_blastAddVec]
    · omega
    · omega
    · intros idx hidx
      rw [AIG.LawfulVecOperator.denote_mem_prefix]
      · rw [AIG.LawfulVecOperator.denote_mem_prefix]
        · rw [AIG.LawfulVecOperator.denote_mem_prefix]
          · rw [AIG.LawfulVecOperator.denote_mem_prefix]
            · simp [hold]
            · simp [Ref.hgate]
          · simp
            exact (old_layer.get idx hidx).hgate
        · simp
          exact (old_layer.get idx hidx).hgate
      · simp
        apply LawfulVecOperator.lt_size_of_lt_aig_size
        exact (old_layer.get idx hidx).hgate
    · intros idx2 hidx2
      simp [denote_blastAppend]
      split
      · case _ hsplit =>
        rw [AIG.LawfulVecOperator.denote_mem_prefix]
        · rw [AIG.LawfulVecOperator.denote_mem_prefix]
          · rw [AIG.LawfulVecOperator.denote_mem_prefix]
            · rw [hnew]
            · simp [Ref.hgate]
          · exact (new_layer.get idx2 (Eq.mpr_prop (Eq.refl (idx2 < iter_num * w)) hsplit)).hgate
        · exact (new_layer.get idx2 (Eq.mpr_prop (Eq.refl (idx2 < iter_num * w)) hsplit)).hgate
      · case _ hsplit1 =>
        have ⟨bvRes, bvRes_proof⟩ := BitVec.pps_layer 0 old_layer_bv 0#(0 * w) (by omega) (by omega)
        simp
        have bvRes_proof' := bvRes_proof iter_num (by omega) (by omega)
        let lhs_bv := BitVec.extractLsb' (2 * iter_num * w) w old_layer_bv
        let rhs_bv := if h : 2 * iter_num + 1 < old_length
                      then BitVec.extractLsb' ((2 * iter_num + 1) * w) w old_layer_bv else 0
        rw [denote_blastAdd (rhs := rhs_bv) (lhs := lhs_bv)]
        · -- have : ∀ k,  (BitVec.extractLsb' (iter_num * w) w bvRes).getLsbD k =
          let k := idx2 - iter_num * w
          have hksum : idx2 = iter_num * w + k := by omega
          rw [hksum]
          rw [show iter_num * w + k - iter_num * w = k by omega]
          specialize bvRes_proof (i := iter_num) (by omega) (by omega)
          have hlsbd := BitVec.getLsbD_extractLsb' (x := bvRes) (start := iter_num * w) (len := w) (i := k)
          have : k < w := by
            apply Classical.byContradiction
            intros hcontra
            simp [hksum, Nat.add_mul] at hidx2
            omega
          simp only [this, decide_true, Bool.true_and] at hlsbd
          simp only [dite_eq_ite, BitVec.ofNat_eq_ofNat, lhs_bv, rhs_bv]
          rw [← hlsbd]
          simp [bvRes_proof]
        · intros idx hidx
          simp only [BitVec.getLsbD_extractLsb', lhs_bv]
          have := BitVec.getLsbD_extractLsb' (x := old_layer_bv) (start := 2 * iter_num * w) (len := w) (i := idx)
          rw [← this]
          rw [AIG.LawfulVecOperator.denote_mem_prefix]
          · simp
            rw [denote_blastExtract]
            split
            · simp [hidx, hold]
            · case _ hh =>
              simp at hh
              simp [hh]
          · exact
            (((blastExtract aig
                          { w := old_length * w, vec := old_layer,
                            start := 2 * iter_num * w }).vec.cast
                    (blastAddVec._proof_10 aig iter_num old_layer
                      (blastAddVec._proof_9 aig iter_num old_layer))).get
                idx hidx).hgate
        · intros idx1 hidx1
          simp only [dite_eq_ite, BitVec.ofNat_eq_ofNat, rhs_bv]
          have :
            ((if 2 * iter_num + 1 < old_length then BitVec.extractLsb' ((2 * iter_num + 1) * w) w old_layer_bv else 0#w).getLsbD idx1) =
            ((decide (idx1 < w) && old_layer_bv.getLsbD ((2 * iter_num + 1) * w + idx1))) := by
            simp [hidx1]
            split
            · case _ hh =>
              simp
            · case _ hh =>
              simp at hh
              have h1 : old_length * w ≤ (2 * iter_num + 1) * w := by
                exact Nat.mul_le_mul_right w hh
              have h2 : old_length * w ≤ (2 * iter_num) * w + w := by
                simp [Nat.add_mul] at h1; omega
              have h3 : old_length * w ≤ (2 * iter_num + 1) * w + idx1 := by
                omega
              simp [h3]
          rw [this]
          have := BitVec.getLsbD_extractLsb' (x := old_layer_bv) (start := (2 * iter_num + 1) * w) (len := w) (i := idx1)
          rw [← this]
          rw [denote_blastExtract]
          split
          · simp
            rw [AIG.LawfulVecOperator.denote_mem_prefix]
            · simp [hold, hidx1]
            · (expose_names; exact (old_layer.get ((2 * iter_num + 1) * w + idx1) h).hgate)
          · case _ hh =>
            simp at hh
            simp
            have h3 : old_length * w ≤ (2 * iter_num + 1) * w + idx1 := by
              omega
            simp [h3]
  · case _ hgen' =>
    have h : iter_num = (old_length + 1) / 2 := by omega
    subst h
    rw [← hgen, hnew]


theorem pss_eq_of_eq (x y : BitVec (l_length * w)) (hxy : x = y)
  (xproof : x.addRecAux l_length 0#w = kx)
  (yproof : y.addRecAux l_length 0#w = ky)
  (xproof_length : 0 < l_length)
  (yproof_length : 0 < l_length)
  (hk : kx = ky)
  (hxy : x = y)
  (xhw : 0 < w)
  (yhw : 0 < w) :
  BitVec.pps x kx xproof xproof_length xhw ≍ BitVec.pps y ky yproof yproof_length yhw := by
  subst hk
  subst hxy
  rfl

theorem denote_go
  (aig : AIG α) (l_length : Nat)
  (l : AIG.RefVec aig (l_length * w)) (hw : 1 < w)
  (h : 0 < l_length)
  (l_bv : BitVec (l_length * w))
  (hpar : ∀ (idx : Nat) (hidx : idx < l_length * w),
          ⟦aig, l.get idx hidx, assign⟧ = l_bv.getLsbD idx) :
    ∀ (idx : Nat) (hidx : idx < w),
      ⟦
        (go aig l_length l h).aig,
        (go aig l_length l h).vec.get idx hidx,
        assign
      ⟧ =
      (BitVec.pps l_bv (l_bv.addRecAux l_length 0#w) (by rfl) (by omega) (by omega)).val.getLsbD idx := by
  intros idx hidx
  generalize hgen : go aig l_length l h = res
  unfold go at hgen
  split at hgen
  · rw [← hgen]
    simp
    have hcastZero : 0 = 0 / 2 * w := by omega
    let bvRes := BitVec.pps_layer 0 l_bv 0#(0 * w) (by omega) (by simp)
    rw [denote_go (l_length := (l_length + 1) / 2) (l_bv := bvRes.val) ]
    · conv =>
        rhs
        unfold BitVec.pps
      simp
      split
      · case _ h1 =>
        subst h1
        simp
        have proof := bvRes.property (i := 0) (by omega) (by omega)
        have hlbv : l_bv.getLsbD idx = (BitVec.extractLsb' (0 * w) w l_bv).getLsbD idx := by
          simp; omega
        unfold BitVec.pps
        simp
        have hresbv : bvRes.val.getLsbD idx = (BitVec.extractLsb' (0 * w) w bvRes.val).getLsbD idx := by
          simp; omega
        rw [hlbv, hresbv]
        congr 1
        rw [proof]
        simp
      · case _ hg =>
        have ⟨layer, layer_proof⟩ := BitVec.pps_layer 0 l_bv (0#(0 * w)) h (by omega)
        have ⟨bvRes, bvRes_proof⟩ := bvRes
        have : bvRes = layer := by
          ext k hk
          let pos := (k - k % w) / w
          let idx := k % w
          have : k = w * ((k - k % w)/w)+ k % w := by
            by_cases hmod0 : k % w = 0
            · simp [hmod0]
              rw [Nat.mul_comm, Nat.div_mul_cancel (by omega)]
            · have h_id : k = (k / w) * w + k % w := by exact Eq.symm (Nat.div_add_mod' k w)
              have h_div_mul : (k / w) * w = k - k % w := by exact Nat.div_mul_self_eq_mod_sub_self
              have h_div : k / w = (k - k % w) / w := by exact Nat.div_eq_sub_mod_div
              rw [← h_div]
              exact Eq.symm (Nat.div_add_mod k w)
          rw [show (k - k % w) / w = pos by rfl, show k % w = idx by rfl] at this
          simp [this, Nat.mul_comm w pos]
          have : (k - k % w) / w < (l_length + 1) / 2 := by
            have h_le_k : k / w * w ≤ k := by exact Nat.div_mul_le_self k w
            have h_combined : k / w * w < (l_length + 1) / 2 * w := Nat.lt_of_le_of_lt h_le_k hk
            have := Nat.sub_eq_of_eq_add (Nat.div_add_mod k w).symm
            rw [this, Nat.mul_div_cancel_left _ (by omega)]
            exact Nat.lt_of_mul_lt_mul_right h_combined
          specialize layer_proof (i := pos) (by simp [pos]; omega) (by omega)
          specialize bvRes_proof (i := pos) (by simp [pos]; omega) (by omega)
          have hlayer := BitVec.getLsbD_extractLsb' (start := pos * w) (i := idx) (x := layer) (len := w)
          have hbvRes := BitVec.getLsbD_extractLsb' (start := pos * w) (i := idx) (x := bvRes) (len := w)
          simp only [show idx < w by simp [idx]; refine Nat.mod_lt k (by omega),
            decide_true,
            Bool.true_and] at hlayer hbvRes
          rw [← BitVec.getLsbD_eq_getElem, ← hbvRes, bvRes_proof]
          rw [← BitVec.getLsbD_eq_getElem, ← hlayer, layer_proof]
        have haddrec := BitVec.rec_add_eq_rec_add_iff (a := bvRes) (b := l_bv) (b_length := l_length)
                            (hadd := by omega) (hw := by omega) (hlen := by omega) (by omega)
                            (n := (l_length + 1) / 2) (by omega)
        subst this
        simp
        congr 2
        ext ls
        simp
        simp [haddrec]
        apply pss_eq_of_eq (x := bvRes) (y := bvRes)
                    (kx := bvRes.addRecAux ((l_length + 1) / 2) 0#w) (ky := l_bv.addRecAux l_length 0#w)
        · rfl
        · exact haddrec
        · rfl
    · omega
    · intros idx hidx
      rw [denote_blastAddVec (old_layer_bv := l_bv) (l_length := l_length)]
      · omega
      · omega
      · intros idx hidx
        apply hpar
      · intros idx hidx
        simp at hidx
  · rw [← hgen]
    simp
    have hval1 : l_length = 1 := by omega
    have hcast : l_length * w = w := by simp [hval1]
    specialize hpar idx (by omega)
    unfold BitVec.pps
    simp [hval1]
    have hcasteq: (hcast ▸ l).get idx hidx = l.get idx (by omega) := by
      congr
      · simp [hval1]
      · exact eqRec_heq hcast l
      · exact heq_of_eqRec_eq (congrArg (LT.lt idx) (id (Eq.symm hcast))) rfl
    rw [hcasteq]
    simp [hpar]
end blastCpop

@[simp]
theorem denote_blastCpop' (aig : AIG α) (xc : RefVec aig w) (x : BitVec w) (assign : α → Bool)
      (hx : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, xc.get idx hidx, assign⟧ = x.getLsbD idx)
      :
      ∀ (idx : Nat) (hidx : idx < w),
        ⟦(blastCpop aig xc).aig, (blastCpop aig xc).vec.get idx hidx, assign⟧
          = (BitVec.cpop x).getLsbD idx := by
    generalize hgen : blastCpop aig xc = res
    unfold blastCpop at hgen
    rw [BitVec.cpop_eq_pps]
    split at hgen
    · intros idx hidx
      rw [← hgen]
      simp only [BitVec.ofNat_eq_ofNat, Lean.Elab.WF.paramLet, BitVec.addRecAux_succ,
        BitVec.addRecAux_zero]
      rw [blastCpop.denote_go (l_bv := BitVec.extractAndExtendPopulate w x)]
      · simp [show ¬ w = 0 by omega]
      · omega
      · intros idx hidx
        rw [blastCpop.denote_blastExtractAndExtendPopulate]
        · omega
        · exact hx
    · split at hgen
      · rw [← hgen]
        have : w = 1 := by omega
        subst this
        simp [BitVec.pps, BitVec.extractAndExtendPopulate, BitVec.extractAndExtendPopulateAux, hx]
      · simp [show w = 0 by omega]

theorem cpop_eq_cpopNatRec {x : BitVec w} :
    x.cpop = BitVec.ofNat w (BitVec.cpopNatRec x w 0) := by
  simp [BitVec.cpop]

@[simp]
theorem denote_blastCpop (aig : AIG α) (xc : RefVec aig w) (x : BitVec w) (assign : α → Bool)
      (hx : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, xc.get idx hidx, assign⟧ = x.getLsbD idx)
      :
      ∀ (idx : Nat) (hidx : idx < w),
        ⟦(blastCpop aig xc).aig, (blastCpop aig xc).vec.get idx hidx, assign⟧
          = (BitVec.ofNat w (BitVec.cpopNatRec x w 0)).getLsbD idx := by
    rw [← cpop_eq_cpopNatRec]
    apply denote_blastCpop'
    simp [hx]

end bitblast
end BVExpr

end Std.Tactic.BVDecide
