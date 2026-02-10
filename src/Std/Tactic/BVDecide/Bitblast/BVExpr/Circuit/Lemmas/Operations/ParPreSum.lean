/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luisa Cicolini, Siddharth Bhat, Henrik Böving
-/
module

prelude
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Basic
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.ParPreSum
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
`Impl.Operations.parPreSum`. We prove that the recursive addition of `w`-long words over
a `len * w`-long bitvector is equal to the addition using a parallel prefix sum circuit of the
same bitvector.
-/

namespace Std.Tactic.BVDecide

open Std.Sat
open Std.Sat.AIG

variable [Hashable α] [DecidableEq α]

namespace BVExpr

namespace bitblast


theorem denote_blastParPreSumLayer
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
      (BitVec.parPreSumLayer (old_layer := old_layer_bv) 0#(0 * w) (by simp; omega)).getLsbD idx) :
    ∀ (idx : Nat) (hidx : idx < (old_length + 1) / 2 * w),
      ⟦
        (blastParPreSumLayer aig iter_num old_layer new_layer hold').aig,
        (blastParPreSumLayer aig iter_num old_layer new_layer hold').vec.get idx hidx,
        assign
      ⟧ =
      (BitVec.parPreSumLayer old_layer_bv 0#(0 * w) (by omega)).getLsbD idx := by
  intros idx hidx
  generalize hgen : blastParPreSumLayer aig iter_num old_layer new_layer hold' = res
  unfold blastParPreSumLayer at hgen
  split at hgen
  · case _ hgen' =>
    rw [← hgen, denote_blastParPreSumLayer ]
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
        have bvRes_proof := BitVec.extractLsb'_parPreSumLayer old_layer_bv 0#(0 * w) (by omega) (by omega)
        let lhs_bv := BitVec.extractLsb' (2 * iter_num * w) w old_layer_bv
        let rhs_bv := BitVec.extractLsb' ((2 * iter_num + 1) * w) w old_layer_bv
        rw [denote_blastAdd (rhs := rhs_bv) (lhs := lhs_bv)]
        · let k := idx2 - iter_num * w
          have hksum : idx2 = iter_num * w + k := by omega
          rw [hksum, show iter_num * w + k - iter_num * w = k by omega]
          specialize bvRes_proof (i := iter_num) (by omega)
          have hlsbd := BitVec.getLsbD_extractLsb' (x := BitVec.parPreSumLayer old_layer_bv 0#(0 * w) (by omega))
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


theorem denote_blastParPreSumTree
  (aig : AIG α) (l_length : Nat)
  (l : AIG.RefVec aig (l_length * w)) (hw : 1 ≤ w)
  (h : 0 < l_length)
  (l_bv : BitVec (l_length * w))
  (hpar : ∀ (idx : Nat) (hidx : idx < l_length * w),
          ⟦aig, l.get idx hidx, assign⟧ = l_bv.getLsbD idx) :
    ∀ (idx : Nat) (hidx : idx < w),
      ⟦
        (blastParPreSumTree aig l h).aig,
        (blastParPreSumTree aig l h).vec.get idx hidx,
        assign
      ⟧ =
      (BitVec.parPreSumTree l_bv (by omega) (by omega)).getLsbD idx := by
  intros idx hidx
  generalize hgen : blastParPreSumTree aig l h = res
  unfold blastParPreSumTree at hgen
  split at hgen
  · rw [← hgen, denote_blastParPreSumTree]
    · conv =>
        rhs
        unfold BitVec.parPreSumTree
        simp [show ¬ l_length = 1 by omega]
    · omega
    · intros idx hidx
      rw [denote_blastParPreSumLayer (old_layer_bv := l_bv) (l_length := l_length)]
      · omega
      · omega
      · intros idx hidx
        apply hpar
      · intros idx hidx
        simp at hidx
  · rw [← hgen]
    simp only [show l_length = 1 by omega, ↓reduceDIte, BitVec.getLsbD_cast, BitVec.parPreSumTree]
    have hcast : l_length * w = w := by simp [show l_length = 1 by omega]
    have hcasteq: (hcast ▸ l).get idx hidx = l.get idx (by omega) := by
      congr 1
      · simp [show l_length = 1 by omega]
      · exact eqRec_heq hcast l
      · exact heq_of_eqRec_eq (congrArg (LT.lt idx) (id (Eq.symm hcast))) rfl
    simp [hcasteq, hpar]

@[simp]
theorem denote_blastParPreSum (aig : AIG α) (l : Nat) (xc : ParPreSumTarget aig l)
      (x : BitVec (xc.w)) (assign : α → Bool)
      (hx : ∀ (idx : Nat) (hidx : idx < xc.w), ⟦aig, xc.inner.get idx hidx, assign⟧ = x.getLsbD idx)
      :
      ∀ (idx : Nat) (hidx : idx < l),
        ⟦(blastParPreSum aig xc).aig, (blastParPreSum aig xc).vec.get idx hidx, assign⟧
          = (BitVec.hAdd l x).getLsbD idx := by
    generalize hgen : blastParPreSum aig xc = res
    unfold blastParPreSum at hgen
    split at hgen
    · rw [← hgen]
      simp
      omega
    · case _ h1 =>
      simp only at hgen
      split at hgen
      · rw [← hgen]
        unfold BitVec.hAdd
        simp only [denote_blastZeroExtend, hx, show ¬l = 0 by omega, reduceDIte,
          show xc.w ≤ l by omega, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth]
        intros j hj
        have hlt : j < xc.w ∨ j ≥ xc.w := by omega
        rcases hlt with hlt | hlt
        · simp [hlt]
          omega
        · simp [hlt]
      · split at hgen
        · rw [← hgen, BitVec.hAdd_eq_parPreSum (hl := by omega) (hlt := by omega)]
          unfold BitVec.parPreSum
          simp only [show 0 < xc.w % l by omega, ↓reduceDIte, BitVec.getLsbD_cast]
          have hzero : (xc.w - xc.w % l) % l = 0 := by
            apply Nat.sub_mod_eq_zero_of_mod_eq
            rw [Nat.mod_mod]
          let diff := (l - (xc.w % l))
          have hmodlt' := Nat.mod_lt (y := l) (x := xc.w) (by omega)
          have hmodeq : (xc.w + diff) % l = 0 := by
            simp only [diff]
            rw [← Nat.add_sub_assoc (by omega), Nat.add_comm,
              show l + xc.w - xc.w % l = l + (xc.w - xc.w % l) by omega]
            simp [hzero]
          generalize hzext : x.zeroExtend (xc.w + diff) = zext
          let init_length := (xc.w + diff) / l
          have hcast : xc.w + diff = init_length * l := by
            simp [init_length]
            refine Eq.symm ((fun n d => (Nat.dvd_iff_div_mul_eq n d).mp) (xc.w + diff) l ?_)
            refine (Nat.mod_eq_sub_iff ?_ ?_).mp ?_
            <;> omega
          generalize hzcast : zext.cast (m := init_length * l) hcast = zext'
          apply denote_blastParPreSumTree
          · omega
          · rw [← hzcast]
            let zeroExtendTarget : ExtendTarget aig (xc.w + diff) := {w := xc.w, vec := xc.inner}
            have hcast' : xc.w + (l - xc.w % l) = (xc.w + (l - xc.w % l)) / l * l := by
              simp [diff] at hmodeq
              omega
            intros j hj
            let zext : (blastZeroExtend aig zeroExtendTarget).aig.RefVec ((xc.w + (l - xc.w % l)) / l * l) :=
                      {refs := Vector.cast hcast' (blastZeroExtend aig zeroExtendTarget).vec.refs,
                        hrefs := by
                                  simp only [Vector.getElem_cast]
                                  intros
                                  apply (blastZeroExtend aig zeroExtendTarget).vec.hrefs}
            have heq : zext.get j hj =  (blastZeroExtend aig zeroExtendTarget).vec.get j (by simp [diff]; omega) := by
              simp only [ zeroExtendTarget, zext]
              congr 2
              · simp only [diff] at ⊢ hmodeq
                omega
              · simp only [diff] at ⊢ hmodeq
                omega
              · congr
                · simp only [diff] at ⊢ hmodeq
                  omega
                · apply heq_of_eqRec_eq
                  · simp
                  · simp
                    omega
              · apply proof_irrel_heq
              · apply heq_of_eqRec_eq
                · simp
                · simp
                  omega
            rw [heq]
            simp only [denote_blastZeroExtend, zeroExtendTarget]
            split
            · simp only [hx, BitVec.getLsbD_cast, ← hzext, BitVec.getLsbD_setWidth,
                Bool.eq_and_self, decide_eq_true_eq]
              omega
            · rw [← hzext, BitVec.cast_setWidth, Bool.false_eq, BitVec.getLsbD_setWidth]
              simp [show xc.w ≤ j by omega]
        · rw [← hgen, BitVec.hAdd_eq_parPreSum (hl := by omega) (hlt := by omega)]
          simp only [show ¬ 0 < xc.w % l by omega, reduceDIte, BitVec.getLsbD_cast, BitVec.parPreSum]
          have hcast : xc.w = xc.w / l * l := by
            refine (Nat.div_eq_iff_eq_mul_left ?_ ?_).mp rfl
            · omega
            · refine Int.ofNat_dvd.mp ?_
              omega
          generalize hxcast : BitVec.cast hcast x = xcast
          apply denote_blastParPreSumTree
          · omega
          · intros idx hidx
            have hxcast' : xcast.getLsbD idx = x.getLsbD idx := by simp [← hxcast]
            rw [hxcast', ← hx]
            · congr 2
            · omega;

end bitblast
end BVExpr

end Std.Tactic.BVDecide
