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
    rw [← hgen]
    rw [denote_blastParPreSumLayer]
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
        let bvRes := BitVec.parPreSumLayer old_layer_bv 0#(0 * w) (by omega)
        have bvRes_proof := BitVec.extractLsb'_parPreSumLayer old_layer_bv 0#(0 * w) (by omega) (by omega)
        have bvRes_proof' := bvRes_proof (by omega)
        let lhs_bv := BitVec.extractLsb' (2 * iter_num * w) w old_layer_bv
        let rhs_bv := BitVec.extractLsb' ((2 * iter_num + 1) * w) w old_layer_bv
        rw [denote_blastAdd (rhs := rhs_bv) (lhs := lhs_bv)]
        · -- have : ∀ k,  (BitVec.extractLsb' (iter_num * w) w bvRes).getLsbD k =
          let k := idx2 - iter_num * w
          have hksum : idx2 = iter_num * w + k := by omega
          rw [hksum]
          rw [show iter_num * w + k - iter_num * w = k by omega]
          specialize bvRes_proof (i := iter_num) (by omega)
          have hlsbd := BitVec.getLsbD_extractLsb' (x := bvRes) (start := iter_num * w) (len := w) (i := k)
          have : k < w := by
            apply Classical.byContradiction
            intros hcontra
            simp [hksum, Nat.add_mul] at hidx2
            omega
          simp only [this, decide_true, Bool.true_and] at hlsbd
          simp only [lhs_bv, rhs_bv]
          rw [← hlsbd]
          exact
            Bool.not_inj_iff.mp
              (congrArg not (congrFun (congrArg BitVec.getLsbD (id (Eq.symm bvRes_proof))) k))
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
                    (blastParPreSumLayer._proof_10 aig iter_num old_layer
                      (blastParPreSumLayer._proof_9 aig iter_num old_layer))).get
                idx hidx).hgate
        · intros idx1 hidx1
          simp only [rhs_bv]
          have :
            ((BitVec.extractLsb' ((2 * iter_num + 1) * w) w old_layer_bv).getLsbD idx1) =
            ((decide (idx1 < w) && old_layer_bv.getLsbD ((2 * iter_num + 1) * w + idx1))) := by
            simp [hidx1]
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
  · rw [← hgen]
    simp
    have hcastZero : 0 = 0 / 2 * w := by omega
    let bvRes := BitVec.parPreSumLayer l_bv 0#(0 * w) (by omega)
    rw [denote_blastParPreSumTree (l_length := (l_length + 1) / 2) (l_bv := bvRes)]
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
    simp
    have hval1 : l_length = 1 := by omega
    have hcast : l_length * w = w := by simp [hval1]
    specialize hpar idx (by omega)
    unfold BitVec.parPreSumTree
    simp [hval1]
    have hcasteq: (hcast ▸ l).get idx hidx = l.get idx (by omega) := by
      congr
      · simp [hval1]
      · exact eqRec_heq hcast l
      · exact heq_of_eqRec_eq (congrArg (LT.lt idx) (id (Eq.symm hcast))) rfl
    rw [hcasteq]
    simp [hpar]

@[simp]
theorem denote_blastParPreSum (aig : AIG α) (l : Nat) (xc : ParPreSumTarget aig l)
      (x : BitVec (xc.w)) (assign : α → Bool)
      (hx : ∀ (idx : Nat) (hidx : idx < xc.w), ⟦aig, xc.inner.get idx hidx, assign⟧ = x.getLsbD idx)
      :
      ∀ (idx : Nat) (hidx : idx < l),
        ⟦(blastParPreSum aig xc).aig, (blastParPreSum aig xc).vec.get idx hidx, assign⟧
          = (BitVec.parPreSum l x).getLsbD idx := by
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
        unfold BitVec.parPreSum
        simp only [denote_blastZeroExtend, hx, dite_eq_ite, Bool.if_false_right,
          show ¬l = 0 by omega, reduceDIte, show xc.w ≤ l by omega, BitVec.truncate_eq_setWidth]
        intros j hj
        by_cases hlt : j < xc.w
        · simp [hlt]
          omega
        · simp [hlt, show xc.w ≤ j by omega]
      · split at hgen
        · rw [← hgen]
          unfold BitVec.parPreSum
          simp [show ¬ l = 0 by omega, show xc.w ≤ l by omega]
          intros j hj
          simp [hj]
          rw [← hx]
          · congr 1
          · omega
        · split at hgen
          · rw [← hgen]
            unfold BitVec.parPreSum
            simp only [show ¬l = 0 by omega, ↓reduceDIte, show ¬xc.w ≤ l by omega,
              show 0 < xc.w % l by omega,
              BitVec.getLsbD_cast]
            have hzero : (xc.w - xc.w % l) % l = 0 := by
              apply Nat.sub_mod_eq_zero_of_mod_eq
              simp
            let diff := (l - (xc.w % l))
            have hmodlt' := Nat.mod_lt (y := l) (x := xc.w) (by omega)
            have hmodeq : (xc.w + diff) % l = 0 := by
              simp only [diff]
              rw [← Nat.add_sub_assoc (by omega), Nat.add_comm,
                show l + xc.w - xc.w % l = l + (xc.w - xc.w % l) by omega]
              simp [hzero]
            let zext := x.zeroExtend (xc.w + diff)
            let init_length := (xc.w + diff) / l
            generalize hzext : zext.cast (m := init_length * l)
                                  (by simp [init_length]; rw [Nat.div_mul_cancel (by omega)]) = zext'
            apply denote_blastParPreSumTree
            · omega
            · rw [← hzext]
              simp [zext]
              let zeroExtendTarget : ExtendTarget aig (xc.w + diff) := {w := xc.w, vec := xc.inner}
              have := denote_blastZeroExtend (target := zeroExtendTarget) (assign := assign)
              have hcast' : xc.w + (l - xc.w % l) = (xc.w + (l - xc.w % l)) / l * l := by
                rw [Nat.div_mul_cancel (n := l)]
                simp [diff] at hmodeq
                omega
              let zextb := blastZeroExtend aig zeroExtendTarget
              let xccast := Vector.cast hcast' zextb.vec.refs
              intros j hj

              let zext0 := (blastZeroExtend aig zeroExtendTarget)
              let zext1 : zext0.aig.RefVec ((xc.w + (l - xc.w % l)) / l * l) :=
                        {refs := Vector.cast hcast' zext0.vec.refs, hrefs := by simp [zext0]
                                                                                intros k hk
                                                                                have := zext0.vec.hrefs (i := k)
                                                                                simp [diff, zext0] at this
                                                                                apply this}
              have heq : zext1.get j hj =
                     zext0.vec.get j (by simp [diff]; omega) := by
                simp [zext0, zext1, zeroExtendTarget]
                congr 2
                · simp [diff]
                  rw [Nat.div_mul_cancel (by simp [diff] at hmodeq; omega)]
                · simp [diff]
                  rw [Nat.div_mul_cancel (by simp [diff] at hmodeq; omega)]
                · congr
                  · simp [diff]
                    rw [Nat.div_mul_cancel (by simp [diff] at hmodeq; omega)]
                  · exact
                    heq_of_eqRec_eq (congrArg (Eq (xc.w + (l - xc.w % l))) (id (Eq.symm hcast')))
                      rfl
                · apply proof_irrel_heq
                · apply heq_of_eqRec_eq (congrArg (LT.lt j) (id (Eq.symm hcast'))) rfl
              have := denote_blastZeroExtend (target := zeroExtendTarget) (assign := assign) (idx := j)
                                              (hidx := by simp [diff]; omega)
              rw [heq]
              simp [zext0, zeroExtendTarget]
              split
              · simp only [hx]
                rw [BitVec.getLsbD_setWidth]
                simp [hj]
              · rw [BitVec.getLsbD_setWidth]
                simp [show xc.w ≤ j by omega]
          · rw [← hgen]
            unfold BitVec.parPreSum
            simp [show ¬l = 0 by omega, show ¬ xc.w ≤ l by omega, show ¬ 0 < xc.w % l by omega]
            have hcast : xc.w = xc.w / l * l := by rw [Nat.div_mul_cancel]; omega
            have hcast' : xc.w = xc.w / l * l := by rw [Nat.div_mul_cancel]; omega
            generalize hxcast : BitVec.cast hcast x = xcast
            let xccast : AIG.RefVec aig (xc.w / l * l) :=
                  {refs := Vector.cast hcast' xc.inner.refs,
                    hrefs := by simp [xc.inner.hrefs]}
            apply denote_blastParPreSumTree
            · omega
            · intros idx hidx
              have : xcast.getLsbD idx = x.getLsbD idx := by
                rw [← hxcast]
                simp
              rw [this, ← hx]
              · congr 2
              · omega;

@[simp]
theorem denote_blastParPreSum' (aig : AIG α) (l : Nat) (xc : ParPreSumTarget aig l)
        (x : BitVec xc.w) (assign : α → Bool)
      (hx : ∀ (idx : Nat) (hidx : idx < xc.w), ⟦aig, xc.inner.get idx hidx, assign⟧ = x.getLsbD idx)
      :
      ∀ (idx : Nat) (hidx : idx < l),
        ⟦(blastParPreSum aig xc).aig, (blastParPreSum aig xc).vec.get idx hidx, assign⟧
          = (BitVec.addRec l x).getLsbD idx := by
  rw [BitVec.addRec_eq_parPreSum]
  apply denote_blastParPreSum
  simp [hx]

end bitblast
end BVExpr

end Std.Tactic.BVDecide
