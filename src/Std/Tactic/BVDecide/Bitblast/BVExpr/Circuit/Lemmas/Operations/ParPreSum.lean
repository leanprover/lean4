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
namespace blastParPreSum


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
      (BitVec.parPreSum_layer 0 (old_layer := old_layer_bv) 0#(0 * w) (by simp; omega)).getLsbD idx) :
    ∀ (idx : Nat) (hidx : idx < (old_length + 1) / 2 * w),
      ⟦
        (blastParPreSumLayer aig iter_num old_layer new_layer hold').aig,
        (blastParPreSumLayer aig iter_num old_layer new_layer hold').vec.get idx hidx,
        assign
      ⟧ =
      (BitVec.parPreSum_layer 0 old_layer_bv 0#(0 * w) (by omega)).getLsbD idx := by sorry
--   intros idx hidx
--   generalize hgen : blastAddVec aig iter_num old_layer new_layer hold' = res
--   unfold blastAddVec at hgen
--   split at hgen
--   · case _ hgen' =>
--     rw [← hgen]
--     rw [denote_blastAddVec]
--     · omega
--     · omega
--     · intros idx hidx
--       rw [AIG.LawfulVecOperator.denote_mem_prefix]
--       · rw [AIG.LawfulVecOperator.denote_mem_prefix]
--         · rw [AIG.LawfulVecOperator.denote_mem_prefix]
--           · rw [AIG.LawfulVecOperator.denote_mem_prefix]
--             · simp [hold]
--             · simp [Ref.hgate]
--           · simp
--             exact (old_layer.get idx hidx).hgate
--         · simp
--           exact (old_layer.get idx hidx).hgate
--       · simp
--         apply LawfulVecOperator.lt_size_of_lt_aig_size
--         exact (old_layer.get idx hidx).hgate
--     · intros idx2 hidx2
--       simp [denote_blastAppend]
--       split
--       · case _ hsplit =>
--         rw [AIG.LawfulVecOperator.denote_mem_prefix]
--         · rw [AIG.LawfulVecOperator.denote_mem_prefix]
--           · rw [AIG.LawfulVecOperator.denote_mem_prefix]
--             · rw [hnew]
--             · simp [Ref.hgate]
--           · exact (new_layer.get idx2 (Eq.mpr_prop (Eq.refl (idx2 < iter_num * w)) hsplit)).hgate
--         · exact (new_layer.get idx2 (Eq.mpr_prop (Eq.refl (idx2 < iter_num * w)) hsplit)).hgate
--       · case _ hsplit1 =>
--         let bvRes := BitVec.pps_layer_without_subtype 0 old_layer_bv 0#(0 * w) (by omega)
--         have bvRes_proof := BitVec.extractLsb'_pps_layer_prop 0 old_layer_bv 0#(0 * w) (by omega) (by simp)
--                               (ls := bvRes) (hls := by simp [bvRes])
--         have bvRes_proof' := bvRes_proof iter_num (by omega) (by omega)
--         let lhs_bv := BitVec.extractLsb' (2 * iter_num * w) w old_layer_bv
--         let rhs_bv := if h : 2 * iter_num + 1 < old_length
--                       then BitVec.extractLsb' ((2 * iter_num + 1) * w) w old_layer_bv else 0
--         rw [denote_blastAdd (rhs := rhs_bv) (lhs := lhs_bv)]
--         · -- have : ∀ k,  (BitVec.extractLsb' (iter_num * w) w bvRes).getLsbD k =
--           let k := idx2 - iter_num * w
--           have hksum : idx2 = iter_num * w + k := by omega
--           rw [hksum]
--           rw [show iter_num * w + k - iter_num * w = k by omega]
--           specialize bvRes_proof (i := iter_num) (by omega) (by omega)
--           have hlsbd := BitVec.getLsbD_extractLsb' (x := bvRes) (start := iter_num * w) (len := w) (i := k)
--           have : k < w := by
--             apply Classical.byContradiction
--             intros hcontra
--             simp [hksum, Nat.add_mul] at hidx2
--             omega
--           simp only [this, decide_true, Bool.true_and] at hlsbd
--           simp only [dite_eq_ite, BitVec.ofNat_eq_ofNat, lhs_bv, rhs_bv]
--           rw [← hlsbd]
--           simp [bvRes_proof]
--         · intros idx hidx
--           simp only [BitVec.getLsbD_extractLsb', lhs_bv]
--           have := BitVec.getLsbD_extractLsb' (x := old_layer_bv) (start := 2 * iter_num * w) (len := w) (i := idx)
--           rw [← this]
--           rw [AIG.LawfulVecOperator.denote_mem_prefix]
--           · simp
--             rw [denote_blastExtract]
--             split
--             · simp [hidx, hold]
--             · case _ hh =>
--               simp at hh
--               simp [hh]
--           · exact
--             (((blastExtract aig
--                           { w := old_length * w, vec := old_layer,
--                             start := 2 * iter_num * w }).vec.cast
--                     (blastAddVec._proof_10 aig iter_num old_layer
--                       (blastAddVec._proof_9 aig iter_num old_layer))).get
--                 idx hidx).hgate
--         · intros idx1 hidx1
--           simp only [dite_eq_ite, BitVec.ofNat_eq_ofNat, rhs_bv]
--           have :
--             ((if 2 * iter_num + 1 < old_length then BitVec.extractLsb' ((2 * iter_num + 1) * w) w old_layer_bv else 0#w).getLsbD idx1) =
--             ((decide (idx1 < w) && old_layer_bv.getLsbD ((2 * iter_num + 1) * w + idx1))) := by
--             simp [hidx1]
--             split
--             · case _ hh =>
--               simp
--             · case _ hh =>
--               simp at hh
--               have h1 : old_length * w ≤ (2 * iter_num + 1) * w := by
--                 exact Nat.mul_le_mul_right w hh
--               have h2 : old_length * w ≤ (2 * iter_num) * w + w := by
--                 simp [Nat.add_mul] at h1; omega
--               have h3 : old_length * w ≤ (2 * iter_num + 1) * w + idx1 := by
--                 omega
--               simp [h3]
--           rw [this]
--           have := BitVec.getLsbD_extractLsb' (x := old_layer_bv) (start := (2 * iter_num + 1) * w) (len := w) (i := idx1)
--           rw [← this]
--           rw [denote_blastExtract]
--           split
--           · simp
--             rw [AIG.LawfulVecOperator.denote_mem_prefix]
--             · simp [hold, hidx1]
--             · (expose_names; exact (old_layer.get ((2 * iter_num + 1) * w + idx1) h).hgate)
--           · case _ hh =>
--             simp at hh
--             simp
--             have h3 : old_length * w ≤ (2 * iter_num + 1) * w + idx1 := by
--               omega
--             simp [h3]
--   · case _ hgen' =>
--     have h : iter_num = (old_length + 1) / 2 := by omega
--     subst h
--     rw [← hgen, hnew]


-- theorem pss_eq_of_eq (x y : BitVec (l_length * w)) (hxy : x = y)
--   (xproof_length : 0 < l_length)
--   (yproof_length : 0 < l_length)
--   (hk : kx = ky)
--   (hxy : x = y)
--   (xhw : 0 < w)
--   (yhw : 0 < w) :
--   BitVec.pps_without_subtype x kx xproof_length xhw ≍ BitVec.pps_without_subtype y ky yproof_length yhw := by
--   subst hk
--   subst hxy
--   rfl

theorem denote_blastParPreSumTree
  (aig : AIG α) (l_length : Nat)
  (l : AIG.RefVec aig (l_length * w)) (hw : 1 < w)
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
      (BitVec.parPreSum_tree l_bv (by omega) (by omega)).getLsbD idx := by sorry
--   intros idx hidx
--   generalize hgen : go aig l_length l h = res
--   unfold go at hgen
--   split at hgen
--   · rw [← hgen]
--     simp
--     have hcastZero : 0 = 0 / 2 * w := by omega
--     let bvRes := BitVec.pps_layer_without_subtype 0 l_bv 0#(0 * w) (by omega)
--     rw [denote_go (l_length := (l_length + 1) / 2) (l_bv := bvRes) ]
--     · conv =>
--         rhs
--         unfold BitVec.pps_without_subtype
--       simp
--       split
--       · case _ h1 =>
--         subst h1
--         simp
--         have proof := BitVec.extractLsb'_pps_layer_prop 0 l_bv 0#(0 * w) (by omega) (ls := bvRes)
--                         (hls := by simp [bvRes])
--         have hlbv : l_bv.getLsbD idx = (BitVec.extractLsb' (0 * w) w l_bv).getLsbD idx := by
--           simp; omega
--         unfold BitVec.pps_without_subtype
--         simp
--         have hresbv : bvRes.getLsbD idx = (BitVec.extractLsb' (0 * w) w bvRes).getLsbD idx := by
--           simp; omega
--         rw [hlbv, hresbv]
--         congr 1
--         rw [proof (by omega)]
--         · simp
--         · omega
--         · omega
--       · case _ hg =>
--         let layer := BitVec.pps_layer_without_subtype 0 l_bv (0#(0 * w)) h
--         have layer_proof := BitVec.extractLsb'_pps_layer_prop 0 l_bv (0#(0 * w)) h (by omega)
--                                 (ls := layer) (hls := by simp [layer])
--         have bvRes_proof := BitVec.extractLsb'_pps_layer_prop 0 l_bv 0#(0 * w) (by omega) (ls := bvRes)
--                         (hls := by simp [bvRes])
--         have : bvRes = layer := by
--           ext k hk
--           let pos := (k - k % w) / w
--           let idx := k % w
--           have : k = w * ((k - k % w)/w)+ k % w := by
--             by_cases hmod0 : k % w = 0
--             · simp [hmod0]
--               rw [Nat.mul_comm, Nat.div_mul_cancel (by omega)]
--             · have h_id : k = (k / w) * w + k % w := by exact Eq.symm (Nat.div_add_mod' k w)
--               have h_div_mul : (k / w) * w = k - k % w := by exact Nat.div_mul_self_eq_mod_sub_self
--               have h_div : k / w = (k - k % w) / w := by exact Nat.div_eq_sub_mod_div
--               rw [← h_div]
--               exact Eq.symm (Nat.div_add_mod k w)
--           rw [show (k - k % w) / w = pos by rfl, show k % w = idx by rfl] at this
--         have haddrec := BitVec.rec_add_eq_rec_add_iff (a := bvRes) (b := l_bv) (b_length := l_length)
--                             (hadd := by omega) (hlen := by omega) (by omega)
--                             (n := (l_length + 1) / 2) (by omega)

--         rw [this]
--         congr 2
--     · omega
--     · intros idx hidx
--       rw [denote_blastAddVec (old_layer_bv := l_bv) (l_length := l_length)]
--       · omega
--       · omega
--       · intros idx hidx
--         apply hpar
--       · intros idx hidx
--         simp at hidx
--   · rw [← hgen]
--     simp
--     have hval1 : l_length = 1 := by omega
--     have hcast : l_length * w = w := by simp [hval1]
--     specialize hpar idx (by omega)
--     unfold BitVec.pps_without_subtype
--     simp [hval1]
--     have hcasteq: (hcast ▸ l).get idx hidx = l.get idx (by omega) := by
--       congr
--       · simp [hval1]
--       · exact eqRec_heq hcast l
--       · exact heq_of_eqRec_eq (congrArg (LT.lt idx) (id (Eq.symm hcast))) rfl
--     rw [hcasteq]
--     simp [hpar]
-- end blastCpop

@[simp]
theorem denote_blastParPreSum' (aig : AIG α) (l : Nat) (xc : ParPreSumTarget aig l)
      (x : BitVec w) (assign : α → Bool)
      (hx : ∀ (idx : Nat) (hidx : idx < xc.w), ⟦aig, xc.inner.get idx hidx, assign⟧ = x.getLsbD idx)
      :
      ∀ (idx : Nat) (hidx : idx < l),
        ⟦(blastParPreSum aig xc).aig, (blastParPreSum aig xc).vec.get idx hidx, assign⟧
          = (BitVec.parPreSum l x).getLsbD idx := by sorry
--     generalize hgen : blastCpop aig xc = res
--     unfold blastCpop at hgen
--     rw [BitVec.cpop_eq_pps]
--     split at hgen
--     · intros idx hidx
--       rw [← hgen]
--       simp only [BitVec.ofNat_eq_ofNat, Lean.Elab.WF.paramLet, BitVec.addRecAux_succ,
--         BitVec.addRecAux_zero]
--       rw [blastCpop.denote_go (l_bv := BitVec.extractAndExtendPopulate w x)]
--       · simp [show ¬ w = 0 by omega]
--       · omega
--       · intros idx hidx
--         rw [blastCpop.denote_blastExtractAndExtendPopulate]
--         · omega
--         · exact hx
--     · split at hgen
--       · rw [← hgen]
--         have : w = 1 := by omega
--         subst this
--         simp [BitVec.pps_without_subtype, BitVec.extractAndExtendPopulate, BitVec.extractAndExtendPopulateAux_without_subtype, hx]
--       · simp [show w = 0 by omega]

-- theorem cpop_eq_cpopNatRec {x : BitVec w} :
--     x.cpop = BitVec.ofNat w (BitVec.cpopNatRec x w 0) := by
--   simp [BitVec.cpop]

@[simp]
theorem denote_blastParPreSum (aig : AIG α) (l : Nat) (xc : ParPreSumTarget aig l)
        (x : BitVec w) (assign : α → Bool)
      (hx : ∀ (idx : Nat) (hidx : idx < xc.w), ⟦aig, xc.inner.get idx hidx, assign⟧ = x.getLsbD idx)
      :
      ∀ (idx : Nat) (hidx : idx < l),
        ⟦(blastParPreSum aig xc).aig, (blastParPreSum aig xc).vec.get idx hidx, assign⟧
          = (BitVec.flattenedAdd l x).getLsbD idx := by sorry
    -- rw [← cpop_eq_cpopNatRec]
    -- apply denote_blastCpop'
    -- simp [hx]

end blastParPreSum
end bitblast
end BVExpr

end Std.Tactic.BVDecide
