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

theorem BitVec.getLsbD_extractAndExtend_of_le_of_lt (w idx currIdx : Nat) (hw : 0 < w) (x : BitVec w)
    (_hcurr : currIdx < w)
    (hlt : idx < w * (currIdx + 1)) (hle : w * currIdx ≤ idx) :
    (BitVec.zeroExtend w (BitVec.extractLsb' currIdx 1 x)).getLsbD (idx - w * currIdx) =
    (BitVec.extractAndExtendPopulate w x).getLsbD idx := by
  unfold BitVec.extractAndExtendPopulate
  have ⟨res, proof⟩ := BitVec.extractAndExtendPopulateAux 0 w x (BitVec.cast (by omega) 0#0) (by omega) (by omega)
  simp [Nat.mul_add] at hlt
  simp [show idx - w * currIdx < w by omega]
  by_cases h2 : idx - w * currIdx = 0
  · have hidx : idx = currIdx * w := by rw [Nat.mul_comm]; omega
    simp [h2]
    simp [hidx]
    specialize proof currIdx
    have : res.getLsbD (currIdx * w) = (BitVec.extractLsb' (currIdx * w) w res)[0] := by
      simp
    simp [this, proof]
  · have hidx : ∃ j, idx = currIdx * w + j := by
      refine Nat.exists_eq_add_of_le (by rw [Nat.mul_comm]; omega)
    obtain ⟨j, hj⟩ := hidx
    simp [h2]
    rw [hj]
    specialize proof currIdx
    have : res.getLsbD (currIdx * w + j) = (BitVec.extractLsb' (currIdx * w) w res).getLsbD j := by
      simp
      intros ht
      by_cases hlt : j < w
      · omega
      · rw [Nat.mul_comm] at hj
        omega
    rw [this]
    rw [proof]
    simp
    intros hj' hj''
    subst hj''
    simp
    rw [Nat.mul_comm] at hj
    omega

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
  (aig : AIG α) (usedNodes validNodes : Nat) (hw : 1 < w)
  (oldParSum : AIG.RefVec aig (validNodes * w)) (newParSum : AIG.RefVec aig ((usedNodes / 2) * w))
  (hval : validNodes ≤ w) (hused : usedNodes ≤ validNodes + 1) (hmod : usedNodes % 2 = 0)
  (oldParSumBv : BitVec (validNodes * w))
  (hval : 0 < validNodes)
  -- the bits added already denote to the corresponding entry in acc
  (hold : ∀ (idx : Nat) (hidx : idx < validNodes * w),
          ⟦aig, oldParSum.get idx hidx, assign⟧ = oldParSumBv.getLsbD idx)
  (hnew : ∀ (idx : Nat) (hidx : idx < (usedNodes / 2) * w),
          ⟦aig, newParSum.get idx hidx, assign⟧ =
      (BitVec.pps_layer 0 (old_layer := oldParSumBv) 0#(0 * w) (by simp; omega) (by sorry)).val.getLsbD idx) :
    ∀ (idx : Nat) (hidx : idx < (validNodes + 1) / 2 * w),
      ⟦
        (blastAddVec aig usedNodes validNodes oldParSum newParSum hval hused hmod).aig,
        (blastAddVec aig usedNodes validNodes oldParSum newParSum hval hused hmod).vec.get idx hidx,
        assign
      ⟧ =
        have hcastZero : 0 = 0 / 2 * w := by omega
      (BitVec.addVecAux 0 validNodes hw oldParSumBv (hcastZero▸0#0) (by intros; omega) (by omega) (by omega) (by omega)).val.getLsbD idx := by sorry
  -- intros idx hidx
  -- generalize hgen : blastAddVec aig usedNodes validNodes oldParSum newParSum hval hused hmod = res
  -- unfold blastAddVec at hgen
  -- split at hgen
  -- · case _ hgen'  =>
  --   rw [← hgen]
  --   expose_names
  --   rw [denote_blastAddVec]
  --   · -- hold
  --     intros idx hidx
  --     specialize hold idx hidx
  --     rw [AIG.LawfulVecOperator.denote_mem_prefix (f := blastAdd)]
  --     rw [AIG.LawfulVecOperator.denote_mem_prefix (f := blastExtract)]
  --     · simp [hold]
  --     · simp
  --       exact (oldParSum.get idx hidx).hgate
  --   · -- hnew
  --     intros idx hidx
  --     · simp
  --       expose_names
  --       let res := (blastAdd (blastExtract aig { w := validNodes * w, vec := oldParSum, start := usedNodes * w }).aig
  --                   { lhs := (blastExtract aig { w := validNodes * w, vec := oldParSum, start := usedNodes * w }).vec,
  --                     rhs := (if usedNodes + 1 < validNodes then (blastExtract aig
  --                                 { w := validNodes * w, vec := oldParSum, start := (usedNodes + 1) * w }).vec
  --                               else blastConst aig 0#w).cast (by apply LawfulVecOperator.le_size (f := blastExtract))})

  --       have h1 : usedNodes / 2 * w + w = (usedNodes + 2) / 2 * w := by
  --           rw [show usedNodes / 2 * w + w = usedNodes / 2 * w + 1 * w by omega]
  --           rw [← Nat.add_mul]
  --           simp

  --       let elem := (blastAdd (blastExtract aig { w := validNodes * w, vec := oldParSum, start := usedNodes * w }).aig
  --                   { lhs := (blastExtract aig { w := validNodes * w, vec := oldParSum, start := usedNodes * w }).vec,
  --                     rhs :=
  --                       (if usedNodes + 1 < validNodes then
  --                             (blastExtract aig
  --                                 { w := validNodes * w, vec := oldParSum, start := (usedNodes + 1) * w }).vec
  --                           else blastConst aig 0#w).cast (by apply LawfulVecOperator.le_size (f := blastExtract))})

  --       have : (h1▸ ((newParSum.cast (by simp [elem]; apply LawfulVecOperator.le_size)).append elem.vec)).get idx hidx =
  --                     ((newParSum.cast (by simp [elem]; apply LawfulVecOperator.le_size)).append elem.vec).get idx (by simp_all) := by
  --               congr 2
  --               · omega
  --               · apply eqRec_heq h1
  --               · exact heq_of_eqRec_eq (congrArg (LT.lt idx) (id (Eq.symm h1))) rfl
  --       have hcastZero : 0 = 0 / 2 * w := by omega
  --       rw [this]
  --       have  : 0 = 0 / 2 * w := by omega
  --       let bvRes:= (BitVec.addVecAux 0 validNodes hw oldParSumBv (hcastZero ▸ 0#0) (by intros; omega) hval (by omega) (by omega))
  --       rw [denote_append (assign := assign) (elem := elem.vec) (acc := newParSum.cast (by simp [elem]; apply LawfulVecOperator.le_size))
  --                 (l := bvRes.val.extractLsb' 0 (usedNodes / 2 * w)) (bv := bvRes.val.extractLsb' (usedNodes / 2 * w) w)]
  --       · simp
  --         by_cases hsplit : idx < usedNodes/2 * w
  --         · simp [bvRes]
  --           rw [BitVec.getLsbD_append]
  --           simp [hsplit]
  --         · rw [BitVec.getLsbD_append]
  --           simp [hsplit, show idx - usedNodes / 2 * w < w by omega]
  --           rw [show usedNodes / 2 * w + (idx - usedNodes / 2 * w) = idx by omega]
  --       · intros idx1 hidx1
  --         simp [elem]
  --         rw [AIG.LawfulVecOperator.denote_mem_prefix (f := blastAdd)]
  --         rw [AIG.LawfulVecOperator.denote_mem_prefix (f := blastExtract)]
  --         · specialize hnew idx1 hidx1
  --           simp [hnew, bvRes]
  --           omega
  --         · exact (newParSum.get idx1 hidx1).hgate
  --       · intros idx1 hidx1
  --         simp [elem]
  --         rw [denote_blastAdd (assign := assign) (w := w)
  --                 (lhs := oldParSumBv.extractLsb' (usedNodes * w) w)
  --                 (rhs := if usedNodes + 1 < validNodes then oldParSumBv.extractLsb' ((usedNodes + 1) * w) w else 0#w)
  --                 (input := ⟨(blastExtract aig { w := validNodes * w, vec := oldParSum, start := usedNodes * w }).vec,
  --                     ((if usedNodes + 1 < validNodes then
  --                     (blastExtract aig { w := validNodes * w, vec := oldParSum, start := (usedNodes + 1) * w }).vec
  --                   else blastConst aig 0#w)).cast (by apply AIG.LawfulVecOperator.le_size)⟩)]
  --         · split
  --           · case _ hsplit =>
  --             simp [hidx1]
  --             have proof := bvRes.property
  --             sorry
  --             specialize proof (usedNodes/2) (by omega) idx1 (by omega)
  --             have hlsb := BitVec.getLsbD_extractLsb'_eq_getLsbD (x := bvRes.val) (start := usedNodes/2 * w) (len := w) (i := idx1) (by omega)
  --             rw [← hlsb]
  --             simp [proof, hsplit, show usedNodes/2 * 2 = usedNodes by omega]
  --             rw [BitVec.getLsbD_eq_getElem (by omega)]
  --           · case _ hsplit =>
  --             have proof := bvRes.property
  --             simp
  --             specialize proof (usedNodes /2) (by omega) idx1 hidx1
  --             have hlsb := BitVec.getLsbD_extractLsb'_eq_getLsbD (x := bvRes.val) (start := usedNodes/2 * w) (len := w) (i := idx1) (by omega)
  --             rw [← hlsb]
  --             simp [proof, hsplit, show usedNodes/2 * 2 = usedNodes by omega]
  --         · intros idx2 hidx2
  --           simp [denote_blastExtract]
  --           split
  --           · simp [hidx2]
  --             specialize hold (usedNodes * w + idx2) (by omega)
  --             simp [hold]
  --           · simp
  --             intros
  --             simp [show validNodes * w ≤ usedNodes * w + idx2 by omega]
  --         · intros idx3 hidx3
  --           simp only
  --           split
  --           · next hsplit =>
  --             rw [AIG.LawfulVecOperator.denote_mem_prefix (f := blastExtract)]
  --             · simp
  --               simp [hidx3]
  --               simp at *
  --               simp [blastExtract]
  --               simp [blastExtract.go_get]
  --               simp [RefVec.getD]
  --               split
  --               · (expose_names; exact hold ((usedNodes + 1) * w + idx3) h)
  --               · rw [denote_mkConstCached]
  --                 simp [show validNodes * w ≤ (usedNodes + 1) * w + idx3 by omega]
  --             · simp
  --               exact
  --                 ((blastExtract aig
  --                           { w := validNodes * w, vec := oldParSum,
  --                             start := (usedNodes + 1) * w }).vec.get
  --                     idx3 hidx3).hgate
  --           · rw [AIG.LawfulVecOperator.denote_mem_prefix (f := blastExtract)]
  --             simp
  --             · rw [denote_blastConst]
  --               simp
  --             · simp
  --               exact ((blastConst aig 0#w).get idx3 hidx3).hgate
  -- · case _ hgen'  =>
  --   rw [← hgen]
  --   have hcast : usedNodes / 2 * w = (validNodes + 1) / 2 * w := by
  --     congr 1
  --     omega
  --   have : (hcast▸newParSum).get idx (by omega) = newParSum.get idx (by omega) := by
  --     congr 2
  --     · omega
  --     · simp_all
  --       exact eqRec_heq hcast newParSum
  --     · simp_all only [Nat.reduceDiv, BitVec.getLsbD_eq_getElem]
  --       rw [heq_eq_eq]
  --   conv =>
  --     lhs
  --     arg 2
  --     arg 2
  --     simp
  --     rw [this]
  --   simp
  --   specialize hnew idx (by omega)
  --   simp [hnew]

theorem denote_go
  (aig : AIG α) (validNodes : Nat)
  (parSum : AIG.RefVec aig (validNodes * w))  (hw : 1 < w)
  (hval : validNodes ≤ w) (hval' : 0 < validNodes)
  (parSumBv : BitVec (validNodes * w))
  (hpar : ∀ (idx : Nat) (hidx : idx < validNodes * w),
          ⟦aig, parSum.get idx hidx, assign⟧ = parSumBv.getLsbD idx) :
    ∀ (idx : Nat) (hidx : idx < w),
      ⟦
        (go aig validNodes parSum hw hval hval').aig,
        (go aig validNodes parSum hw hval hval').vec.get idx hidx,
        assign
      ⟧ =
      (BitVec.parPrefixSum validNodes parSumBv (by omega) hval hval').val.getLsbD idx := by sorry
  -- intros idx hidx
  -- generalize hgen : go aig validNodes parSum hw hval hval' = res
  -- unfold go at hgen
  -- split at hgen
  -- · rw [← hgen]
  --   simp
  --   have hcastZero : 0 = 0 / 2 * w := by omega
  --   let bvRes := BitVec.addVecAux 0 validNodes (by omega) parSumBv (hcastZero▸0#0)
  --                       (by intros i hi j hj; simp [show i = 0 by omega]; omega) (by omega) (by omega) (by omega)
  --   rw [denote_go (validNodes := (validNodes + 1)/2) (parSumBv := bvRes.val)]
  --   · conv =>
  --       rhs
  --       unfold BitVec.parPrefixSum
  --     simp
  --     split
  --     · simp [bvRes]
  --     · omega
  --   · intros idx hidx
  --     rw [denote_blastAddVec (oldParSumBv := parSumBv)]
  --     · intros idx hidx
  --       apply hpar
  --     · omega
  -- · rw [← hgen]
  --   simp
  --   have hval1 : validNodes = 1 := by omega
  --   have hcast : validNodes * w = w := by simp [hval1]
  --   specialize hpar idx (by simp [hval1]; omega)
  --   unfold BitVec.parPrefixSum
  --   simp [hval1]
  --   have hcasteq: (hcast ▸ parSum).get idx hidx = parSum.get idx (by omega) := by
  --     congr
  --     · simp [hval1]
  --     · exact eqRec_heq hcast parSum
  --     · exact heq_of_eqRec_eq (congrArg (LT.lt idx) (id (Eq.symm hcast))) rfl
  --   rw [hcasteq]
  --   simp [hpar]

end blastCpop


@[simp]
theorem denote_blastCpop (aig : AIG α) (xc : RefVec aig w) (x : BitVec w) (assign : α → Bool)
      (hx : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, xc.get idx hidx, assign⟧ = x.getLsbD idx)
      :
      ∀ (idx : Nat) (hidx : idx < w),
        ⟦(blastCpop aig xc).aig, (blastCpop aig xc).vec.get idx hidx, assign⟧
          = (BitVec.cpop x).getLsbD idx := by
    generalize hgen : blastCpop aig xc = res
    unfold blastCpop at hgen
    rw [BitVec.cpop_eq_pps]
    split at hgen
    · rw [← hgen]
      let initAcc := blastConst (w := 0) aig 0
      let res1 := blastExtractAndExtendPopulate aig 0 xc initAcc (by omega)
      let aig1 := res.aig
      sorry
    · sorry
  -- rw [BitVec.popCount_eq_popCountParSum]
  -- split at hgen
  -- · rw [← hgen]
  --   let initAcc := blastConst (w := 0) aig 0
  --   let res1 := blastExtractAndExtendPopulate aig 0 xc initAcc (by omega)
  --   let aig1 := res.aig
  --   have extendedBits := res.vec
  --   let initAcc := 0#0
  --   let bvRes := BitVec.extractAndExtendPopulateAux 0 x initAcc (by omega) (by intros; omega)
  --   rw [denote_go (parSumBv := bvRes.val)]
  --   · unfold BitVec.popCountParSum
  --     simp [show 1 < w by omega, bvRes, initAcc]
  --   · intros idx hidx
  --     rw [denote_blastExtractAndExtendPopulate]
  --     · simp
  --     · intros idx hidx
  --       apply hx
  -- · split at hgen
  --   · rw [← hgen]
  --     have hw1: w = 1 := by omega
  --     simp [BitVec.popCountParSum]
  --     conv =>
  --       rhs
  --       simp [hw1]
  --     apply hx
  --   · rw [← hgen]
  --     have hw0: w = 0 := by omega
  --     simp [BitVec.popCountParSum]
  --     conv =>
  --       rhs
  --       simp [hw0]
  --     omega

end bitblast
end BVExpr

end Std.Tactic.BVDecide
