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

theorem blastExtractAndExtendPopulate_denote_eq'
  -- blastExtractAndExtendPopulate inputs
  (aigInit aigAcc : AIG α) (start w : Nat) (xc : AIG.RefVec aigInit w) (x : BitVec w) (acc : RefVecVec aigAcc w start) (hw : start < w)
  -- casting
  (hcast : aigInit.decls.size ≤ aigAcc.decls.size)
  -- the `curr`-th node in the accumulator corresponds to the `curr`-th element in the list
  (hacc : ∀ (idx1 : Nat) (hidx1 : idx1 < start),
            ∀ (idx2 : Nat) (hidx2 : idx2 < w),
              let ⟨val, proof⟩ := BitVec.extractAndExtendPopulateAux 0 x [] (by omega) (by simp)
              ⟦aigAcc, (acc.vec.get ⟨idx1, hidx1⟩).get idx2 hidx2, assign⟧ =
              (val.get ⟨idx1, by simp [proof]; exact Nat.lt_trans hidx1 hw⟩).getLsbD idx2)
  -- the initial circuit denotes to the input
  (hx : ∀ (idx : Nat) (hidx : idx < w), ⟦aigInit, xc.get idx hidx, assign⟧ = x.getLsbD idx)
  (assign : α → Bool) :
    ∀ (idx1 : Nat) (hidx1 : idx1 < w),
      ∀ (idx2 : Nat) (hidx2 : idx2 < w),
      let eBitsVec := blastExtractAndExtendPopulate aigAcc start (xc.cast (aig1 := aigInit) (aig2 := aigAcc) hcast) acc (by omega)
      ⟦
        eBitsVec.aig,
        (eBitsVec.vec.vec.get ⟨idx1, hidx1⟩).get idx2 hidx2,
        assign
      ⟧ =
      ((BitVec.extractAndExtendPopulateAux 0 x [] (by omega) (by simp)).val.get ⟨start, by
      have := (BitVec.extractAndExtendPopulateAux 0 x [] (by omega) (by simp)).property
      omega⟩).getLsbD idx2 := by
  intros idx1 hidx1 idx2 hidx2
  generalize hext: blastExtractAndExtendPopulate aigAcc start (xc.cast (aig1 := aigInit) (aig2 := aigAcc) hcast) acc (by omega) = res
  unfold blastExtractAndExtendPopulate at hext
  split at hext
  · case isTrue h =>
    rw [← hext]
    dsimp only
    rw [blastExtractAndExtendPopulate_denote_eq']
    · sorry
    · sorry
    · sorry
    · sorry
    · sorry
    · sorry
  · case isFalse h => simp [h] at hw


theorem blastExtractAndExtendPopulate_denote_eq
  -- blastExtractAndExtendPopulate inputs
  (aig : AIG α) (start : Nat) (xc : AIG.RefVec aig w) (x : BitVec w) (acc : RefVecVec aig w start) (hw : start ≤ w)
  -- denotation
  (initVec : RefVecVec aig w 0 := {vec : Vector (AIG.RefVec aig w) 0 := Vector.emptyWithCapacity 0})
  (hx : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, xc.get idx hidx, assign⟧ = x.getLsbD idx)
  (assign : α → Bool) :
    ∀ (idx1 : Nat) (hidx1 : idx1 < w),
      ∀ (idx2 : Nat) (hidx2 : idx2 < w),
      ⟦
        (blastExtractAndExtendPopulate aig 0 xc initVec (by omega)).aig,
        ((blastExtractAndExtendPopulate aig 0 xc initVec (by omega)).vec.vec.get ⟨idx1,hidx1⟩).get idx2 hidx2,
        assign
      ⟧ =
      ((BitVec.extractAndExtendPopulateAux 0 x [] (by omega) (by simp)).val.get ⟨idx1, by
        have := (BitVec.extractAndExtendPopulateAux 0 x [] (by omega) (by simp)).property
        simp [this]
        omega
        ⟩).getLsbD idx2 := by
  intros idx1 hidx1 idx2 hidx2
  generalize hext: blastExtractAndExtendPopulate aig 0 xc initVec (by omega) = res
  unfold blastExtractAndExtendPopulate at hext
  dsimp at hext
  split at hext
  · case isTrue h =>
    rw [← hext]
    dsimp


    sorry
  · case isFalse h => omega

end blastPopCount

@[simp]
theorem denote_blastPopCount (aig : AIG α) (xc : RefVec aig w) (x : BitVec w) (assign : α → Bool)
      (hx : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, xc.get idx hidx, assign⟧ = x.getLsbD idx)
      :
      ∀ (idx : Nat) (hidx : idx < w),
        ⟦(blastPopCount aig xc).aig, (blastPopCount aig xc).vec.get idx hidx, assign⟧
          =
        (BitVec.popCountAuxRec x 0 0).getLsbD idx := by
  sorry

end bitblast
end BVExpr

end Std.Tactic.BVDecide
