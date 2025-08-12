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

theorem push_denote_eq {aigOld aigNew : AIG α} {n w : Nat}
  (acc : RefVecVec aigOld w n) (elem : AIG.RefVec aigNew w)
  (haig : aigOld.decls.size ≤ aigNew.decls.size)
  (assign : α → Bool) (l : List (BitVec w)) (bv : BitVec w)
  (hlen : l.length = n)
  (hvec : ∀ (idx1 : Nat) (hidx1 : idx1 < n),
    ∀ (idx2 : Nat) (hidx2 : idx2 < w),
      ⟦aigNew, ((acc.cast haig).vec.get ⟨idx1, hidx1⟩).get idx2 hidx2, assign⟧ =
      (l.get ⟨idx1, by omega⟩).getLsbD idx2)
  (helem : ∀ (idx1 : Nat) (hidx1 : idx1 < w),
    ⟦aigNew, elem.get idx1 hidx1, assign⟧ = (bv.getLsbD idx1))
  : ∀ (idx1 : Nat) (hidx1 : idx1 < n + 1),
    ∀ (idx2 : Nat) (hidx2 : idx2 < w),
      ⟦aigNew, ((acc.push elem haig).vec.get ⟨idx1, hidx1⟩).get idx2 hidx2, assign⟧ =
      ((l.concat bv).get ⟨idx1, by have := List.length_concat (as := l) (a := bv); omega⟩).getLsbD idx2 := by
  intros idx1 hidx1 idx2 hidx2
  by_cases hidxlt : idx1 < n
  · have : (acc.push elem haig).vec.get ⟨idx1, (by omega)⟩ =
      ((acc.cast haig).vec.get ⟨idx1, (by omega)⟩) := by
      unfold RefVecVec.push
      exact Vector.getElem_push_lt (x := elem) (i := idx1) (xs := (Vector.map (fun refVec => refVec.cast haig) acc.vec)) hidxlt
    simp only [this]
    have : (l.concat bv).get ⟨idx1, by simp [hlen]; omega⟩ = l.get ⟨idx1, by simp [hlen]; omega⟩ := by
      have hlen' := List.length_concat (as := l) (a := bv)
      have := List.getElem_append_left (as := l) (i := idx1) (bs := [bv]) (by simp [hlen]; omega) (h' := by simp; omega)
      simp [this]
    rw [this]
    simp [hvec]
  · have : idx1 = n := by omega
    simp only  [this] at *
    have : (acc.push elem haig).vec.get ⟨n, (by omega)⟩ = elem := by
      unfold RefVecVec.push
      exact Vector.getElem_push_last (x := elem) (n := n)
        (xs := (Vector.map (fun refVec => refVec.cast haig) acc.vec))
    simp only [this]
    have : (l.concat bv).get ⟨n, by simp [hlen]⟩ = bv := by
      have h2 := List.getElem_concat_length (l := l) (i := n) (a := bv) (by simp [hlen])
      specialize h2 (by simp [hlen])
      simp [h2]
    rw [this]
    simp [helem]

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


theorem blastExtractAndExtendPopulate_denote_eq' (w : Nat)
  (assign : α → Bool)
  (aigAcc : AIG α) (start w : Nat) (xc : AIG.RefVec aigAcc w) (x : BitVec w) (acc : RefVecVec aigAcc w start) (hw : start + 1 < w)
  (hacc : ∀ (idx1 : Nat) (hidx1 : idx1 < start),
            ∀ (idx2 : Nat) (hidx2 : idx2 < w),
              ⟦aigAcc, (acc.vec.get ⟨idx1, hidx1⟩).get idx2 hidx2, assign⟧ =
              ((BitVec.extractAndExtendPopulateAux 0 x [] (by omega) (by simp)).val.get ⟨idx1, by simp [(BitVec.extractAndExtendPopulateAux 0 x [] (by omega) (by simp)).property]; exact Nat.lt_trans hidx1 (by omega)⟩).getLsbD idx2)
  (hx : ∀ (idx : Nat) (hidx : idx < w), ⟦aigAcc, xc.get idx hidx, assign⟧ = x.getLsbD idx)
   :
    ∀ (idx1 : Nat) (hidx1 : idx1 < start + 1),
      ∀ (idx2 : Nat) (hidx2 : idx2 < w),
      ⟦
        (blastExtractAndExtend aigAcc xc start).aig,
        (((acc.cast (aig2 := (blastExtractAndExtend aigAcc xc (start)).aig) (by apply extractAndExtend_le_size)).push (blastExtractAndExtend aigAcc xc (start)).vec (by omega)).vec.get ⟨idx1, by omega⟩).get idx2 hidx2,
        assign
      ⟧ =
        let bvRes := BitVec.extractAndExtendPopulateAux 0 x [] (by omega) (by simp)
      (bvRes.val.get ⟨idx1, by simp [bvRes.property]; omega⟩).getLsbD idx2 := by
  -- Introduce a variable `ext` for `blastExtractAndExtend`
  intros idx1 hidx1 idx2 hidx2
  let elem := blastExtractAndExtend aigAcc xc start
  have := RefVecVec.push_denote_eq
    (assign := assign)
    (aigNew := (blastExtractAndExtend aigAcc xc start).aig)
    (w := w)
    (n := start)
    (aigOld := aigAcc)
    (vec := acc.cast (by sorry))
    (elem := (blastExtractAndExtend aigAcc xc start).vec)
    (haig := by sorry)
    (idx1 := idx1)
    (hidx1 := hidx1)
    (idx2 := idx2)
    (hidx2 := hidx2)


  rw [this]

  sorry
  -- -- Rewrite the goal using `ext`
  -- have h_rewrite : ∀ (idx1 : Nat) (hidx1 : idx1 < start + 1) (idx2 : Nat) (hidx2 : idx2 < w),
  --   ⟦
  --     hext.aig,
  --     (((acc.cast (aig2 := hext.aig) (by apply extractAndExtend_le_size)).push hext.vec (by omega)).vec.get ⟨idx1, by omega⟩).get idx2 hidx2,
  --     assign
  --   ⟧ =
  --     let bvRes := BitVec.extractAndExtendPopulateAux 0 x [] (by omega) (by simp)
  --   (bvRes.val.get ⟨idx1, by simp [bvRes.property]; omega⟩).getLsbD idx2 := by
  --   -- Now you can continue the proof with the new goal
  --   intros idx1 hidx1 idx2 hidx2
  --   -- The body of your proof goes here
  --   unfold blastExtractAndExtend at hext


  --   sorry
  -- -- Apply the rewritten goal to the original goal
  -- exact h_rewrite


/-- We first prove the base case of the recursion: after all the iterations, the function
--   returns a Vector containing all the extended bits. -/
-- theorem blastExtractAndExtendPopulate_denote_base
--   -- blastExtractAndExtendPopulate inputs
--   (aig : AIG α) (w : Nat) (xc : AIG.RefVec aig w) (x : BitVec w) (acc : RefVecVec aig w w) (hw : 0 < w)
--   -- the accumulator denotes to the complete list of extended bits
--   (hacc : ∀ (idx1 : Nat) (hidx1 : idx1 < w),
--             ∀ (idx2 : Nat) (hidx2 : idx2 < w),
--               ⟦aig, (acc.vec.get ⟨idx1, hidx1⟩).get idx2 hidx2, assign⟧ =
--               ((BitVec.extractAndExtendPopulateAux 0 x [] (by omega) (by simp)).val.get ⟨idx1,
--                 by simp [(BitVec.extractAndExtendPopulateAux 0 x [] (by omega) (by simp)).property]; exact hidx1⟩).getLsbD idx2)
--   -- the initial circuit denotes to the input
--   (hx : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, xc.get idx hidx, assign⟧ = x.getLsbD idx)
--   (assign : α → Bool)
--    :
--     ∀ (idx1 : Nat) (hidx1 : idx1 < w),
--       ∀ (idx2 : Nat) (hidx2 : idx2 < w),
--       let initVec : RefVecVec aig w 0 := {vec : Vector (AIG.RefVec aig w) 0 := Vector.emptyWithCapacity 0}
--       ⟦
--         (blastExtractAndExtendPopulate aig 0 xc initVec (by omega)).aig,
--         ((blastExtractAndExtendPopulate aig 0 xc initVec (by omega)).vec.vec.get ⟨idx1, hidx1⟩).get idx2 hidx2,
--         assign
--       ⟧ =
--         let ⟨bvRes, bvProof⟩ := BitVec.extractAndExtendPopulateAux 0 x [] (by omega) (by simp)
--       (bvRes.get ⟨idx1, by simp [bvProof]; omega⟩).getLsbD idx2 := by
--   intro idx1 hidx1 idx2 hidx2
--   let initVec : RefVecVec aig w 0 := {vec : Vector (AIG.RefVec aig w) 0 := Vector.emptyWithCapacity 0}
--   generalize hext : blastExtractAndExtendPopulate aig 0 xc initVec (by omega) = res
--   unfold blastExtractAndExtendPopulate at hext
--   split at hext
--   · case isTrue h =>
--     dsimp

--     have := blastExtractAndExtendPopulate_denote_base (assign := assign)

--     sorry

--   · omega

-- theorem blastExtractAndExtendPopulate_denote_eq' (w : Nat)
--   -- blastExtractAndExtendPopulate inputs
--   (assign : α → Bool)
--   (aigAcc : AIG α) (start w : Nat) (xc : AIG.RefVec aigAcc w) (x : BitVec w) (acc : RefVecVec aigAcc w start) (hw : start + 1 < w)
--   -- the `curr`-th node in the accumulator corresponds to the `curr`-th element in the list
--   (hacc : ∀ (idx1 : Nat) (hidx1 : idx1 < start),
--             ∀ (idx2 : Nat) (hidx2 : idx2 < w),
--               ⟦aigAcc, (acc.vec.get ⟨idx1, hidx1⟩).get idx2 hidx2, assign⟧ =
--               ((BitVec.extractAndExtendPopulateAux 0 x [] (by omega) (by simp)).val.get ⟨idx1, by simp [(BitVec.extractAndExtendPopulateAux 0 x [] (by omega) (by simp)).property]; exact Nat.lt_trans hidx1 (by omega)⟩).getLsbD idx2)
--   -- the initial circuit denotes to the input
--   (hx : ∀ (idx : Nat) (hidx : idx < w), ⟦aigAcc, xc.get idx hidx, assign⟧ = x.getLsbD idx)
--    :
--     ∀ (idx1 : Nat) (hidx1 : idx1 < start + 1),
--       ∀ (idx2 : Nat) (hidx2 : idx2 < w),
--       -- let extAigBit  := blastExtractAndExtend aigAcc xc (start)
--       -- let newAcc := acc.cast (aig2 := extAigBit.aig) (by simp [extAigBit]; apply extractAndExtend_le_size)
--       -- let newAcc := newAcc.push extAigBit.vec (by omega)
--       -- ⟦
--       --   extAigBit.aig,
--       --   (newAcc.vec.get ⟨idx1, by omega⟩).get idx2 hidx2,
--       --   assign
--       -- ⟧ =
--       --   let bvRes := BitVec.extractAndExtendPopulateAux 0 x [] (by omega) (by simp)
--       -- (bvRes.val.get ⟨idx1, by simp [bvRes.property]; omega⟩).getLsbD idx2 := by
--       -- let extAigBit  := blastExtractAndExtend aigAcc xc (start)
--       -- let newAcc := acc.cast (aig2 := extAigBit.aig) (by simp [extAigBit]; apply extractAndExtend_le_size)
--       -- let newAcc := newAcc.push extAigBit.vec (by omega)
--       ⟦
--         (blastExtractAndExtend aigAcc xc start).aig,
--         (((acc.cast (aig2 := (blastExtractAndExtend aigAcc xc (start)).aig) (by apply extractAndExtend_le_size)).push (blastExtractAndExtend aigAcc xc (start)).vec (by omega)).vec.get ⟨idx1, by omega⟩).get idx2 hidx2,
--         assign
--       ⟧ =
--         let bvRes := BitVec.extractAndExtendPopulateAux 0 x [] (by omega) (by simp)
--       (bvRes.val.get ⟨idx1, by simp [bvRes.property]; omega⟩).getLsbD idx2 := by
--   intros idx1 hidx1 idx2 hidx2
--   unfold blastExtractAndExtend
--   dsimp

--   sorry

  -- generalize hext: blastExtractAndExtendPopulate (blastExtractAndExtend aig1 xc start).aig (start + 1) (xc.cast (by apply extractAndExtend_le_size)) (acc.push ((blastExtractAndExtend

  -- aig1 xc start).vec) (aigOld := aig1) (aigNew := (blastExtractAndExtend aig1 xc start).aig) (by apply extractAndExtend_le_size)) (by omega) = res
  -- unfold blastExtractAndExtendPopulate at hext
  -- split at hext
  -- · case isTrue h =>
  --   simp at hext
  --   rw [← hext]
  --   simp
  --   rw [blastExtractAndExtendPopulate_denote_eq' (assign := assign) (start := start) (aig1 := aig1) (xc := xc)]

  --   sorry
  -- · case isFalse h =>
  --   sorry


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
