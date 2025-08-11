/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luisa Cicolini, Siddharth Bhat, Henrik Böving
-/

module

prelude
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Const
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Sub
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Eq
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Extract
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.ZeroExtend
public import Std.Sat.AIG.If

@[expose] public section

/-!
This module contains the implementation of a bitblaster for `BitVec.popCount`.
-/

namespace Std.Tactic.BVDecide

open Std.Sat

variable [Hashable α] [DecidableEq α]

namespace BVExpr
namespace bitblast

/-- A vector of `AIG.RefVec aig w` of size n. -/
structure RefVecVec {α : Type} [DecidableEq α] [Hashable α] [DecidableEq α] (aig : AIG α) (w : Nat) (n : Nat) where
  vec : Vector (AIG.RefVec aig w) n

/-- A vector of `AIG.RefVec aig w` (vec) pointing to the same AIG (aig)-/
structure RefVecEntryVec (α : Type) [DecidableEq α] [Hashable α] [DecidableEq α] (w : Nat) (n : Nat) where
  aig : AIG α
  vec : RefVecVec aig w n

/-- Casting `RefVecVec` -/
def RefVecVec.cast {aig1 aig2 : AIG α} (s : RefVecVec aig1 lenWords len) (h : aig1.decls.size ≤ aig2.decls.size) :
    RefVecVec aig2 lenWords len :=
  let vec' := s.vec.map fun rv => rv.cast h
  RefVecVec.mk vec'

/-- When pushing a new element `elem` to vec we need to cast all the AIGs of its elements to the new element's AIG (elem.aig)-/
def RefVecVec.push {aigOld aigNew: AIG α} {n w : Nat} (vec : RefVecVec aigOld w n) (elem : AIG.RefVec aigNew w) (haig: aigOld.decls.size ≤ aigNew.decls.size):
  RefVecVec aigNew w (n + 1) :=
  let vec' : Vector (AIG.RefVec aigNew w) n := vec.vec.map fun refVec => refVec.cast haig
  {vec := vec'.push elem}

-- structure ExtractAndExtendInput (aig : AIG α) (len : Nat) where
--   lhs : AIG.RefVec aig len
--   start : Nat

/-- We extract one bit from `x` and extend it to width `w` -/
-- def blastExtractAndExtend (aig : AIG α) (input : ExtractAndExtendInput aig w) : AIG.RefVecEntry α w :=
--   let ⟨x, start⟩ := input
--   -- extract 1 bit starting from start
--   let targetExtract : ExtractTarget aig 1 := {vec := x, start := start}
--   let res := blastExtract aig targetExtract
--   let aig := res.aig
--   let extract := res.vec
--   -- zero-extend the extracted portion to have
--   let targetExtend : AIG.ExtendTarget aig w := {vec := extract, w := 1}
--   let res := blastZeroExtend aig targetExtend
--   let aig := res.aig
--   let extend := res.vec
--   ⟨aig, extend⟩

def blastExtractAndExtend (aig : AIG α) (x : AIG.RefVec aig w) (start : Nat) : AIG.RefVecEntry α w :=
  -- extract 1 bit starting from start
  let targetExtract : ExtractTarget aig 1 := {vec := x, start := start}
  let res := blastExtract aig targetExtract
  let aig := res.aig
  let extract := res.vec
  -- zero-extend the extracted portion to have
  let targetExtend : AIG.ExtendTarget aig w := {vec := extract, w := 1}
  let res := blastZeroExtend aig targetExtend
  let aig := res.aig
  let extend := res.vec
  ⟨aig, extend⟩

theorem extractAndExtend_le_size (aig : AIG α) (x : AIG.RefVec aig w) (start : Nat) :
    aig.decls.size ≤ (blastExtractAndExtend aig x start).aig.decls.size := by
  unfold blastExtractAndExtend
  dsimp only
  apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := blastZeroExtend)
  apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := blastExtract)
  omega

theorem extractAndExtend_decl_eq (aig : AIG α) (x : AIG.RefVec aig w) (start : Nat):
    ∀ (idx : Nat) (h1) (h2),
        (blastExtractAndExtend aig x start).aig.decls[idx]'h2 = aig.decls[idx]'h1 := by
  generalize hres : blastExtractAndExtend aig x start = res
  unfold blastExtractAndExtend at hres
  dsimp only at hres
  rw [← hres]
  intros
  rw [AIG.LawfulVecOperator.decl_eq (f := blastZeroExtend)]
  rw [AIG.LawfulVecOperator.decl_eq (f := blastExtract)]
  (expose_names; exact h1)

-- Note: can't wrap start into a struct because then lean won't be able to show termination

-- /-- We recursively extract and extend all bits from `x` and use them to populate `acc`, casting the AIG accordingly -/
def blastExtractAndExtendPopulate (aig : AIG α) (start : Nat) (x : AIG.RefVec aig w) (acc : RefVecVec aig w start) (hw : start ≤ w) : RefVecEntryVec α w w :=
  if hw : start < w then
    let res := blastExtractAndExtend aig x start
    let aig := res.aig
    let bv := res.vec
    let x := x.cast (aig2 := aig) (by simp [res, aig]; apply extractAndExtend_le_size)
    let acc := acc.cast (aig2 := aig) (by simp [res, aig]; apply extractAndExtend_le_size)
    let acc := acc.push bv (by simp [res, aig])
    blastExtractAndExtendPopulate aig (start + 1) x acc (by omega)
  else
    have hs : start = w := by omega
    {aig := aig, vec := hs▸acc}

theorem extractAndExtendPopulate_le_size (aig : AIG α) (x : AIG.RefVec aig w) (acc : RefVecVec aig w start) (hw : start ≤ w) :
    aig.decls.size ≤ (blastExtractAndExtendPopulate aig start x acc hw).aig.decls.size := by
  unfold blastExtractAndExtendPopulate
  dsimp only
  split
  · refine Nat.le_trans ?_ (by apply extractAndExtendPopulate_le_size)
    apply extractAndExtend_le_size
  · simp

theorem extractAndExtendPopulate_decl_eq (aig : AIG α) (x : AIG.RefVec aig w) (acc : RefVecVec aig w start) (hw : start ≤ w) :
    ∀ (idx : Nat) (h1) (h2),
        (blastExtractAndExtendPopulate aig start x acc hw).aig.decls[idx]'h2 = aig.decls[idx]'h1 := by
  generalize hres : blastExtractAndExtendPopulate aig start x acc hw = res
  unfold blastExtractAndExtendPopulate at hres
  dsimp only at hres
  split at hres
  · rw [← hres]
    intros
    rw [extractAndExtendPopulate_decl_eq, extractAndExtend_decl_eq]
    have := extractAndExtend_le_size aig x start
    (expose_names; exact Nat.lt_of_lt_of_le h1 this)
  · simp [← hres]

/-- Given a vector of references belonging to the same AIG `oldParSum`, we create a note to add the `curr`-th couple of elements and use that to populate a new vector `newParSum` -/
def blastAddVec (aig : AIG α) (currNode inputNodes: Nat) (oldParSum : RefVecVec aig w inputNodes) (newParSum : RefVecVec aig w (currNode/2)) (heven : currNode %2 = 0) (hle : currNode ≤ inputNodes + 1) (hw : inputNodes ≤ w) (hw' : 1 < inputNodes) : RefVecEntryVec α w ((inputNodes + 1)/2) :=
    if hc1 : currNode < inputNodes then
      let nextCurr := currNode + 2
      have hcast : currNode / 2 + 1 = nextCurr/2 := by omega
      -- create add node from the nodes in `oldParSum`
      if hc2 : currNode + 1 < inputNodes then
        let res := blastAdd aig ⟨oldParSum.vec.get ⟨currNode, hc1⟩, oldParSum.vec.get ⟨currNode + 1, hc2⟩⟩
        let aig := res.aig
        let add := res.vec
        have := AIG.LawfulVecOperator.le_size (f := blastAdd) ..
        let oldParSum := oldParSum.cast (aig2 := res.aig) this
        let newParSum := newParSum.cast (aig2 := res.aig) this -- this should be redundant because when the new element is pushed casting occurs, but we'll leave it there for now
        let newVec := newParSum.push add (by omega) -- now we don't need hypotheses in the push because the aigs have been cast already :) and omega suffices
        blastAddVec aig nextCurr inputNodes oldParSum (hcast▸newVec) (by omega) (by omega) hw hw'
      else
        let zero := blastConst aig (w := w) 0
        let res := blastAdd aig ⟨oldParSum.vec.get ⟨currNode, hc1⟩, zero⟩
        let aig := res.aig
        let add := res.vec
        have := AIG.LawfulVecOperator.le_size (f := blastAdd) ..
        let oldParSum := oldParSum.cast (aig2 := res.aig) this
        let newParSum := newParSum.cast (aig2 := res.aig) this -- this should be redundant because when the new element is pushed casting occurs, but we'll leave it there for now
        let newVec := newParSum.push add (by omega) -- now we don't need hypotheses in the push because the aigs have been cast already :) and omega suffices
        blastAddVec aig (currNode := nextCurr) (inputNodes := inputNodes) (oldParSum := oldParSum) (newParSum := hcast▸newVec) (by omega) (by omega) hw hw'
    else
      have hcast : currNode / 2 = (inputNodes + 1)/2 := by
        by_cases heven' : inputNodes % 2 = 0 <;> omega
      ⟨aig, hcast▸newParSum⟩

theorem blastAddVec_le_size (aig : AIG α) (currNode inputNodes: Nat) (oldParSum : RefVecVec aig w inputNodes) (newParSum : RefVecVec aig w (currNode/2)) (heven : currNode %2 = 0) (hle : currNode ≤ inputNodes + 1) (hw : inputNodes ≤ w) (hw' : 1 < inputNodes) :
    aig.decls.size ≤ (blastAddVec aig currNode inputNodes oldParSum newParSum heven hle hw hw').aig.decls.size := by
  unfold blastAddVec
  dsimp only
  split
  · split
    <;> (refine Nat.le_trans ?_ (by apply blastAddVec_le_size); apply AIG.LawfulVecOperator.le_size)
  · simp

theorem blastAddVec_decl_eq (aig : AIG α) (currNode inputNodes: Nat) (oldParSum : RefVecVec aig w inputNodes) (newParSum : RefVecVec aig w (currNode/2)) (heven : currNode %2 = 0) (hle : currNode ≤ inputNodes + 1) (hw : inputNodes ≤ w) (hw' : 1 < inputNodes) :
    ∀ (idx : Nat) (h1) (h2),
        (blastAddVec aig currNode inputNodes oldParSum newParSum heven hle hw hw').aig.decls[idx]'h1 = aig.decls[idx]'h2 := by
  generalize hres : blastAddVec aig currNode inputNodes oldParSum newParSum heven hle hw hw' = res
  unfold blastAddVec at hres
  dsimp only at hres
  split at hres
  · split at hres
    · rw [← hres]
      intros
      rw [blastAddVec_decl_eq]
      · apply AIG.LawfulVecOperator.decl_eq (f := blastAdd)
      · apply AIG.LawfulVecOperator.lt_size_of_lt_aig_size (f := blastAdd)
        assumption
    · rw [← hres]
      intros
      rw [blastAddVec_decl_eq]
      · apply AIG.LawfulVecOperator.decl_eq (f := blastAdd)
      · apply AIG.LawfulVecOperator.lt_size_of_lt_aig_size (f := blastAdd)
        assumption
  · simp [← hres]

def blastPopCount (aig : AIG α) (x : AIG.RefVec aig w):
    AIG.RefVecEntry α w :=
  if hw : 0 < w then
    let initVec : RefVecVec aig w 0 := {vec : Vector (AIG.RefVec aig w) 0 := Vector.emptyWithCapacity 0}
    let extendedBits : RefVecEntryVec α w w := blastExtractAndExtendPopulate aig 0 x initVec (by omega)
    let aig := extendedBits.aig
    let parSumInit := extendedBits.vec
    go aig w w parSumInit (by constructor; omega) (by omega) (by omega)
  else
    let zero := blastConst aig (w := w) 0
    ⟨aig, zero⟩
where
  go (aig : AIG α) (w inputNodes: Nat) (parSum : RefVecVec aig w inputNodes) (hw : NeZero w) (hw' : inputNodes ≤ w) (hw'' : 0 < inputNodes) : AIG.RefVecEntry α w :=
  if h : 1 < inputNodes then
    let outpuVec : Vector (AIG.RefVec aig w) 0 := Vector.emptyWithCapacity 0
    let outpuRefVec : RefVecVec aig w 0 := {vec := outpuVec}
    -- inputNodes = 2^n, 2^n-1, ...
    let res := blastAddVec aig (currNode := 0) (inputNodes := inputNodes) (oldParSum := parSum) (newParSum := outpuRefVec) (by omega) (by omega) (by omega) (by omega)
    let aig := res.aig
    let addNodesVec := res.vec
    go aig w ((inputNodes + 1)/2) addNodesVec hw (by omega) (by omega)
  else
    have : inputNodes = 1 := by omega
    ⟨aig, parSum.vec.get ⟨0, by omega⟩⟩

namespace blastPopCount

theorem go_le_size (aig : AIG α) (w inputNodes: Nat) (parSum : RefVecVec aig w inputNodes) (hw : NeZero w) (hw' : inputNodes ≤ w) (hw'' : 0 < inputNodes) :
    aig.decls.size ≤ (go aig w inputNodes parSum hw hw' hw'').aig.decls.size := by
  unfold go
  dsimp only
  split
  · refine Nat.le_trans ?_ (by apply go_le_size)
    apply blastAddVec_le_size
  · simp

theorem go_le_size' (w : Nat) (aig : AIG α) (input : aig.RefVec w) (h : 0 < w) :
  aig.decls.size ≤
  (go (blastExtractAndExtendPopulate aig 0 input { vec := Vector.emptyWithCapacity 0 } (by omega)).aig w w
          (blastExtractAndExtendPopulate aig 0 input { vec := Vector.emptyWithCapacity 0 } (by omega)).vec (by constructor; omega) (by omega) h).aig.decls.size:= by
  unfold go
  dsimp only
  split
  · refine Nat.le_trans ?_ (by apply go_le_size)
    refine Nat.le_trans ?_ (by apply blastAddVec_le_size)
    apply extractAndExtendPopulate_le_size
  · apply extractAndExtendPopulate_le_size

theorem go_decl_eq (w inputNodes: Nat) (aig : AIG α) (parSum : RefVecVec aig w inputNodes) (hw : NeZero w) (hw' : inputNodes ≤ w) (hw'' : 0 < inputNodes)
  : ∀ (idx : Nat) h1 h2,
    (go aig w inputNodes parSum hw hw' hw'').aig.decls[idx]'h1 =
    aig.decls[idx]'h2 := by
  generalize hgo : go aig w inputNodes parSum hw hw' hw'' = res
  unfold go at hgo
  dsimp only at hgo
  split at hgo
  · rw [← hgo]
    intros
    rw [go_decl_eq]
    · have := blastAddVec_decl_eq aig 0 inputNodes parSum
      (expose_names;
        refine
          this { vec := Vector.emptyWithCapacity 0 } (_proof_2 w inputNodes)
            (_proof_4 w inputNodes h) hw' h idx ?_ h2)
    · have := blastAddVec_le_size aig 0 inputNodes parSum
      (expose_names;
        exact
          Nat.lt_of_lt_of_le h2
            (this { vec := Vector.emptyWithCapacity 0 } (_proof_2 w inputNodes)
              (_proof_4 w inputNodes h) hw' h))
  · simp [← hgo]

theorem go_decl_eq' (w : Nat) (aig : AIG α) (input : aig.RefVec w) (hw : 0 < w)
  : ∀ (idx : Nat) h1 h2,
    (go (blastExtractAndExtendPopulate aig 0 input { vec := Vector.emptyWithCapacity 0 } (by omega)).aig w w
          (blastExtractAndExtendPopulate aig 0 input { vec := Vector.emptyWithCapacity 0 } (by omega)).vec (by constructor; omega) (by omega)
          hw).aig.decls[idx]'(by
            sorry) =
    aig.decls[idx]'h2 := by sorry

theorem go_decl_eq'' (w : Nat) (aig : AIG α) (input : aig.RefVec w) (hw : 0 < w)
  : ∀ (idx : Nat) h1 h2,
    (go (blastExtractAndExtendPopulate aig 0 input { vec := Vector.emptyWithCapacity 0 } (by omega)).aig w w
          (blastExtractAndExtendPopulate aig 0 input { vec := Vector.emptyWithCapacity 0 } (by omega)).vec (by constructor; omega) (by omega)
          hw).aig.decls[idx]'(by
            have := go_decl_eq w 0 aig
            have := extractAndExtendPopulate_decl_eq aig input (start := 0)

            sorry) =
    aig.decls[idx]'h2 := by sorry
  -- generalize hgo : go aig w inputNodes parSum hw hw' hw'' = res
  -- unfold go at hgo
  -- dsimp only at hgo
  -- split at hgo
  -- · sorry
  -- · sorry


instance : AIG.LawfulVecOperator α AIG.RefVec blastPopCount where
  le_size := by
    intros
    unfold blastPopCount
    split
    · apply go_le_size'
    · simp
  decl_eq := by
    intros
    unfold blastPopCount
    dsimp only
    expose_names
    split
    · apply go_decl_eq'
    · simp

end blastPopCount

end bitblast
end BVExpr

end Std.Tactic.BVDecide
