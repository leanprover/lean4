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

/-- We extract one bit from `x` and extend it to width `w` -/
def extractAndExtend (start : Nat) (aig : AIG α) (x : AIG.RefVec aig w) : AIG.RefVecEntry α w :=
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

theorem extractAndExtend_le_size (aig : AIG α) (start : Nat) (x : AIG.RefVec aig w):
    aig.decls.size ≤ (extractAndExtend start aig x).aig.decls.size := by
  unfold extractAndExtend
  dsimp only
  apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := blastZeroExtend)
  apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := blastExtract)
  omega

/-- We recursively extract and extend all bits from `x` and use them to populate `acc`, casting the AIG accordingly -/
def extractAndExtendPopulate (start : Nat) (aig : AIG α) (x : AIG.RefVec aig w) (acc : RefVecVec aig w start) (hw : start ≤ w) : RefVecEntryVec α w w :=
  if hw : start < w then
    let res := extractAndExtend start aig x
    let aig := res.aig
    let bv := res.vec
    let x := x.cast (aig2 := aig) (by simp [res, aig]; apply extractAndExtend_le_size)
    let acc := acc.cast (aig2 := aig) (by simp [res, aig]; apply extractAndExtend_le_size)
    let acc := acc.push bv (by simp [res, aig])
    extractAndExtendPopulate (start + 1) aig x acc (by omega)
  else
    have hs : start = w := by omega
    {aig := aig, vec := hs▸acc}

/-- Given a vector of references belonging to the same AIG `oldParSum`, we create a note to add the `curr`-th couple of elements and use that to populate a new vector `newParSum` -/
def addVec (aig : AIG α) (addedNodes inputNodes: Nat) (oldParSum : RefVecVec aig w inputNodes) (newParSum : RefVecVec aig w addedNodes) (hw : inputNodes ≤ w): RefVecEntryVec α w (inputNodes/2) :=
  if hc : addedNodes < inputNodes/2 then
    -- create add node from the nodes in oldParSum
    let res := blastAdd aig ⟨oldParSum.vec.get ⟨addedNodes*2, by omega⟩, oldParSum.vec.get ⟨addedNodes*2 + 1, by omega⟩⟩
    let aig := res.aig
    let add := res.vec
    have := AIG.LawfulVecOperator.le_size (f := blastAdd) ..
    let oldParSum := oldParSum.cast (aig2 := res.aig) this
    let newParSum := newParSum.cast (aig2 := res.aig) this -- this should be redundant because when the new element is pushed casting occurs, but we'll leave it there for now
    let newVec := newParSum.push add (by omega) -- now we don't need hypotheses in the push because the aigs have been cast already :) and omega suffices
    addVec aig (addedNodes + 1) inputNodes oldParSum newVec hw
  else
    have hcast : addedNodes = inputNodes/2 := by sorry
    ⟨aig, hcast▸newParSum⟩

def blastPopCount (aig : AIG α) (x : AIG.RefVec aig w) :
    AIG.RefVecEntry α w :=
  if hw : 0 < w then
    let initVec' : Vector (AIG.RefVec aig w) 0 := Vector.emptyWithCapacity 0
    let initVec : RefVecVec aig w 0 := {vec := initVec'}
    let extendedBits : RefVecEntryVec α w w := extractAndExtendPopulate 0 aig x initVec (by omega)
    let aig := extendedBits.aig
    let parSumInit := extendedBits.vec
    go aig w w parSumInit (by constructor; omega) (by omega) (by omega)
  else
    let zero := blastConst aig (w := w) 0
    ⟨aig, zero⟩
where
  go (aig : AIG α) (w inputNodes: Nat) (parSum : RefVecVec aig w inputNodes) (hw : NeZero w) (hw' : inputNodes ≤ w) (hw'' : 0 < inputNodes): AIG.RefVecEntry α w :=
  if h : 1 < inputNodes then
    let outpuVec : Vector (AIG.RefVec aig w) 0 := Vector.emptyWithCapacity 0
    let outpuRefVec : RefVecVec aig w 0 := {vec := outpuVec}
    -- inputNodes = 2^n, 2^n-1, ...
    let res := addVec aig (addedNodes := 0) (inputNodes := inputNodes) (oldParSum := parSum) (newParSum := outpuRefVec) hw'
    let aig := res.aig
    let addNodesVec := res.vec
    go aig w (inputNodes/2) addNodesVec hw (by omega) (by omega)
  else if h' : inputNodes = 1 then
    ⟨aig, parSum.vec.get ⟨0, by omega⟩⟩
    else
      have : inputNodes = 0 := by omega
      ⟨aig, parSum.vec.get ⟨0, by simp_all⟩⟩

namespace blastPopCount

end blastPopCount

-- theorem blastPopCount.go_le_size (aig : AIG α) (curr : Nat)(acc : AIG.RefVec aig w)
--     (xc : AIG.RefVec aig w) :
--     aig.decls.size ≤ (go aig xc curr acc).aig.decls.size := by
--   unfold go
--   dsimp only
--   split
--   · refine Nat.le_trans ?_ (by apply go_le_size)
--     apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := AIG.RefVec.ite)
--     apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := blastAdd)
--     simp
--   · simp

-- theorem blastPopCount.go_decl_eq (aig : AIG α) (curr : Nat)  (acc : AIG.RefVec aig w)
--     (xc : AIG.RefVec aig w) :
--     ∀ (idx : Nat) h1 h2,
--         (go aig xc curr acc).aig.decls[idx]'h1 = aig.decls[idx]'h2 := by
--   generalize hgo : go aig xc curr acc = res
--   unfold go at hgo
--   dsimp only at hgo
--   split at hgo
--   · rw [← hgo]
--     intros
--     rename_i h
--     rw [blastPopCount.go_decl_eq, AIG.LawfulVecOperator.decl_eq (f := AIG.RefVec.ite),
--       AIG.LawfulVecOperator.decl_eq (f := blastAdd)]
--     apply AIG.LawfulVecOperator.lt_size_of_lt_aig_size (f := blastAdd)
--     · exact h
--     · intros
--       apply AIG.LawfulVecOperator.lt_size_of_lt_aig_size (f := AIG.RefVec.ite)
--       apply AIG.LawfulVecOperator.lt_size_of_lt_aig_size (f := blastAdd)
--       exact h
--   · simp [← hgo]

-- instance : AIG.LawfulVecOperator α AIG.RefVec blastPopCount where
--   le_size := by
--     intros
--     unfold blastPopCount
--     dsimp only
--     apply blastPopCount.go_le_size
--   decl_eq := by
--     intros
--     unfold blastPopCount
--     dsimp only
--     apply blastPopCount.go_decl_eq

end bitblast
end BVExpr

end Std.Tactic.BVDecide
