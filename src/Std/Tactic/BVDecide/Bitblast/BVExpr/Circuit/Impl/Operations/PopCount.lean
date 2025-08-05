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
structure RefVecVec (α : Type) [DecidableEq α] [Hashable α] [DecidableEq α] (aig : AIG α) (w : Nat) (n : Nat) where
  vec : Vector (AIG.RefVec aig w) n

/-- A vector of `AIG.RefVec aig w` (vec) pointing to the same AIG (aig)-/
structure RefVecEntryVec (α : Type) [DecidableEq α] [Hashable α] [DecidableEq α] (w : Nat) (n : Nat) where
  aig : AIG α
  vec : RefVecVec α aig w n

/-- When pushing a new element `elem` to vec we need to cast all the AIGs of its elements to the new element's AIG (elem.aig)-/
def RefVecVec.push (vec : RefVecVec α aigOld w n) (elem : AIG.RefVecEntry α w) (haig : aigOld.decls.size ≤ elem.aig.decls.size) :
  RefVecVec α elem.aig w (n + 1) :=
  let vec' : Vector (AIG.RefVec elem.aig w) n := vec.vec.map fun refVec => refVec.cast haig
  { vec := vec'.push elem.vec}

/-- We extract one bit from `x` and extend it to width `w` -/
def extractAndExtend (start : Nat) (aig : AIG α) (x : AIG.RefVec aig w) : AIG.RefVecEntry α w :=
  -- extract 1 bit starting from start
  let targetExtract : ExtractTarget aig 1 := {
    vec := x,
    start := start
  }
  let res := blastExtract aig targetExtract
  let aig := res.aig
  let extract := res.vec
  -- zero-extend the extracted portion to have
  let targetExtend : AIG.ExtendTarget aig w := {
    vec := extract,
    w := 1
  }
  let res := blastZeroExtend aig targetExtend
  let aig := res.aig
  let extend := res.vec
  ⟨aig, extend⟩

theorem extractAndExtend_le_size (start : Nat) (aig : AIG α) (x : AIG.RefVec aig w):
    aig.decls.size ≤ (extractAndExtend start aig x).aig.decls.size := by
  unfold extractAndExtend
  dsimp only
  apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := blastZeroExtend)
  apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := blastExtract)
  omega

/-- We recursively extract and extend all bits from `x` and use them to populate `acc`, casting the AIG accordingly -/
def extractAndExtendPopulate (start : Nat) (aig : AIG α) (x : AIG.RefVec aig w) (acc : RefVecEntryVec α w start) (hw : start ≤ w): RefVecEntryVec α w w :=
  if hw : start < w then
    let extendedBV := extractAndExtend start aig x
    let newVec := acc.vec.push extendedBV (by sorry)
    let newAcc : RefVecEntryVec α w (start + 1) := ⟨extendedBV.aig, newVec⟩
    extractAndExtendPopulate (start + 1) aig x newAcc (by omega)
  else
    have hs : start = w := by omega
    hs ▸ acc

/-- Given a vector of references belonging to the same AIG `oldParSum`, we create a note to add the `curr`-th couple of elements and use that to populate a new vector `newParSum` -/
def addVec (aig : AIG α) (currNumNodes curr: Nat) (oldParSum : RefVecEntryVec α w currNumNodes) (newParSum : RefVecEntryVec α w curr) (hw : currNumNodes ≤ w) (hcs : curr < currNumNodes - 1) : RefVecEntryVec α w (currNumNodes/2) :=
  if curr < currNumNodes/2 then
    -- create add node from the nodes in oldParSum
    let res := blastAdd oldParSum.aig ⟨oldParSum.vec.vec.get ⟨curr, by omega⟩, oldParSum.vec.vec.get ⟨curr + 1, by omega⟩⟩
    -- push add node to newParSum
    let newVec := newParSum.vec.push res (by sorry)
    let newParSum : RefVecEntryVec α w (curr + 1) := ⟨res.aig, newVec⟩
    let newParSum.vec := newVec
    addVec aig (currNumNodes := currNumNodes) (curr := curr + 1) oldParSum newParSum hw (by sorry)
  else
    oldParSum


def blastPopCount (aig : AIG α) (x : AIG.RefVec aig w) :
    AIG.RefVecEntry α w :=
  if hw : 0 < w then
    let initVec' : Vector (AIG.RefVec aig w) 0 := Vector.emptyWithCapacity 0
    let initVec : RefVecVec α aig w 0 := {vec := initVec'}
    let acc : RefVecEntryVec α w 0 := {aig := aig, vec := initVec}
    let extendedBits : RefVecEntryVec α w w := extractAndExtendPopulate 0 aig x acc (by omega)
    go aig w extendedBits (by constructor; omega)
  else
    let zero := blastConst aig (w := w) 0
    ⟨aig, zero⟩
where
  go (aig : AIG α) (fuel : Nat) (parSum : RefVecEntryVec α w fuel) (hw : NeZero w) :=
  if 0 < fuel then
    let outpuVec : Vector (AIG.RefVec aig w) 0 := Vector.emptyWithCapacity 0
    let outpuRefVec : RefVecVec α aig w 0 := {vec := outpuVec}
    let outpuRefVecEntryVec : RefVecEntryVec α w 0 := {aig := aig, vec := outpuRefVec}
    let addNodes := addVec aig (currNumNodes := fuel) (curr := 0) (oldParSum := parSum) (newParSum := outpuRefVecEntryVec) (by sorry) (by sorry)
    go aig (fuel/2) addNodes hw
    sorry
  else
    sorry

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

theorem blastPopCount.go_decl_eq (aig : AIG α) (curr : Nat)  (acc : AIG.RefVec aig w)
    (xc : AIG.RefVec aig w) :
    ∀ (idx : Nat) h1 h2,
        (go aig xc curr acc).aig.decls[idx]'h1 = aig.decls[idx]'h2 := by
  generalize hgo : go aig xc curr acc = res
  unfold go at hgo
  dsimp only at hgo
  split at hgo
  · rw [← hgo]
    intros
    rename_i h
    rw [blastPopCount.go_decl_eq, AIG.LawfulVecOperator.decl_eq (f := AIG.RefVec.ite),
      AIG.LawfulVecOperator.decl_eq (f := blastAdd)]
    apply AIG.LawfulVecOperator.lt_size_of_lt_aig_size (f := blastAdd)
    · exact h
    · intros
      apply AIG.LawfulVecOperator.lt_size_of_lt_aig_size (f := AIG.RefVec.ite)
      apply AIG.LawfulVecOperator.lt_size_of_lt_aig_size (f := blastAdd)
      exact h
  · simp [← hgo]

instance : AIG.LawfulVecOperator α AIG.RefVec blastPopCount where
  le_size := by
    intros
    unfold blastPopCount
    dsimp only
    apply blastPopCount.go_le_size
  decl_eq := by
    intros
    unfold blastPopCount
    dsimp only
    apply blastPopCount.go_decl_eq

end bitblast
end BVExpr

end Std.Tactic.BVDecide
