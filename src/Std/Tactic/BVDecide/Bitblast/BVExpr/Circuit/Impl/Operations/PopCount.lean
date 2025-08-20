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

/-- When inserting a new element `elem` to vec we need to cast all the AIGs of its elements to the new element's AIG (elem.aig)-/
def RefVecVec.set {aigOld aigNew: AIG α} {n w : Nat} (idx : Nat) (vec : RefVecVec aigOld w n) (elem : AIG.RefVec aigNew w) (haig: aigOld.decls.size ≤ aigNew.decls.size) (proof : idx < n ):
  RefVecVec aigNew w n :=
  let vec' : Vector (AIG.RefVec aigNew w) n := vec.vec.map fun refVec => refVec.cast haig
  {vec := vec'.set idx elem proof}

/-- We extract a single bit in position `start` and extend it to haev width `w`-/
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

/-- We recursively extract and extend all bits from `x` and use them to populate `acc`, casting the AIG accordingly -/
def blastExtractAndExtendPopulate (aig : AIG α) (idx : Nat)
    (x : AIG.RefVec aig w) (acc : RefVecVec aig w w) : RefVecEntryVec α w w :=
  if hw : idx < w then
    let res := blastExtractAndExtend aig x idx
    let aig := res.aig
    let bv := res.vec
    let x := x.cast (aig2 := aig) (by simp [res, aig]; apply extractAndExtend_le_size)
    let acc := acc.cast (aig2 := aig) (by simp [res, aig]; apply extractAndExtend_le_size)
    let acc := acc.set idx bv (by simp [res, aig]) hw
    blastExtractAndExtendPopulate aig (idx + 1) x acc
  else
    {aig := aig, vec := acc}

theorem extractAndExtendPopulate_le_size (aig : AIG α) (x : AIG.RefVec aig w) (acc : RefVecVec aig w w) :
    aig.decls.size ≤ (blastExtractAndExtendPopulate aig idx x acc).aig.decls.size := by
  unfold blastExtractAndExtendPopulate
  dsimp only
  split
  · apply Nat.le_trans ?_ (by apply extractAndExtendPopulate_le_size)
    apply extractAndExtend_le_size
  · simp

theorem extractAndExtendPopulate_decl_eq (idx' : Nat) (aig : AIG α) (x : AIG.RefVec aig w) (acc : RefVecVec aig w w) :
    ∀ (idx : Nat) (h1) (h2),
        (blastExtractAndExtendPopulate aig idx' x acc).aig.decls[idx]'h2 = aig.decls[idx]'h1 := by
  generalize hres : blastExtractAndExtendPopulate aig idx' x acc = res
  unfold blastExtractAndExtendPopulate at hres
  dsimp only at hres
  split at hres
  · rw [← hres]
    intros
    rw [extractAndExtendPopulate_decl_eq, extractAndExtend_decl_eq]
    apply AIG.LawfulVecOperator.lt_size_of_lt_aig_size (f := blastZeroExtend)
    apply AIG.LawfulVecOperator.lt_size_of_lt_aig_size (f := blastExtract)
    omega
  · simp [← hres]

/-- Given a vector of references belonging to the same AIG `oldParSum`, we create a node to add the `curr`-th couple of elements and push the add node to `newParSum` -/
def blastAddVec (aig : AIG α) (usedNodes validNodes : Nat) (oldParSum : RefVecVec aig w w)
      (newParSum : RefVecVec aig w w) (hval : validNodes ≤ w) :
    RefVecEntryVec α w w :=
    if hc1 : usedNodes < validNodes then
      if hc2 : usedNodes + 1 < validNodes then
        let res := blastAdd aig ⟨oldParSum.vec.get ⟨usedNodes, by omega⟩, oldParSum.vec.get ⟨usedNodes + 1, by omega⟩⟩
        let aig := res.aig
        let add := res.vec
        have := AIG.LawfulVecOperator.le_size (f := blastAdd) ..
        let oldParSum := oldParSum.cast (aig2 := aig) this
        let newVec := newParSum.set ((usedNodes + 1)/ 2) add (by omega) (by omega) -- set also includes casting
        blastAddVec aig (usedNodes + 2) validNodes oldParSum newVec hval
      else
        let zero := blastConst aig (w := w) 0
        let res := blastAdd aig ⟨oldParSum.vec.get ⟨usedNodes, by omega⟩, zero⟩
        let aig := res.aig
        let add := res.vec
        have := AIG.LawfulVecOperator.le_size (f := blastAdd) ..
        let oldParSum := oldParSum.cast (aig2 := aig) this
        let newVec := newParSum.set ((usedNodes + 1)/ 2) add (by omega) (by omega) -- set also includes casting
        blastAddVec aig (usedNodes + 2) validNodes oldParSum newVec hval
    else
      ⟨aig, newParSum⟩


theorem addVec_le_size (aig : AIG α) (usedNodes validNodes: Nat) (oldParSum : RefVecVec aig w w) (newParSum : RefVecVec aig w w)
              (hvalid : validNodes ≤ w) :
    aig.decls.size ≤ (blastAddVec aig usedNodes validNodes oldParSum newParSum hvalid).aig.decls.size := by
  unfold blastAddVec
  dsimp only
  split
  · split
    <;> (refine Nat.le_trans ?_ (by apply addVec_le_size); apply AIG.LawfulVecOperator.le_size)
  · simp

theorem addVec_decl_eq (aig : AIG α) (usedNodes validNodes: Nat) (oldParSum : RefVecVec aig w w) (newParSum : RefVecVec aig w w)
              (hvalid : validNodes ≤ w) :
    ∀ (idx : Nat) (h1) (h2),
        (blastAddVec aig usedNodes validNodes oldParSum newParSum hvalid).aig.decls[idx]'h1 = aig.decls[idx]'h2 := by
  generalize hres : blastAddVec aig usedNodes validNodes oldParSum newParSum hvalid = res
  unfold blastAddVec at hres
  dsimp only at hres
  split at hres
  · split at hres
    · rw [← hres]
      intros
      rw [addVec_decl_eq]
      · apply AIG.LawfulVecOperator.decl_eq (f := blastAdd)
      · apply AIG.LawfulVecOperator.lt_size_of_lt_aig_size (f := blastAdd)
        assumption
    · rw [← hres]
      intros
      rw [addVec_decl_eq]
      · apply AIG.LawfulVecOperator.decl_eq (f := blastAdd)
      · apply AIG.LawfulVecOperator.lt_size_of_lt_aig_size (f := blastAdd)
        assumption
  · simp [← hres]

/-- We first extend all the single bits in the input BitVec w to have width `w`, then compute
the parallel prefix sum given these bits.-/
def blastPopCount (aig : AIG α) (x : AIG.RefVec aig w) : AIG.RefVecEntry α w :=
  if hw : 1 < w then
    -- init
    let zero := blastConst aig (w := w) 0
    let initVec : Vector (AIG.RefVec aig w) w := Vector.replicate (α := AIG.RefVec aig w) (n := w) (v := zero)
    let initRefVec : RefVecVec aig w w := {vec := initVec}
    let extendedBits : RefVecEntryVec α w w := blastExtractAndExtendPopulate aig 0 x initRefVec
    let aig := extendedBits.aig
    let parSumInit := extendedBits.vec
    go aig w parSumInit (by omega) (by omega)
  else
    if hw' : 0 < w then
      ⟨aig, x⟩
    else
      let zero := blastConst aig (w := w) 0
      ⟨aig, zero⟩
where
  go (aig : AIG α) (validNodes : Nat) (parSum : RefVecVec aig w w) (hin : 1 < w) (hval : validNodes ≤ w) : AIG.RefVecEntry α w :=
  if hlt : 1 < validNodes  then
    let res := blastAddVec aig 0 validNodes parSum parSum hval
    let aig := res.aig
    let addNodesVec := res.vec
    go aig ((validNodes + 1)/2) addNodesVec hin (by omega)
  else
    ⟨aig, parSum.vec.get ⟨0, by omega⟩⟩

namespace blastPopCount

theorem go_le_size (aig : AIG α) (validNodes: Nat) (parSum : RefVecVec aig w w) (hin : 1 < w) (hval : validNodes ≤ w) :
    aig.decls.size ≤ (go aig validNodes parSum hin hval).aig.decls.size := by
  unfold go
  dsimp only
  split
  · refine Nat.le_trans ?_ (by apply go_le_size)
    apply addVec_le_size
  · simp

theorem go_le_size' (validNodes : Nat) (aig : AIG α) (input : aig.RefVec w) (h : 1 < w) (hval : validNodes ≤ w) :
  let zero := blastConst aig (w := w) 0
  let initVec : Vector (AIG.RefVec aig w) w := Vector.replicate (α := AIG.RefVec aig w) (n := w) (v := zero)
  let initRefVec : RefVecVec aig w w := {vec := initVec}
  aig.decls.size ≤
  (go (blastExtractAndExtendPopulate aig 0 input initRefVec ).aig validNodes
          (blastExtractAndExtendPopulate aig 0 input initRefVec).vec h hval).aig.decls.size:= by
  unfold go
  dsimp only
  split
  · refine Nat.le_trans ?_ (by apply go_le_size)
    refine Nat.le_trans ?_ (by apply addVec_le_size)
    apply extractAndExtendPopulate_le_size
  · apply extractAndExtendPopulate_le_size

theorem go_decl_eq {w : Nat} (validNodes : Nat) (aig : AIG α) (parSum : RefVecVec aig w w)  (hin : 1 < w) (hval : validNodes ≤ w)
  : ∀ (idx : Nat) h1 h2,
    (go aig validNodes parSum hin hval).aig.decls[idx]'h1 =
    aig.decls[idx]'h2 := by
  generalize hgo : go aig validNodes parSum hin hval = res
  unfold go at hgo
  dsimp only at hgo
  split at hgo
  · rw [← hgo]
    intros idx hidx hidx'
    rw [go_decl_eq]
    · exact addVec_decl_eq aig 0 validNodes parSum parSum (by omega) (by omega) ?_ hidx'
    · have :=  addVec_le_size aig 0 validNodes parSum parSum (by omega)
      exact Nat.lt_of_lt_of_le hidx' this
  · simp [← hgo]

instance : AIG.LawfulVecOperator α AIG.RefVec blastPopCount where
  le_size := by
    intros
    unfold blastPopCount
    split
    · apply go_le_size'
    · split <;> simp
  decl_eq := by
    intros
    unfold blastPopCount
    dsimp only
    expose_names
    split
    · have := extractAndExtendPopulate_le_size (idx := 0) aig input
                    ({vec := Vector.replicate len (blastConst aig 0)})
      rw [go_decl_eq]
      apply extractAndExtendPopulate_decl_eq (idx' := 0) aig input
      exact Nat.lt_of_lt_of_le h1 this
    · split <;> simp

end blastPopCount

end bitblast
end BVExpr

end Std.Tactic.BVDecide
