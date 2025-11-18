/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luisa Cicolini, Siddharth Bhat, Henrik Böving
-/

prelude
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Const
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Sub
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Eq
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Extract
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.ZeroExtend
public import Std.Sat.AIG.If

/-!
This module contains the implementation of a bitblaster for `BitVec.popCount`.
-/

namespace Std.Tactic.BVDecide

open Std.Sat

variable [Hashable α] [DecidableEq α]

namespace BVExpr
namespace bitblast

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

/-- We extract one bit at a time from the initial vector and zero-extend them to width `w`,
  appending the result to `acc` which eventually will have size `w * w`-/
def blastExtractAndExtendPopulate (aig : AIG α) (idx : Nat) (x : AIG.RefVec aig w)
    (acc : AIG.RefVec aig (w * idx)) (hlt : idx ≤ w)
  : AIG.RefVecEntry α (w * w) :=
  if hidx : idx < w then
    let res := blastExtractAndExtend aig x idx
    let aigRes := res.aig
    let bv := res.vec
    have := extractAndExtend_le_size aig x idx
    let acc := acc.cast (aig2 := aigRes) this
    let x := x.cast (aig2 := aigRes) this
    let acc := acc.append bv
    have hcast : w * (idx + 1) = w * idx + w := by simp [Nat.mul_add]
    have acc := hcast▸acc
    blastExtractAndExtendPopulate (aigRes) (idx + 1) (x := x) (acc := acc) (by omega)
  else
    have : idx = w := by omega
    have hcast : w * idx = w * w := by rw [this]
    ⟨aig, hcast▸acc⟩

theorem extractAndExtendPopulate_le_size (aig : AIG α) (idx : Nat) (x : AIG.RefVec aig w) (acc : AIG.RefVec aig (w * idx)) (hlt : idx ≤ w):
    aig.decls.size ≤ (blastExtractAndExtendPopulate aig idx x acc hlt).aig.decls.size := by
  unfold blastExtractAndExtendPopulate
  dsimp only
  split
  · apply Nat.le_trans ?_ (by apply extractAndExtendPopulate_le_size)
    apply extractAndExtend_le_size
  · simp

theorem extractAndExtendPopulate_decl_eq  (aig : AIG α) (idx' : Nat) (x : AIG.RefVec aig w) (acc : AIG.RefVec aig (w * idx')) (hlt : idx' ≤ w):
    ∀ (idx : Nat) (h1) (h2),
        (blastExtractAndExtendPopulate aig idx' x acc hlt).aig.decls[idx]'h2 = aig.decls[idx]'h1 := by
  generalize hres : blastExtractAndExtendPopulate aig idx' x acc hlt = res
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
def blastAddVec (aig : AIG α) (usedNodes validNodes : Nat)
      (oldParSum : AIG.RefVec aig (validNodes * w)) (newParSum : AIG.RefVec aig ((usedNodes / 2) * w))
      (hval : validNodes ≤ w) (hused : usedNodes ≤ validNodes + 1) (hmod : usedNodes % 2 = 0) :
   AIG.RefVecEntry α (((validNodes+1)/2) * w) :=
  if hc1 : usedNodes < validNodes then
    -- rhs
    let rhs := if h : usedNodes + 1 < validNodes then
                let targetExtract : ExtractTarget aig w := {vec := oldParSum, start := (usedNodes + 1) * w}
                let res := blastExtract aig targetExtract
                let aig := res.aig
                have := AIG.LawfulVecOperator.le_size (f := blastExtract) (input := targetExtract)
                let oldParSum := oldParSum.cast this
                let newParSum := newParSum.cast this
                res.vec
              else blastConst aig (w := w) 0
    -- lhs
    let targetExtract : ExtractTarget aig w := {vec := oldParSum, start := usedNodes * w}
    let res := blastExtract aig targetExtract
    let aig := res.aig
    let lhs := res.vec
    have := AIG.LawfulVecOperator.le_size (f := blastExtract) ..
    let oldParSum := oldParSum.cast this
    let newParSum := newParSum.cast this
    let rhs := rhs.cast this
    -- add
    let res := blastAdd aig ⟨lhs, rhs⟩
    let aig := res.aig
    let add := res.vec
    have := AIG.LawfulVecOperator.le_size (f := blastAdd) ..
    let oldParSum := oldParSum.cast this
    let newParSum := newParSum.cast this
    let rhs := rhs.cast this
    let lhs := lhs.cast this
    let newVec := newParSum.append add
    have hcast : usedNodes / 2 * w + w = (usedNodes + 2) / 2 * w := by
        simp [show usedNodes / 2 * w + w = usedNodes / 2 * w + 1 * w by omega,
            show (usedNodes + 2) / 2 = usedNodes/2 + 1 by omega, Nat.add_mul]
    blastAddVec aig (usedNodes + 2) validNodes oldParSum (hcast▸newVec) hval (by omega) (by omega)
  else
    have hor : usedNodes = validNodes ∨ usedNodes = validNodes + 1 := by omega
    have hcast : usedNodes / 2 * w = (validNodes + 1) / 2 * w := by
      simp_all
      rcases hor with hor|hor
      · simp [hor] at *
        rw [show (validNodes + 1) / 2 = validNodes / 2 by omega]
      · simp [hor] at *
    let newParSum := hcast▸newParSum
    ⟨aig, newParSum⟩

theorem addVec_le_size (aig : AIG α) (usedNodes validNodes: Nat)
      (oldParSum : AIG.RefVec aig (validNodes * w)) (newParSum : AIG.RefVec aig ((usedNodes / 2) * w))
      (hval : validNodes ≤ w) (hused : usedNodes ≤ validNodes + 1) (hmod : usedNodes % 2 = 0) :
    aig.decls.size ≤ (blastAddVec aig usedNodes validNodes oldParSum newParSum hval hused hmod).aig.decls.size := by
  unfold blastAddVec
  dsimp only
  split
  · simp
    <;> (refine Nat.le_trans ?_ (by apply addVec_le_size); apply AIG.LawfulVecOperator.le_size)
  · simp

theorem addVec_decl_eq (aig : AIG α) (usedNodes validNodes: Nat)
    (oldParSum : AIG.RefVec aig (validNodes * w)) (newParSum : AIG.RefVec aig ((usedNodes / 2) * w))
    (hval : validNodes ≤ w) (hused : usedNodes ≤ validNodes + 1) (hmod : usedNodes % 2 = 0) :
    ∀ (idx : Nat) (h1) (h2),
        (blastAddVec aig usedNodes validNodes oldParSum newParSum hval hused hmod).aig.decls[idx]'h1 = aig.decls[idx]'h2 := by
  generalize hres : blastAddVec aig usedNodes validNodes oldParSum newParSum hval hused hmod = res
  unfold blastAddVec at hres
  dsimp only at hres
  split at hres
  · simp at hres
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
    let initAcc := blastConst (aig := aig) (w := 0) (val := 0)
    let res := blastExtractAndExtendPopulate aig 0 x initAcc (by omega)
    let aig := res.aig
    let extendedBits := res.vec
    have := extractAndExtendPopulate_le_size
    let x := x.cast (aig2 := res.aig) (by apply this)
    go aig w extendedBits (by omega) (by omega) (by omega)
  else
    if hw' : 0 < w then
      ⟨aig, x⟩
    else
      let zero := blastConst aig (w := w) 0
      ⟨aig, zero⟩
where
  go (aig : AIG α) (validNodes : Nat) (parSum : AIG.RefVec aig (validNodes * w))
      (hin : 1 < w) (hval : validNodes ≤ w) (hval' : 0 < validNodes) : AIG.RefVecEntry α w :=
  if hlt : 1 < validNodes  then
    have hcastZero : 0 = 0 / 2 * w := by omega
    let initAcc := blastConst (aig := aig) (w := 0) (val := 0)
    let res := blastAddVec aig 0 validNodes parSum (hcastZero▸initAcc) hval (by omega) (by omega)
    let aig := res.aig
    let parSum := res.vec
    go (aig := aig) (validNodes := (validNodes + 1)/2) (parSum := parSum) (hin := hin) (hval := by omega) (by omega)
  else
    have hcast : validNodes * w = w := by
      simp [show validNodes = 1 by omega]
    ⟨aig, hcast▸parSum⟩


theorem blastPopCount.go_le_size (aig : AIG α) (validNodes : Nat) (parSum : AIG.RefVec aig (validNodes * w))
      (hin : 1 < w) (hval : validNodes ≤ w) (hval' : 0 < validNodes) :
    aig.decls.size ≤ (go aig validNodes parSum hin hval hval').aig.decls.size := by
  unfold go
  dsimp only
  split
  · refine Nat.le_trans ?_ (by apply go_le_size)
    apply addVec_le_size
  · simp


theorem blastPopCount.go_le_size' (aig : AIG α) (input : aig.RefVec w) (h : 1 < w) :
    let initAcc := blastConst (aig := aig) (w := 0) (val := 0)
  aig.decls.size ≤
    (go (blastExtractAndExtendPopulate aig 0 input initAcc (by omega)).aig w
        (blastExtractAndExtendPopulate aig 0 input initAcc (by omega)).vec
        h (by omega) (by omega)).aig.decls.size:= by
  unfold go
  dsimp only
  split
  · refine Nat.le_trans ?_ (by apply go_le_size)
    refine Nat.le_trans ?_ (by apply addVec_le_size)
    apply extractAndExtendPopulate_le_size
  · omega

theorem blastPopCount.go_decl_eq {w : Nat} (validNodes : Nat) (aig : AIG α) (parSum : AIG.RefVec aig (validNodes * w))
      (hin : 1 < w) (hval : validNodes ≤ w) (hval' : 0 < validNodes)  : ∀ (idx : Nat) h1 h2,
    (go aig validNodes parSum hin hval hval').aig.decls[idx]'h1 =
    aig.decls[idx]'h2 := by
  generalize hgo : go aig validNodes parSum hin hval hval' = res
  unfold go at hgo
  dsimp only at hgo
  split at hgo
  · rw [← hgo]
    intros idx hidx hidx'
    rw [go_decl_eq]
    · apply addVec_decl_eq
    · let initAcc := blastConst (aig := aig) (w := 0) (val := 0)
      have hcast : 0 = 0/2*w := by omega
      have := addVec_le_size aig 0 validNodes parSum (hcast▸initAcc) (by omega) (by omega) (by omega)
      exact Nat.lt_of_lt_of_le hidx' this
  · simp [← hgo]

instance : AIG.LawfulVecOperator α AIG.RefVec blastPopCount where
  le_size := by
    intros
    unfold blastPopCount
    split
    · apply blastPopCount.go_le_size'
    · split <;> simp
  decl_eq := by sorry
    -- intros
    -- unfold blastPopCount
    -- dsimp only
    -- expose_names
    -- split
    -- · let initAcc := blastConst (aig := aig) (w := 0) (val := 0)
    --   have := extractAndExtendPopulate_le_size (idx := 0) aig input initAcc (by omega)
    --   rw [blastPopCount.go_decl_eq]
    --   apply extractAndExtendPopulate_decl_eq (idx' := 0) aig input
    --   exact Nat.lt_of_lt_of_le h1 this
    -- · split <;> simp

end bitblast
end BVExpr

end Std.Tactic.BVDecide
