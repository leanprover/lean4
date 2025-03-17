/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Std.Tactic.BVDecide.Bitblast.BVExpr.Basic
import Std.Sat.AIG.CachedGatesLemmas
import Std.Sat.AIG.LawfulVecOperator
import Std.Sat.AIG.If

/-!
This module contains the implementation of a bitblaster for `BitVec.shiftRight`.
It distinguishes two cases:
1. Shifting by a constant distance (trivial)
2. Shifting by a symbolic `BitVec` distance (requires symbolic branches over the distance).
-/

namespace Std.Tactic.BVDecide

open Std.Sat

namespace BVExpr
namespace bitblast

variable [Hashable α] [DecidableEq α]

def blastShiftRightConst (aig : AIG α) (target : AIG.ShiftTarget aig w) :
    AIG.RefVecEntry α w :=
  let ⟨input, distance⟩ := target
  go aig input distance 0 (by omega) .empty
where
  go (aig : AIG α) (input : AIG.RefVec aig w) (distance : Nat) (curr : Nat) (hcurr : curr ≤ w)
      (s : AIG.RefVec aig curr) :
      AIG.RefVecEntry α w :=
  if hidx : curr < w then
    if hdist : (distance + curr) < w then
      let s := s.push (input.get (distance + curr) (by omega))
      go aig input distance (curr + 1) (by omega) s
    else
      let res := aig.mkConstCached false
      let aig := res.aig
      let zeroRef := res.ref
      have hfinal := AIG.LawfulOperator.le_size (f := AIG.mkConstCached) ..
      let s := s.cast hfinal
      let input := input.cast hfinal
      let s := s.push zeroRef
      go aig input distance (curr + 1) (by omega) s
  else
    have hcurr : curr = w := by omega
    ⟨aig, hcurr ▸ s⟩
termination_by w - curr

theorem blastShiftRightConst.go_le_size (aig : AIG α) (distance : Nat) (input : AIG.RefVec aig w)
    (curr : Nat) (hcurr : curr ≤ w) (s : AIG.RefVec aig curr) :
    aig.decls.size ≤ (go aig input distance curr hcurr s).aig.decls.size := by
  unfold go
  split
  · dsimp only
    split
    · refine Nat.le_trans ?_ (by apply go_le_size)
      omega
    · refine Nat.le_trans ?_ (by apply go_le_size)
      apply AIG.LawfulOperator.le_size
  · simp
termination_by w - curr

theorem blastShiftRightConst.go_decl_eq (aig : AIG α) (distance : Nat) (input : AIG.RefVec aig w)
    (curr : Nat) (hcurr : curr ≤ w) (s : AIG.RefVec aig curr) :
    ∀ (idx : Nat) (h1) (h2),
        (go aig input distance curr hcurr s).aig.decls[idx]'h2 = aig.decls[idx]'h1 := by
  generalize hgo : go aig input distance curr hcurr s = res
  unfold go at hgo
  split at hgo
  · dsimp only at hgo
    split at hgo
    · rw [← hgo]
      intro idx h1 h2
      rw [blastShiftRightConst.go_decl_eq]
    · rw [← hgo]
      intro idx h1 h2
      rw [blastShiftRightConst.go_decl_eq]
      rw [AIG.LawfulOperator.decl_eq (f := AIG.mkConstCached)]
      apply AIG.LawfulOperator.lt_size_of_lt_aig_size (f := AIG.mkConstCached)
      assumption
  · simp [← hgo]
termination_by w - curr

instance : AIG.LawfulVecOperator α AIG.ShiftTarget blastShiftRightConst where
  le_size := by
    intros
    unfold blastShiftRightConst
    apply blastShiftRightConst.go_le_size
  decl_eq := by
    intros
    unfold blastShiftRightConst
    apply blastShiftRightConst.go_decl_eq

def blastArithShiftRightConst (aig : AIG α) (target : AIG.ShiftTarget aig w) :
    AIG.RefVecEntry α w :=
  let ⟨input, distance⟩ := target
  ⟨aig, go input distance 0 (by omega) .empty⟩
where
  go {aig : AIG α} (input : AIG.RefVec aig w) (distance : Nat) (curr : Nat) (hcurr : curr ≤ w)
      (s : AIG.RefVec aig curr) :
      AIG.RefVec aig w :=
  if hidx : curr < w then
    if hdist : (distance + curr) < w then
      let s := s.push (input.get (distance + curr) (by omega))
      go input distance (curr + 1) (by omega) s
    else
      let s := s.push (input.get (w - 1) (by omega))
      go input distance (curr + 1) (by omega) s
  else
    have hcurr : curr = w := by omega
    hcurr ▸ s
termination_by w - curr

instance : AIG.LawfulVecOperator α AIG.ShiftTarget blastArithShiftRightConst where
  le_size := by
    intros
    unfold blastArithShiftRightConst
    simp
  decl_eq := by
    intros
    unfold blastArithShiftRightConst
    simp

structure TwoPowShiftTarget (aig : AIG α) (w : Nat) where
  n : Nat
  lhs : AIG.RefVec aig w
  rhs : AIG.RefVec aig n
  pow : Nat

namespace blastShiftRight

def twoPowShift (aig : AIG α) (target : TwoPowShiftTarget aig w) : AIG.RefVecEntry α w :=
  let ⟨n, lhs, rhs, pow⟩ := target
  if h : pow < n then
    let res := blastShiftRightConst aig ⟨lhs, 2 ^ pow⟩
    let aig := res.aig
    let shifted := res.vec

    have := AIG.LawfulVecOperator.le_size (f := blastShiftRightConst) ..
    let rhs := rhs.cast this
    let lhs := lhs.cast this
    AIG.RefVec.ite aig ⟨rhs.get pow h, shifted, lhs⟩
  else
    ⟨aig, lhs⟩

instance : AIG.LawfulVecOperator α TwoPowShiftTarget twoPowShift where
  le_size := by
    intros
    unfold twoPowShift
    dsimp only
    split
    · apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := AIG.RefVec.ite)
      apply AIG.LawfulVecOperator.le_size (f := blastShiftRightConst)
    · simp
  decl_eq := by
    intros
    unfold twoPowShift
    dsimp only
    split
    · rw [AIG.LawfulVecOperator.decl_eq (f := AIG.RefVec.ite)]
      rw [AIG.LawfulVecOperator.decl_eq (f := blastShiftRightConst)]
      apply AIG.LawfulVecOperator.lt_size_of_lt_aig_size (f := blastShiftRightConst)
      assumption
    · simp

end blastShiftRight

def blastShiftRight (aig : AIG α) (target : AIG.ArbitraryShiftTarget aig w) :
    AIG.RefVecEntry α w :=
  let ⟨n, input, distance⟩ := target
  if n = 0 then
    ⟨aig, input⟩
  else
    let res := blastShiftRight.twoPowShift aig ⟨_, input, distance, 0⟩
    let aig := res.aig
    let acc := res.vec
    have := AIG.LawfulVecOperator.le_size (f := blastShiftRight.twoPowShift) ..
    let distance := distance.cast this
    go aig distance 0 acc
where
  go {n : Nat} (aig : AIG α) (distance : AIG.RefVec aig n) (curr : Nat)
      (acc : AIG.RefVec aig w) :
      AIG.RefVecEntry α w :=
    if curr < n - 1 then
      let res := blastShiftRight.twoPowShift aig ⟨_, acc, distance, curr + 1⟩
      let aig := res.aig
      let acc := res.vec
      have := AIG.LawfulVecOperator.le_size (f := blastShiftRight.twoPowShift) ..
      let distance := distance.cast this
      go aig distance (curr + 1) acc
    else
      ⟨aig, acc⟩
  termination_by n - 1 - curr

theorem blastShiftRight.go_le_size (aig : AIG α) (distance : AIG.RefVec aig n) (curr : Nat)
    (acc : AIG.RefVec aig w) :
    aig.decls.size ≤ (go aig distance curr acc).aig.decls.size := by
  unfold go
  dsimp only
  split
  · refine Nat.le_trans ?_ (by apply go_le_size)
    apply AIG.LawfulVecOperator.le_size (f := blastShiftRight.twoPowShift)
  · simp
termination_by n - 1 - curr

theorem blastShiftRight.go_decl_eq (aig : AIG α) (distance : AIG.RefVec aig n) (curr : Nat)
    (acc : AIG.RefVec aig w) :
    ∀ (idx : Nat) (h1) (h2),
        (go aig distance curr acc).aig.decls[idx]'h2 = aig.decls[idx]'h1 := by
  generalize hgo : go aig distance curr acc = res
  unfold go at hgo
  dsimp only at hgo
  split at hgo
  · rw [← hgo]
    intros
    rw [blastShiftRight.go_decl_eq]
    rw [AIG.LawfulVecOperator.decl_eq (f := blastShiftRight.twoPowShift)]
    apply AIG.LawfulVecOperator.lt_size_of_lt_aig_size (f := blastShiftRight.twoPowShift)
    assumption
  · simp [← hgo]
termination_by n - 1 - curr


instance : AIG.LawfulVecOperator α AIG.ArbitraryShiftTarget blastShiftRight where
  le_size := by
    intros
    unfold blastShiftRight
    dsimp only
    split
    · simp
    · refine Nat.le_trans ?_ (by apply blastShiftRight.go_le_size)
      apply AIG.LawfulVecOperator.le_size (f := blastShiftRight.twoPowShift)
  decl_eq := by
    intros
    unfold blastShiftRight
    dsimp only
    split
    · simp
    · rw [blastShiftRight.go_decl_eq]
      rw [AIG.LawfulVecOperator.decl_eq (f := blastShiftRight.twoPowShift)]
      apply AIG.LawfulVecOperator.lt_size_of_lt_aig_size (f := blastShiftRight.twoPowShift)
      assumption

namespace blastArithShiftRight

def twoPowShift (aig : AIG α) (target : TwoPowShiftTarget aig w) : AIG.RefVecEntry α w :=
  let ⟨n, lhs, rhs, pow⟩ := target
  if h : pow < n then
    let res := blastArithShiftRightConst aig ⟨lhs, 2 ^ pow⟩
    let aig := res.aig
    let shifted := res.vec

    have := AIG.LawfulVecOperator.le_size (f := blastArithShiftRightConst) ..
    let rhs := rhs.cast this
    let lhs := lhs.cast this
    AIG.RefVec.ite aig ⟨rhs.get pow h, shifted, lhs⟩
  else
    ⟨aig, lhs⟩

instance : AIG.LawfulVecOperator α TwoPowShiftTarget twoPowShift where
  le_size := by
    intros
    unfold twoPowShift
    dsimp only
    split
    · apply AIG.LawfulVecOperator.le_size_of_le_aig_size (f := AIG.RefVec.ite)
      apply AIG.LawfulVecOperator.le_size (f := blastArithShiftRightConst)
    · simp
  decl_eq := by
    intros
    unfold twoPowShift
    dsimp only
    split
    · rw [AIG.LawfulVecOperator.decl_eq (f := AIG.RefVec.ite)]
      rw [AIG.LawfulVecOperator.decl_eq (f := blastArithShiftRightConst)]
      apply AIG.LawfulVecOperator.lt_size_of_lt_aig_size (f := blastArithShiftRightConst)
      assumption
    · simp

end blastArithShiftRight

def blastArithShiftRight (aig : AIG α) (target : AIG.ArbitraryShiftTarget aig w) :
    AIG.RefVecEntry α w :=
  let ⟨n, input, distance⟩ := target
  if n = 0 then
    ⟨aig, input⟩
  else
    let res := blastArithShiftRight.twoPowShift aig ⟨_, input, distance, 0⟩
    let aig := res.aig
    let acc := res.vec
    have := AIG.LawfulVecOperator.le_size (f := blastArithShiftRight.twoPowShift) ..
    let distance := distance.cast this
    go aig distance 0 acc
where
  go {n : Nat} (aig : AIG α) (distance : AIG.RefVec aig n) (curr : Nat)
      (acc : AIG.RefVec aig w) :
      AIG.RefVecEntry α w :=
    if curr < n - 1 then
      let res := blastArithShiftRight.twoPowShift aig ⟨_, acc, distance, curr + 1⟩
      let aig := res.aig
      let acc := res.vec
      have := AIG.LawfulVecOperator.le_size (f := blastArithShiftRight.twoPowShift) ..
      let distance := distance.cast this
      go aig distance (curr + 1) acc
    else
      ⟨aig, acc⟩
  termination_by n - 1 - curr

theorem blastArithShiftRight.go_le_size (aig : AIG α) (distance : AIG.RefVec aig n) (curr : Nat)
    (acc : AIG.RefVec aig w) :
    aig.decls.size ≤ (go aig distance curr acc).aig.decls.size := by
  unfold go
  dsimp only
  split
  · refine Nat.le_trans ?_ (by apply go_le_size)
    apply AIG.LawfulVecOperator.le_size (f := blastArithShiftRight.twoPowShift)
  · simp
termination_by n - 1 - curr

theorem blastArithShiftRight.go_decl_eq (aig : AIG α) (distance : AIG.RefVec aig n) (curr : Nat)
    (acc : AIG.RefVec aig w) :
    ∀ (idx : Nat) (h1) (h2),
        (go aig distance curr acc).aig.decls[idx]'h2 = aig.decls[idx]'h1 := by
  generalize hgo : go aig distance curr acc = res
  unfold go at hgo
  dsimp only at hgo
  split at hgo
  · rw [← hgo]
    intros
    rw [blastArithShiftRight.go_decl_eq]
    rw [AIG.LawfulVecOperator.decl_eq (f := blastArithShiftRight.twoPowShift)]
    apply AIG.LawfulVecOperator.lt_size_of_lt_aig_size (f := blastArithShiftRight.twoPowShift)
    assumption
  · simp [← hgo]
termination_by n - 1 - curr


instance : AIG.LawfulVecOperator α AIG.ArbitraryShiftTarget blastArithShiftRight where
  le_size := by
    intros
    unfold blastArithShiftRight
    dsimp only
    split
    · simp
    · refine Nat.le_trans ?_ (by apply blastArithShiftRight.go_le_size)
      apply AIG.LawfulVecOperator.le_size (f := blastArithShiftRight.twoPowShift)
  decl_eq := by
    intros
    unfold blastArithShiftRight
    dsimp only
    split
    · simp
    · rw [blastArithShiftRight.go_decl_eq]
      rw [AIG.LawfulVecOperator.decl_eq (f := blastArithShiftRight.twoPowShift)]
      apply AIG.LawfulVecOperator.lt_size_of_lt_aig_size (f := blastArithShiftRight.twoPowShift)
      assumption

end bitblast
end BVExpr

end Std.Tactic.BVDecide
