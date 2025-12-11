/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Basic
public import Std.Sat.AIG.If
import Init.Grind

@[expose] public section

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
  go aig input distance 0 (by omega) (.emptyWithCapacity w)
where
  go (aig : AIG α) (input : AIG.RefVec aig w) (distance : Nat) (curr : Nat) (hcurr : curr ≤ w)
      (s : AIG.RefVec aig curr) :
      AIG.RefVecEntry α w :=
  if hidx : curr < w then
    if hdist : (distance + curr) < w then
      let s := s.push (input.get (distance + curr) (by omega))
      go aig input distance (curr + 1) (by omega) s
    else
      let zeroRef := aig.mkConstCached false
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
    · apply go_le_size
    · apply go_le_size
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
  · simp [← hgo]
termination_by w - curr

@[grind! .]
theorem blastShiftRightConst_le_size (aig : AIG α) (input : aig.ShiftTarget w) :
    aig.decls.size ≤ (blastShiftRightConst aig input).aig.decls.size := by
  intros
  unfold blastShiftRightConst
  apply blastShiftRightConst.go_le_size

@[grind =]
theorem blastShiftRightConst_decl_eq (aig : AIG α) (input : aig.ShiftTarget w) (idx : Nat)
    (h1 : idx < aig.decls.size) (h2 : idx < (blastShiftRightConst aig input).aig.decls.size) :
    (blastShiftRightConst aig input).aig.decls[idx] = aig.decls[idx] := by
  intros
  unfold blastShiftRightConst
  apply blastShiftRightConst.go_decl_eq

instance : AIG.LawfulVecOperator α AIG.ShiftTarget blastShiftRightConst where
  le_size := blastShiftRightConst_le_size
  decl_eq := blastShiftRightConst_decl_eq

def blastArithShiftRightConst (aig : AIG α) (target : AIG.ShiftTarget aig w) :
    AIG.RefVecEntry α w :=
  let ⟨input, distance⟩ := target
  ⟨aig, go input distance 0 (by omega) (.emptyWithCapacity w)⟩
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

@[grind! .]
theorem blastArithShiftRightConst_le_size (aig : AIG α) (input : aig.ShiftTarget w) :
    aig.decls.size ≤ (blastArithShiftRightConst aig input).aig.decls.size := by
  simp [blastArithShiftRightConst]

@[grind =]
theorem blastArithShiftRightConst_decl_eq (aig : AIG α) (input : aig.ShiftTarget w) (idx : Nat)
    (h1 : idx < aig.decls.size) (h2 : idx < (blastArithShiftRightConst aig input).aig.decls.size) :
    (blastArithShiftRightConst aig input).aig.decls[idx] = aig.decls[idx]'h1 := by
  simp [blastArithShiftRightConst]

instance : AIG.LawfulVecOperator α AIG.ShiftTarget blastArithShiftRightConst where
  le_size := blastArithShiftRightConst_le_size
  decl_eq := blastArithShiftRightConst_decl_eq

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

@[grind! .]
theorem twoPowShift_le_size (aig : AIG α) (input : TwoPowShiftTarget aig w) :
    aig.decls.size ≤ (twoPowShift aig input).aig.decls.size := by
  intros
  unfold twoPowShift
  grind

@[grind =]
theorem twoPowShift_decl_eq (aig : AIG α) (input : TwoPowShiftTarget aig w) (idx : Nat)
    (h1 : idx < aig.decls.size) (h2 : idx < (twoPowShift aig input).aig.decls.size) :
    (twoPowShift aig input).aig.decls[idx] = aig.decls[idx] := by
  intros
  unfold twoPowShift
  grind

instance : AIG.LawfulVecOperator α TwoPowShiftTarget twoPowShift where
  le_size := twoPowShift_le_size
  decl_eq := twoPowShift_decl_eq

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

@[grind! .]
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

@[grind =]
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

@[grind! .]
theorem blastShiftRight_le_size (aig : AIG α) (input : aig.ArbitraryShiftTarget w) :
    aig.decls.size ≤ (blastShiftRight aig input).aig.decls.size := by
  intros
  unfold blastShiftRight
  grind

@[grind =]
theorem blastShiftRight_decl_eq (aig : AIG α) (input : aig.ArbitraryShiftTarget w) (idx : Nat)
    (h1 : idx < aig.decls.size) (h2 : idx < (blastShiftRight aig input).aig.decls.size) :
    (blastShiftRight aig input).aig.decls[idx] = aig.decls[idx] := by
  intros
  unfold blastShiftRight
  grind

instance : AIG.LawfulVecOperator α AIG.ArbitraryShiftTarget blastShiftRight where
  le_size := blastShiftRight_le_size
  decl_eq := blastShiftRight_decl_eq

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

@[grind! .]
theorem twoPowShift_le_size (aig : AIG α) (input : TwoPowShiftTarget aig w) :
    aig.decls.size ≤ (twoPowShift aig input).aig.decls.size := by
  intros
  unfold twoPowShift
  grind

@[grind =]
theorem twoPowShift_decl_eq (aig : AIG α) (input : TwoPowShiftTarget aig w) (idx : Nat)
    (h1 : idx < aig.decls.size) (h2 : idx < (twoPowShift aig input).aig.decls.size) :
    (twoPowShift aig input).aig.decls[idx] = aig.decls[idx] := by
  intros
  unfold twoPowShift
  grind

instance res : AIG.LawfulVecOperator α TwoPowShiftTarget twoPowShift where
  le_size := twoPowShift_le_size
  decl_eq := twoPowShift_decl_eq

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

@[grind! .]
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

@[grind =]
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
    all_goals grind
  · simp [← hgo]
termination_by n - 1 - curr

@[grind! .]
theorem blastArithShiftRight_le_size (aig : AIG α) (input : aig.ArbitraryShiftTarget w) :
    aig.decls.size ≤ (blastArithShiftRight aig input).aig.decls.size := by
  intros
  unfold blastArithShiftRight
  grind

@[grind =]
theorem blastArithShiftRight_decl_eq (aig : AIG α) (input : aig.ArbitraryShiftTarget w) (idx : Nat)
    (h1 : idx < aig.decls.size) (h2 : idx < (blastArithShiftRight aig input).aig.decls.size) :
    (blastArithShiftRight aig input).aig.decls[idx] = aig.decls[idx] := by
  intros
  unfold blastArithShiftRight
  grind

instance : AIG.LawfulVecOperator α AIG.ArbitraryShiftTarget blastArithShiftRight where
  le_size := blastArithShiftRight_le_size
  decl_eq := blastArithShiftRight_decl_eq

end bitblast
end BVExpr

end Std.Tactic.BVDecide
