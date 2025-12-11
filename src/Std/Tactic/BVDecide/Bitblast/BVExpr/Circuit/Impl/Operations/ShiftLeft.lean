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
This module contains the implementation of a bitblaster for `BitVec.shiftLeft`.
It distinguishes two cases:
1. Shifting by a constant distance (trivial)
2. Shifting by a symbolic `BitVec` distance (requires symbolic branches over the distance).
-/

namespace Std.Tactic.BVDecide

open Std.Sat

namespace BVExpr
namespace bitblast

variable [Hashable α] [DecidableEq α]

def blastShiftLeftConst (aig : AIG α) (target : AIG.ShiftTarget aig w) :
    AIG.RefVecEntry α w :=
  let ⟨input, distance⟩ := target
  go aig input distance 0 (by omega) (.emptyWithCapacity w)
where
  go (aig : AIG α) (input : AIG.RefVec aig w) (distance : Nat) (curr : Nat) (hcurr : curr ≤ w)
      (s : AIG.RefVec aig curr) :
      AIG.RefVecEntry α w :=
  if hidx : curr < w then
    if hdist : curr < distance then
      let zeroRef := aig.mkConstCached false
      let s := s.push zeroRef
      go aig input distance (curr + 1) (by omega) s
    else
      let s := s.push (input.get (curr - distance) (by omega))
      go aig input distance (curr + 1) (by omega) s
  else
    have hcurr : curr = w := by omega
    ⟨aig, hcurr ▸ s⟩
  termination_by w - curr

theorem blastShiftLeftConst.go_le_size (aig : AIG α) (distance : Nat) (input : AIG.RefVec aig w)
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

theorem blastShiftLeftConst.go_decl_eq (aig : AIG α) (distance : Nat) (input : AIG.RefVec aig w)
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
      rw [blastShiftLeftConst.go_decl_eq]
    · rw [← hgo]
      intro idx h1 h2
      rw [blastShiftLeftConst.go_decl_eq]
  · simp [← hgo]
termination_by w - curr

@[grind! .]
theorem blastShiftLeftConst_le_size (aig : AIG α) (input : aig.ShiftTarget w) :
    aig.decls.size ≤ (blastShiftLeftConst aig input).aig.decls.size := by
  intros
  unfold blastShiftLeftConst
  apply blastShiftLeftConst.go_le_size

@[grind =]
theorem blastShiftLeftConst_decl_eq (aig : AIG α) (input : aig.ShiftTarget w) (idx : Nat)
    (h1 : idx < aig.decls.size) (h2 : idx < (blastShiftLeftConst aig input).aig.decls.size) :
    (blastShiftLeftConst aig input).aig.decls[idx] = aig.decls[idx] := by
  intros
  unfold blastShiftLeftConst
  apply blastShiftLeftConst.go_decl_eq

instance : AIG.LawfulVecOperator α AIG.ShiftTarget blastShiftLeftConst where
  le_size := blastShiftLeftConst_le_size
  decl_eq := blastShiftLeftConst_decl_eq

namespace blastShiftLeft

structure TwoPowShiftTarget (aig : AIG α) (w : Nat) where
  n : Nat
  lhs : AIG.RefVec aig w
  rhs : AIG.RefVec aig n
  pow : Nat

def twoPowShift (aig : AIG α) (target : TwoPowShiftTarget aig w) : AIG.RefVecEntry α w :=
  let ⟨n, lhs, rhs, pow⟩ := target
  if h : pow < n then
    let res := blastShiftLeftConst aig ⟨lhs, 2 ^ pow⟩
    let aig := res.aig
    let shifted := res.vec

    have := AIG.LawfulVecOperator.le_size (f := blastShiftLeftConst) ..
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

end blastShiftLeft

def blastShiftLeft (aig : AIG α) (target : AIG.ArbitraryShiftTarget aig w) :
    AIG.RefVecEntry α w :=
  let ⟨n, input, distance⟩ := target
  if n = 0 then
    ⟨aig, input⟩
  else
    let res := blastShiftLeft.twoPowShift aig ⟨_, input, distance, 0⟩
    let aig := res.aig
    let acc := res.vec
    have := AIG.LawfulVecOperator.le_size (f := blastShiftLeft.twoPowShift) ..
    let distance := distance.cast this
    go aig distance 0 acc
where
  go {n : Nat} (aig : AIG α) (distance : AIG.RefVec aig n) (curr : Nat)
      (acc : AIG.RefVec aig w) :
      AIG.RefVecEntry α w :=
    if curr < n - 1 then
      let res := blastShiftLeft.twoPowShift aig ⟨_, acc, distance, curr + 1⟩
      let aig := res.aig
      let acc := res.vec
      have := AIG.LawfulVecOperator.le_size (f := blastShiftLeft.twoPowShift) ..
      let distance := distance.cast this
      go aig distance (curr + 1) acc
    else
      ⟨aig, acc⟩
  termination_by n - 1 - curr

@[grind! .]
theorem blastShiftLeft.go_le_size (aig : AIG α) (distance : AIG.RefVec aig n) (curr : Nat)
    (acc : AIG.RefVec aig w) :
    aig.decls.size ≤ (go aig distance curr acc).aig.decls.size := by
  unfold go
  dsimp only
  split
  · refine Nat.le_trans ?_ (by apply go_le_size)
    apply AIG.LawfulVecOperator.le_size (f := blastShiftLeft.twoPowShift)
  · simp
termination_by n - 1 - curr

@[grind =]
theorem blastShiftLeft.go_decl_eq (aig : AIG α) (distance : AIG.RefVec aig n) (curr : Nat)
    (acc : AIG.RefVec aig w) :
    ∀ (idx : Nat) (h1) (h2),
        (go aig distance curr acc).aig.decls[idx]'h2 = aig.decls[idx]'h1 := by
  generalize hgo : go aig distance curr acc = res
  unfold go at hgo
  dsimp only at hgo
  split at hgo
  · rw [← hgo]
    intros
    rw [blastShiftLeft.go_decl_eq]
    rw [AIG.LawfulVecOperator.decl_eq (f := blastShiftLeft.twoPowShift)]
    apply AIG.LawfulVecOperator.lt_size_of_lt_aig_size (f := blastShiftLeft.twoPowShift)
    assumption
  · simp [← hgo]
termination_by n - 1 - curr

@[grind! .]
theorem blastShiftLeft_le_size (aig : AIG α) (input : aig.ArbitraryShiftTarget w) :
    aig.decls.size ≤ (blastShiftLeft aig input).aig.decls.size := by
  intros
  unfold blastShiftLeft
  grind

@[grind =]
theorem blastShiftLeft_decl_eq (aig : AIG α) (input : aig.ArbitraryShiftTarget w) (idx : Nat)
    (h1 : idx < aig.decls.size) (h2 : idx < (blastShiftLeft aig input).aig.decls.size) :
    (blastShiftLeft aig input).aig.decls[idx] = aig.decls[idx] := by
  intros
  unfold blastShiftLeft
  grind

instance : AIG.LawfulVecOperator α AIG.ArbitraryShiftTarget blastShiftLeft where
  le_size := blastShiftLeft_le_size
  decl_eq := blastShiftLeft_decl_eq

end bitblast
end BVExpr

end Std.Tactic.BVDecide
