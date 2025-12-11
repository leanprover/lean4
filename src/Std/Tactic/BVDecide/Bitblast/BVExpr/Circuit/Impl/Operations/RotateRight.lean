/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Basic
public import Std.Sat.AIG.LawfulVecOperator

@[expose] public section

/-!
This module contains the implementation of a bitblaster for `BitVec.rotateRight`. Note that only
rotating with a known rotation distance is supported because `rotateRight` takes a `Nat` as distance.
-/

namespace Std.Tactic.BVDecide

open Std.Sat

namespace BVExpr
namespace bitblast

variable [Hashable α] [DecidableEq α]

def blastRotateRight (aig : AIG α) (target : AIG.ShiftTarget aig w) :
    AIG.RefVecEntry α w :=
  let ⟨input, distance⟩ := target
  ⟨aig, go input distance 0 (by omega) (.emptyWithCapacity w)⟩
where
  go {aig : AIG α} (input : AIG.RefVec aig w) (distance : Nat) (curr : Nat) (hcurr : curr ≤ w)
      (s : AIG.RefVec aig curr) :
      AIG.RefVec aig w :=
  if hcurr1 : curr < w then
    if hcurr2 : curr < w - distance % w then
      let ref := input.get ((distance % w) + curr) (by omega)
      let s := s.push ref
      go input distance (curr + 1) (by omega) s
    else
      let ref := input.get (curr - (w - (distance % w))) (by omega)
      let s := s.push ref
      go input distance (curr + 1) (by omega) s
  else
    have hcurr : curr = w := by omega
    hcurr ▸ s
termination_by w - curr

@[grind! .]
theorem blastRotateRight_le_size (aig : AIG α) (input : aig.ShiftTarget w) :
    aig.decls.size ≤ (blastRotateRight aig input).aig.decls.size := by
  intros
  unfold blastRotateRight
  dsimp only
  omega

@[grind =]
theorem blastRotateRight_decl_eq (aig : AIG α) (input : aig.ShiftTarget w) (idx : Nat)
    (h1 : idx < aig.decls.size) (h2 : idx < (blastRotateRight aig input).aig.decls.size) :
    (blastRotateRight aig input).aig.decls[idx] = aig.decls[idx]'h1 := by
  intros
  unfold blastRotateRight
  dsimp only

instance : AIG.LawfulVecOperator α AIG.ShiftTarget blastRotateRight where
  le_size := blastRotateRight_le_size
  decl_eq := blastRotateRight_decl_eq

end bitblast
end BVExpr

end Std.Tactic.BVDecide
