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
This module contains the implementation of a bitblaster for `BitVec.extract`.
-/

namespace Std.Tactic.BVDecide

open Std.Sat

namespace BVExpr
namespace bitblast

variable [Hashable α] [DecidableEq α]

structure ExtractTarget (aig : AIG α) (len : Nat) where
  {w : Nat}
  vec : AIG.RefVec aig w
  start : Nat

def blastExtract (aig : AIG α) (target : ExtractTarget aig newWidth) :
    AIG.RefVecEntry α newWidth :=
  let ⟨input, start⟩ := target
  ⟨aig, go input start 0 (by omega) (.emptyWithCapacity newWidth)⟩
where
  go {aig : AIG α} {w : Nat} (input : AIG.RefVec aig w) (start : Nat) (curr : Nat)
      (hcurr : curr ≤ newWidth) (s : AIG.RefVec aig curr) :
      AIG.RefVec aig newWidth :=
  if h : curr < newWidth then
    let falseRef := aig.mkConstCached false
    let nextRef := input.getD (start + curr) falseRef
    let s := s.push nextRef
    go input start (curr + 1) (by omega) s
  else
    have : curr = newWidth := by omega
    this ▸ s
termination_by newWidth - curr

@[grind! .]
theorem blastExtract_le_size (aig : AIG α) (input : ExtractTarget aig w) :
    aig.decls.size ≤ (blastExtract aig input).aig.decls.size := by
  intros
  unfold blastExtract
  simp

@[grind =]
theorem blastExtract_decl_eq (aig : AIG α) (input : ExtractTarget aig w) (idx : Nat)
    (h1 : idx < aig.decls.size) (h2 : idx < (blastExtract aig input).aig.decls.size) :
    (blastExtract aig input).aig.decls[idx] = aig.decls[idx]'h1 := by
  intros
  unfold blastExtract
  simp

instance : AIG.LawfulVecOperator α ExtractTarget blastExtract where
  le_size := blastExtract_le_size
  decl_eq := blastExtract_decl_eq

end bitblast
end BVExpr

end Std.Tactic.BVDecide
