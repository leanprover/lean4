/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Basic
public import Std.Sat.AIG.LawfulVecOperator
import Init.Data.Int.Lemmas
import Init.Data.Int.Order
import Init.Data.Nat.Order
import Init.Data.Order.Lemmas
import Init.Omega

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

instance : AIG.LawfulVecOperator α ExtractTarget blastExtract where
  le_size := by
    intros
    unfold blastExtract
    simp
  decl_eq := by
    intros
    unfold blastExtract
    simp

end bitblast
end BVExpr

end Std.Tactic.BVDecide
