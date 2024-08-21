/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Std.Tactic.BVDecide.Bitblast.BVExpr.Basic
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.ZeroExtend
import Std.Sat.AIG.CachedGatesLemmas
import Std.Sat.AIG.LawfulVecOperator

/-!
This module contains the implementation of a bitblaster for `BitVec.signExtend`.
-/

namespace Std.Tactic.BVDecide

open Std.Sat

namespace BVExpr
namespace bitblast

variable [Hashable α] [DecidableEq α]

def blastSignExtend (aig : AIG α) (target : AIG.ExtendTarget aig newWidth) :
    AIG.RefVecEntry α newWidth :=
  let ⟨width, input⟩ := target
  if hw : width = 0 then
    blastZeroExtend aig ⟨width, input⟩
  else
    ⟨aig, go width (by omega) input newWidth 0 (by omega) .empty⟩
where
  go {aig : AIG α} (w : Nat) (hw : 0 < w) (input : AIG.RefVec aig w) (newWidth : Nat)
      (curr : Nat) (hcurr : curr ≤ newWidth) (s : AIG.RefVec aig curr) :
      AIG.RefVec aig newWidth :=
    if hcurr1 : curr < newWidth then
      if hcurr2 : curr < w then
        let s := s.push (input.get curr hcurr2)
        go w hw input newWidth (curr + 1) (by omega) s
      else
        let s := s.push (input.get (w - 1) (by omega))
        go w hw input newWidth (curr + 1) (by omega) s
    else
      have hcurr : curr = newWidth := by omega
      hcurr ▸ s
termination_by newWidth - curr

instance : AIG.LawfulVecOperator α AIG.ExtendTarget blastSignExtend where
  le_size := by
    intros
    unfold blastSignExtend
    dsimp only
    split
    · apply AIG.LawfulVecOperator.le_size (f := blastZeroExtend)
    · simp
  decl_eq := by
    intros
    unfold blastSignExtend
    dsimp only
    split
    · rw [AIG.LawfulVecOperator.decl_eq (f := blastZeroExtend)]
    · simp

end bitblast
end BVExpr

end Std.Tactic.BVDecide
