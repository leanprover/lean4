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
import Init.Omega

@[expose] public section

/-!
This module contains the implementation of a bitblaster for `BitVec` constants.
-/

namespace Std.Tactic.BVDecide

open Std.Sat

namespace BVExpr
namespace bitblast

variable [Hashable α] [DecidableEq α]

def blastConst (aig : AIG α) (val : BitVec w) : AIG.RefVec aig w :=
  go aig val 0 (.emptyWithCapacity w) (by omega)
where
  go (aig : AIG α) (val : BitVec w) (curr : Nat) (s : AIG.RefVec aig curr) (hcurr : curr ≤ w) :
      AIG.RefVec aig w :=
    if hcurr : curr < w then
      let bitRef := aig.mkConstCached (val.getLsbD curr)
      let s := s.push bitRef
      go aig val (curr + 1) s (by omega)
    else
      have hcurr : curr = w := by omega
      hcurr ▸ s
  termination_by w - curr

end bitblast
end BVExpr

end Std.Tactic.BVDecide
