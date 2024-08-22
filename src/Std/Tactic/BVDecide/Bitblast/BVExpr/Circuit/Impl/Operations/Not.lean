/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Std.Tactic.BVDecide.Bitblast.BVExpr.Basic
import Std.Sat.AIG.CachedGatesLemmas
import Std.Sat.AIG.LawfulVecOperator
import Std.Sat.AIG.RefVecOperator

/-!
This module contains the implementation of a bitblaster for `BitVec.not`.
-/

namespace Std.Tactic.BVDecide

open Std.Sat

namespace BVExpr
namespace bitblast

variable [Hashable α] [DecidableEq α]

def blastNot (aig : AIG α) (s : AIG.RefVec aig w) : AIG.RefVecEntry α w :=
  AIG.RefVec.map aig ⟨s, AIG.mkNotCached⟩

instance : AIG.LawfulVecOperator α AIG.RefVec blastNot where
  le_size := by
    intros
    unfold blastNot
    apply AIG.LawfulVecOperator.le_size (f := AIG.RefVec.map)
  decl_eq := by
    intros
    unfold blastNot
    apply AIG.LawfulVecOperator.decl_eq (f := AIG.RefVec.map)

end bitblast
end BVExpr

end Std.Tactic.BVDecide
