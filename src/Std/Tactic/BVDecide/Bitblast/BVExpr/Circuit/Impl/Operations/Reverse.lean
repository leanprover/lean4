/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Basic
public import Std.Sat.AIG.LawfulVecOperator

@[expose] public section

set_option debug.byAsSorry true  -- TODO: remove after bootstrap

/-!
This module contains the implementation of a bitblaster for `BitVec.reverse`.
-/

namespace Std.Tactic.BVDecide

open Std.Sat

namespace BVExpr
namespace bitblast

variable [Hashable α] [DecidableEq α]

def blastReverse (aig : AIG α) (s : AIG.RefVec aig w) : AIG.RefVecEntry α w :=
  let ⟨refs, hrefs⟩ := s
  ⟨aig, ⟨refs.reverse, by simp [hrefs]⟩⟩

instance : AIG.LawfulVecOperator α AIG.RefVec blastReverse where
  le_size := by simp [blastReverse]
  decl_eq := by simp [blastReverse]

end bitblast
end BVExpr

end Std.Tactic.BVDecide
