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

@[grind! .]
theorem blastReverse_le_size (aig : AIG α) (input : aig.RefVec w) :
    aig.decls.size ≤ (blastReverse aig input).aig.decls.size := by
  simp [blastReverse]

@[grind =]
theorem blastReverse_decl_eq (aig : AIG α) (input : aig.RefVec w) (idx : Nat)
    (h1 : idx < aig.decls.size) (h2 : idx < (blastReverse aig input).aig.decls.size) :
    (blastReverse aig input).aig.decls[idx] = aig.decls[idx]'h1 := by
  simp [blastReverse]

instance : AIG.LawfulVecOperator α AIG.RefVec blastReverse where
  le_size := blastReverse_le_size
  decl_eq := blastReverse_decl_eq

end bitblast
end BVExpr

end Std.Tactic.BVDecide
