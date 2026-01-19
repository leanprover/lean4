/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Basic
public import Std.Sat.AIG.RefVecOperator
import Init.Grind

@[expose] public section

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

@[grind! .]
theorem blastNot_le_size (aig : AIG α) (input : aig.RefVec w) :
    aig.decls.size ≤ (blastNot aig input).aig.decls.size := by
  intros
  unfold blastNot
  grind

@[grind =]
theorem blastNot_decl_eq (aig : AIG α) (input : aig.RefVec w) (idx : Nat)
    (h1 : idx < aig.decls.size) (h2 : idx < (blastNot aig input).aig.decls.size) :
    (blastNot aig input).aig.decls[idx] = aig.decls[idx] := by
  intros
  unfold blastNot
  grind

instance : AIG.LawfulVecOperator α AIG.RefVec blastNot where
  le_size := blastNot_le_size
  decl_eq := blastNot_decl_eq

end bitblast
end BVExpr

end Std.Tactic.BVDecide
