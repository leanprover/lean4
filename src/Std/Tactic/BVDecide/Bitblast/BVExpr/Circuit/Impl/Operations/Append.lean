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
This module contains the implementation of a bitblaster for `BitVec.append`.
-/

namespace Std.Tactic.BVDecide

open Std.Sat

namespace BVExpr
namespace bitblast

variable [Hashable α] [DecidableEq α]

structure AppendTarget (aig : AIG α) (combined : Nat) where
  {lw : Nat}
  {rw : Nat}
  lhs : AIG.RefVec aig lw
  rhs : AIG.RefVec aig rw
  h : combined = rw + lw

def blastAppend (aig : AIG α) (target : AppendTarget aig newWidth) :
    AIG.RefVecEntry α newWidth :=
  let ⟨lhs, rhs, h⟩ := target
  let combined := rhs.append lhs
  ⟨aig, h ▸ combined⟩

@[grind! .]
theorem blastAppend_le_size (aig : AIG α) (input : AppendTarget aig w) :
    aig.decls.size ≤ (blastAppend aig input).aig.decls.size := by
  simp [blastAppend]

@[grind =]
theorem blastAppend_decl_eq (aig : AIG α) (input : AppendTarget aig w) (idx : Nat)
    (h1 : idx < aig.decls.size) (h2 : idx < (blastAppend aig input).aig.decls.size) :
    (blastAppend aig input).aig.decls[idx] = aig.decls[idx]'h1 := by
  simp [blastAppend]

instance : AIG.LawfulVecOperator α AppendTarget blastAppend where
  le_size := blastAppend_le_size
  decl_eq := blastAppend_decl_eq

end bitblast
end BVExpr

end Std.Tactic.BVDecide
