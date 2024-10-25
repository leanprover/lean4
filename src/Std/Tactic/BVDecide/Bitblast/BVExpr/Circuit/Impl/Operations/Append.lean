/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Std.Tactic.BVDecide.Bitblast.BVExpr.Basic
import Std.Sat.AIG.LawfulVecOperator

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

instance : AIG.LawfulVecOperator α AppendTarget blastAppend where
  le_size := by simp [blastAppend]
  decl_eq := by simp [blastAppend]

end bitblast
end BVExpr

end Std.Tactic.BVDecide
