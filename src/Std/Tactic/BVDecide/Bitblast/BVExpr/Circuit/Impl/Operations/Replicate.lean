/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Std.Tactic.BVDecide.Bitblast.BVExpr.Basic
import Std.Sat.AIG.LawfulVecOperator

/-!
This module contains the implementation of a bitblaster for `BitVec.replicate`.
-/

namespace Std.Tactic.BVDecide

open Std.Sat

namespace BVExpr
namespace bitblast

variable [Hashable α] [DecidableEq α]

structure ReplicateTarget (aig : AIG α) (combined : Nat) where
  {w : Nat}
  n : Nat
  inner : AIG.RefVec aig w
  h : combined = w * n

def blastReplicate (aig : AIG α) (target : ReplicateTarget aig newWidth) :
    AIG.RefVecEntry α newWidth :=
  let ⟨n, inner, h⟩ := target
  let ref := go n inner 0 (by omega) .empty
  ⟨aig, h ▸ ref⟩
where
  go {aig : AIG α} {w : Nat} (n : Nat) (input : AIG.RefVec aig w) (curr : Nat) (hcurr : curr ≤ n)
      (s : AIG.RefVec aig (w * curr)) : AIG.RefVec aig (w * n) :=
    if h : curr < n then
      let s := s.append input
      go n input (curr + 1) (by omega) s
    else
      have : curr = n := by omega
      this ▸ s
  termination_by n - curr

instance : AIG.LawfulVecOperator α ReplicateTarget blastReplicate where
  le_size := by simp [blastReplicate]
  decl_eq := by simp [blastReplicate]

end bitblast
end BVExpr

end Std.Tactic.BVDecide
