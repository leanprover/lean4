/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Std.Sat.AIG.CachedGatesLemmas
import Std.Sat.AIG.RefVec

/-!
This module contains the implementation of a bitblaster for `BitVec.getLsbD`.
-/

namespace Std.Tactic.BVDecide

open Std.Sat

namespace BVPred

variable [Hashable α] [DecidableEq α]

structure GetLsbDTarget (aig : AIG α) where
  {w : Nat}
  vec : AIG.RefVec aig w
  idx : Nat

def blastGetLsbD (aig : AIG α) (target : GetLsbDTarget aig) : AIG.Entrypoint α :=
  if h : target.idx < target.w then
    ⟨aig, target.vec.get target.idx h⟩
  else
    AIG.mkConstCached aig false

instance : AIG.LawfulOperator α GetLsbDTarget blastGetLsbD where
  le_size := by
    intros
    unfold blastGetLsbD
    split
    · simp
    · apply AIG.LawfulOperator.le_size (f := AIG.mkConstCached)
  decl_eq := by
    intros
    unfold blastGetLsbD
    split
    · simp
    · rw [AIG.LawfulOperator.decl_eq (f := AIG.mkConstCached)]

end BVPred

end Std.Tactic.BVDecide
