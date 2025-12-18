/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Std.Sat.AIG.RefVec

@[expose] public section

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

def blastGetLsbD (aig : AIG α) (target : GetLsbDTarget aig) : AIG.Ref aig :=
  if h : target.idx < target.w then
    target.vec.get target.idx h
  else
    aig.mkConstCached false

end BVPred

end Std.Tactic.BVDecide
