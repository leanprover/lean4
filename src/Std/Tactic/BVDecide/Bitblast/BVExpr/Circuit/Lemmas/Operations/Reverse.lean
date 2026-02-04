/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Basic
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Reverse
import Init.Data.Int.Lemmas
import Init.Data.Int.Order
import Init.Omega

@[expose] public section

/-!
This module contains the verification of the bitblaster for `BitVec.reverse` from
`Impl.Operations.Reverse`.
-/

namespace Std.Tactic.BVDecide

open Std.Sat
open Std.Sat.AIG

namespace BVExpr
namespace bitblast

variable [Hashable α] [DecidableEq α]

@[simp]
theorem denote_blastReverse (aig : AIG α) (target : RefVec aig w)
    (assign : α → Bool) :
    ∀ (idx : Nat) (hidx : idx < w),
        ⟦(blastReverse aig target).aig, (blastReverse aig target).vec.get idx hidx, assign⟧
          =
        ⟦aig, target.get (w - 1 - idx) (by omega), assign⟧ := by
  intro idx hidx
  simp [blastReverse, AIG.RefVec.get]


end bitblast
end BVExpr

end Std.Tactic.BVDecide
