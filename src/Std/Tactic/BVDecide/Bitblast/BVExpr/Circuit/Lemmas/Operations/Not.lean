/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Basic
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Not

/-!
This module contains the verification of the bitblaster for `BitVec.not` from `Impl.Operations.Not`.
-/

namespace Std.Tactic.BVDecide

open Std.Sat
open Std.Sat.AIG

namespace BVExpr
namespace bitblast

variable [Hashable α] [DecidableEq α]

@[simp]
theorem denote_blastNot (aig : AIG α) (target : RefVec aig w)
    (assign : α → Bool) :
    ∀ (idx : Nat) (hidx : idx < w),
        ⟦(blastNot aig target).aig, (blastNot aig target).vec.get idx hidx, assign⟧
          =
        !⟦aig, target.get idx hidx, assign⟧ := by
  intro idx hidx
  unfold blastNot
  simp

end bitblast
end BVExpr

end Std.Tactic.BVDecide
