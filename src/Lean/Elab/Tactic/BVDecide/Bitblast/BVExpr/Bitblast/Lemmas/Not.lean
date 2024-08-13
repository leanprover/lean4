/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Lean.Elab.Tactic.BVDecide.Bitblast.BVExpr.Bitblast.Lemmas.Basic
import Lean.Elab.Tactic.BVDecide.Bitblast.BVExpr.Bitblast.Impl.Not

/-!
This module contains the verification of the bitblaster for `BitVec.not` from `Impl.Not`.
-/

namespace Lean.Elab.Tactic.BVDecide

open Std.Sat
open Std.Sat.AIG

namespace BVExpr
namespace bitblast

variable [Hashable α] [DecidableEq α]

@[simp]
theorem blastNot_denote_eq (aig : AIG α) (target : RefVec aig w)
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

end Lean.Elab.Tactic.BVDecide
