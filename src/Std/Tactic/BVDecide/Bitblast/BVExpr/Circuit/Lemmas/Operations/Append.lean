/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Basic
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Append

/-!
This module contains the verification of the `BitVec.append` bitblaster from `Impl.Operations.Append`.
-/

namespace Std.Tactic.BVDecide

open Std.Sat
open Std.Sat.AIG

namespace BVExpr
namespace bitblast

variable [Hashable α] [DecidableEq α]

@[simp]
theorem denote_blastAppend (aig : AIG α) (target : AppendTarget aig newWidth)
  (assign : α → Bool) :
  ∀ (idx : Nat) (hidx : idx < newWidth),
      ⟦
        (blastAppend aig target).aig,
        (blastAppend aig target).vec.get idx hidx,
        assign
      ⟧
        =
      if hr : idx < target.rw then
         ⟦aig, target.rhs.get idx hr, assign⟧
      else
         have := target.h
         ⟦aig, target.lhs.get (idx - target.rw) (by omega), assign⟧
    := by
  intros
  unfold blastAppend
  rcases target with ⟨lw, rw, lhs, rhs, ht⟩
  dsimp only
  rw [AIG.RefVec.get_append]
  split <;> rfl


end bitblast
end BVExpr

end Std.Tactic.BVDecide
