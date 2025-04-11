/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Basic
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Neg
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Sub

/-!
This module contains the verification of the bitblaster for `BitVec.sub` from `Impl.Operations.Sub`.
-/

namespace Std.Tactic.BVDecide

open Std.Sat
open Std.Sat.AIG

namespace BVExpr
namespace bitblast

variable [Hashable α] [DecidableEq α]

theorem denote_blastSub (aig : AIG α) (lhs rhs : BitVec w) (assign : α → Bool)
      (input : BinaryRefVec aig w)
      (hleft : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, input.lhs.get idx hidx, assign⟧ = lhs.getLsbD idx)
      (hright : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, input.rhs.get idx hidx, assign⟧ = rhs.getLsbD idx) :
      ∀ (idx : Nat) (hidx : idx < w),
          ⟦(blastSub aig input).aig, (blastSub aig input).vec.get idx hidx, assign⟧
            =
          (lhs - rhs).getLsbD idx := by
  intro idx hidx
  rw [BitVec.sub_eq_add_neg]
  unfold blastSub
  rw [denote_blastAdd]
  · intros
    rw [AIG.LawfulVecOperator.denote_mem_prefix (f := blastNeg)]
    · simp [hleft]
    · simp [Ref.hgate]
  · intros
    rw [denote_blastNeg]
    exact hright

end bitblast
end BVExpr

end Std.Tactic.BVDecide
