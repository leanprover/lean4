/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Basic
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Const
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Neg
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Not
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Add

/-!
This module contains the verification of the bitblaster for `BitVec.neg` from `Impl.Operations.Neg`.
-/

namespace Std.Tactic.BVDecide

open Std.Sat
open Std.Sat.AIG

namespace BVExpr
namespace bitblast

variable [Hashable α] [DecidableEq α]

theorem denote_blastNeg (aig : AIG α) (value : BitVec w) (target : RefVec aig w)
    (assign : α → Bool)
    (htarget : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, target.get idx hidx, assign⟧ = value.getLsbD idx) :

    ∀ (idx : Nat) (hidx : idx < w),
        ⟦(blastNeg aig target).aig, (blastNeg aig target).vec.get idx hidx, assign⟧
          =
        (-value).getLsbD idx := by
  intro idx hidx
  rw [BitVec.neg_eq_not_add]
  unfold blastNeg
  dsimp only
  rw [denote_blastAdd]
  · intro idx hidx
    rw [AIG.LawfulVecOperator.denote_mem_prefix (f := blastConst)]
    · simp only [RefVec.get_cast, Ref.gate_cast, BitVec.getLsbD_not, hidx, decide_true,
        Bool.true_and]
      rw [denote_blastNot, htarget]
    · simp [Ref.hgate]
  · simp

end bitblast
end BVExpr

end Std.Tactic.BVDecide
