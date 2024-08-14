/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Lean.Elab.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Basic
import Lean.Elab.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.GetLsb

/-!
This module contains the verification of the `BitVec.getLsb` bitblaster from `Impl.Extract`.
-/

namespace Lean.Elab.Tactic.BVDecide

open Std.Sat
open Std.Sat.AIG

namespace BVPred

variable [Hashable α] [DecidableEq α]

@[simp]
theorem denote_blastGetLsb (aig : AIG α) (target : GetLsbTarget aig)
    (assign : α → Bool) :
    ⟦blastGetLsb aig target, assign⟧
      =
    if h : target.idx < target.w then
      ⟦aig, target.vec.get target.idx h, assign⟧
    else
      false := by
  rcases target with ⟨expr, idx⟩
  unfold blastGetLsb
  dsimp only
  split <;> simp

end BVPred

end Lean.Elab.Tactic.BVDecide
