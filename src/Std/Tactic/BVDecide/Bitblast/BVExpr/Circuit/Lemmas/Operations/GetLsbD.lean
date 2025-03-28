/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Basic
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.GetLsbD

/-!
This module contains the verification of the `BitVec.getLsb` bitblaster from `Impl.Operations.Extract`.
-/

namespace Std.Tactic.BVDecide

open Std.Sat
open Std.Sat.AIG

namespace BVPred

variable [Hashable α] [DecidableEq α]

theorem denote_getD_eq_getLsbD (aig : AIG α) (assign : α → Bool) (x : BitVec w)
    (xv : AIG.RefVec aig w) (falseRef : AIG.Ref aig)
    (hx : ∀ idx hidx, ⟦aig, xv.get idx hidx, assign⟧ = x.getLsbD idx)
    (hfalse : ⟦aig, falseRef, assign⟧ = false) :
    ∀ idx, ⟦aig, xv.getD idx falseRef, assign⟧ = x.getLsbD idx := by
  intro idx
  rw [AIG.RefVec.getD]
  split
  · rw [hx]
  · rw [hfalse]
    symm
    apply BitVec.getLsbD_of_ge
    omega

@[simp]
theorem denote_blastGetLsbD (aig : AIG α) (target : GetLsbDTarget aig) (assign : α → Bool) :
    ⟦blastGetLsbD aig target, assign⟧
      =
    if h : target.idx < target.w then
      ⟦aig, target.vec.get target.idx h, assign⟧
    else
      false := by
  rcases target with ⟨expr, idx⟩
  unfold blastGetLsbD
  dsimp only
  split <;> simp

end BVPred

end Std.Tactic.BVDecide
