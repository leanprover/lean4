/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Basic
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.ZeroExtend
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.SignExtend

/-!
This module contains the verification of the bitblaster for `BitVec.signExtend` from
`Impl.Operations.SignExtend`.
-/

namespace Std.Tactic.BVDecide

open Std.Sat
open Std.Sat.AIG

namespace BVExpr
namespace bitblast

variable [Hashable α] [DecidableEq α]

namespace blastSignExtend

theorem go_get_aux (aig : AIG α) (w : Nat) (hw : 0 < w) (input : RefVec aig w) (newWidth : Nat)
    (curr : Nat) (hcurr : curr ≤ newWidth) (s : RefVec aig curr) :
    ∀ (idx : Nat) (hidx1 : idx < curr),
        (go w hw input newWidth curr hcurr s).get idx (by omega)
          =
        s.get idx hidx1 := by
  intro idx hidx
  unfold go
  split
  · dsimp only
    split
    all_goals
      rw [go_get_aux]
      rw [AIG.RefVec.get_push_ref_lt]
  · dsimp only
    simp only [RefVec.get, Ref.mk.injEq]
    have : curr = newWidth := by omega
    subst this
    simp

theorem go_get (aig : AIG α) (w : Nat) (hw : 0 < w) (input : RefVec aig w) (newWidth : Nat)
    (curr : Nat) (hcurr : curr ≤ newWidth) (s : RefVec aig curr) :
    ∀ (idx : Nat) (hidx1 : idx < newWidth),
        curr ≤ idx
          →
        (go w hw input newWidth curr hcurr s).get idx hidx1
          =
        if hidx2 : idx < w then
          input.get idx (by omega)
        else
          input.get (w - 1) (by omega)
    := by
  intro idx hidx1 hcurr
  unfold go
  have : curr < newWidth := by omega
  simp only [this, ↓reduceDIte]
  cases Nat.eq_or_lt_of_le hcurr with
  | inl heq =>
    simp only [heq]
    split
    all_goals
      rw [go_get_aux]
      rw [AIG.RefVec.get_push_ref_eq']
      rw [heq]
  | inr heq =>
    split
    all_goals
      rw [go_get]
      omega

end blastSignExtend

theorem blastSignExtend_empty_eq_zeroExtend (aig : AIG α) (target : ExtendTarget aig newWidth)
    (htarget : target.w = 0) :
    blastSignExtend aig target = blastZeroExtend aig target := by
  unfold blastSignExtend
  simp [htarget]

theorem denote_blastSignExtend (aig : AIG α) (target : ExtendTarget aig newWidth)
    (assign : α → Bool) (htarget : 0 < target.w) :
    ∀ (idx : Nat) (hidx : idx < newWidth),
        ⟦(blastSignExtend aig target).aig, (blastSignExtend aig target).vec.get idx hidx, assign⟧
          =
        if hidx : idx < target.w then
           ⟦aig, target.vec.get idx hidx, assign⟧
        else
           ⟦aig, target.vec.get (target.w - 1) (by omega), assign⟧
    := by
  intro idx hidx
  generalize hg : blastSignExtend aig target = res
  unfold blastSignExtend at hg
  dsimp only at hg
  have : ¬ (target.w = 0) := by omega
  simp only [this, ↓reduceDIte] at hg
  rw [← hg]
  dsimp only
  rw [blastSignExtend.go_get]
  · split <;> simp only
  · omega

end bitblast
end BVExpr

end Std.Tactic.BVDecide
