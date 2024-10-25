/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Basic
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.RotateRight

/-!
This module contains the verification of the bitblaster for `BitVec.rotateRight` from
`Impl.Operations.RotateRight`.
-/

namespace Std.Tactic.BVDecide

open Std.Sat
open Std.Sat.AIG

namespace BVExpr
namespace bitblast

variable [Hashable α] [DecidableEq α]

namespace blastRotateRight

theorem go_get_aux (aig : AIG α) (distance : Nat) (input : AIG.RefVec aig w)
    (curr : Nat) (hcurr : curr ≤ w) (s : AIG.RefVec aig curr) :
    ∀ (idx : Nat) (hidx : idx < curr),
        (go input distance curr hcurr s).get idx (by omega)
          =
        s.get idx hidx := by
  intro idx hidx
  unfold go
  split
  · dsimp only
    split
    · rw [go_get_aux]
      rw [AIG.RefVec.get_push_ref_lt]
    · rw [go_get_aux]
      rw [AIG.RefVec.get_push_ref_lt]
  · dsimp only
    simp only [RefVec.get, Ref.mk.injEq]
    have : curr = w := by omega
    subst this
    simp
termination_by w - curr

theorem go_get (aig : AIG α) (distance : Nat) (input : AIG.RefVec aig w)
    (curr : Nat) (hcurr : curr ≤ w) (s : AIG.RefVec aig curr) :
    ∀ (idx : Nat) (hidx1 : idx < w),
        curr ≤ idx
          →
        (go input distance curr hcurr s).get idx hidx1
          =
        if hidx3 : idx < w - distance % w then
          input.get ((distance % w) + idx) (by omega)
        else
          input.get (idx - (w - (distance % w))) (by omega)
        := by
  intro idx hidx1 hidx2
  unfold go
  split
  · dsimp only
    cases Nat.eq_or_lt_of_le hidx2 with
    | inl heq =>
      split
      · split
        · rw [go_get_aux]
          rw [AIG.RefVec.get_push_ref_eq']
          · simp [heq]
          · omega
        · omega
      · split
        · omega
        · rw [go_get_aux]
          rw [AIG.RefVec.get_push_ref_eq']
          · simp [heq]
          · omega
    | inr heq =>
      split
      · rw [go_get]
        omega
      · rw [go_get]
        omega
  · omega
termination_by w - curr

end blastRotateRight

@[simp]
theorem denote_blastRotateRight (aig : AIG α) (target : ShiftTarget aig w)
  (assign : α → Bool) :
  ∀ (idx : Nat) (hidx : idx < w),
      ⟦
        (blastRotateRight aig target).aig,
        (blastRotateRight aig target).vec.get idx hidx,
        assign
      ⟧
        =
      if hidx2 : idx < w - target.distance % w then
        ⟦aig, target.vec.get ((target.distance % w) + idx) (by omega), assign⟧
      else
        ⟦aig, target.vec.get (idx - (w - (target.distance % w))) (by omega), assign⟧
      := by
  intros
  unfold blastRotateRight
  dsimp only
  rw [blastRotateRight.go_get]
  · split <;> simp
  · omega

end bitblast
end BVExpr

end Std.Tactic.BVDecide
