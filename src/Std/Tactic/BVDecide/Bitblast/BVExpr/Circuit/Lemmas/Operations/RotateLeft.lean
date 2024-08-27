/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Basic
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.RotateLeft

/-!
This module contains the verification of the bitblaster for `BitVec.rotateLeft` from
`Impl.Operations.RotateLeft`.
-/

namespace Std.Tactic.BVDecide

open Std.Sat
open Std.Sat.AIG

namespace BVExpr
namespace bitblast

variable [Hashable α] [DecidableEq α]

namespace blastRotateLeft

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
    obtain rfl : curr = w := by omega
    simp
termination_by w - curr

theorem go_get (aig : AIG α) (distance : Nat) (input : AIG.RefVec aig w)
    (curr : Nat) (hcurr : curr ≤ w) (s : AIG.RefVec aig curr) :
    ∀ (idx : Nat) (hidx1 : idx < w),
        curr ≤ idx
          →
        (go input distance curr hcurr s).get idx hidx1
          =
        if hidx3 : idx < distance % w then
          input.get (w - (distance % w) + idx) (by omega)
        else
          input.get (idx - (distance % w)) (by omega)
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

end blastRotateLeft

@[simp]
theorem denote_blastRotateLeft (aig : AIG α) (target : ShiftTarget aig w)
    (assign : α → Bool) :
    ∀ (idx : Nat) (hidx : idx < w),
        ⟦
          (blastRotateLeft aig target).aig,
          (blastRotateLeft aig target).vec.get idx hidx,
          assign
        ⟧
          =
        if hidx2 : idx < target.distance % w then
          ⟦aig, target.vec.get (w - (target.distance % w) + idx) (by omega), assign⟧
        else
          ⟦aig, target.vec.get (idx - (target.distance % w)) (by omega), assign⟧
      := by
  intros
  unfold blastRotateLeft
  dsimp only
  rw [blastRotateLeft.go_get]
  · split
    · rfl
    · rfl
  · omega

end bitblast
end BVExpr

end Std.Tactic.BVDecide
