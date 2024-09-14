/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Basic
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.ZeroExtend

/-!
This module contains the verification of the bitblaster `BitVec.zeroExtend` from `Impl.Operations.ZeroExtend`.
-/

namespace Std.Tactic.BVDecide

open Std.Sat
open Std.Sat.AIG

namespace BVExpr
namespace bitblast

variable [Hashable α] [DecidableEq α]

namespace blastZeroExtend

theorem go_get_aux (aig : AIG α) (w : Nat) (input : AIG.RefVec aig w) (newWidth curr : Nat)
    (hcurr : curr ≤ newWidth) (s : AIG.RefVec aig curr) :
    ∀ (idx : Nat) (hidx : idx < curr) (hfoo),
        (go aig w input newWidth curr hcurr s).vec.get idx (by omega)
          =
        (s.get idx hidx).cast hfoo := by
  intro idx hidx
  generalize hgo : go aig w input newWidth curr hcurr s = res
  unfold go at hgo
  split at hgo
  · dsimp only at hgo
    split at hgo
    · rw [← hgo]
      intros
      rw [go_get_aux]
      rw [AIG.RefVec.get_push_ref_lt]
    · rw [← hgo]
      intros
      rw [go_get_aux]
      rw [AIG.RefVec.get_push_ref_lt]
      · simp only [Ref.cast, Ref.mk.injEq]
        rw [AIG.RefVec.get_cast]
        · simp
        · assumption
      · apply go_le_size
  · dsimp only at hgo
    rw [← hgo]
    simp only [Nat.le_refl, get, Ref.gate_cast, Ref.mk.injEq, true_implies]
    have : curr = newWidth := by omega
    subst this
    simp
termination_by newWidth - curr

theorem go_get (aig : AIG α) (w : Nat) (input : AIG.RefVec aig w) (newWidth curr : Nat)
    (hcurr : curr ≤ newWidth) (s : AIG.RefVec aig curr) :
    ∀ (idx : Nat) (hidx : idx < curr),
        (go aig w input newWidth curr hcurr s).vec.get idx (by omega)
          =
        (s.get idx hidx).cast (by apply go_le_size) := by
  intros
  apply go_get_aux

theorem go_denote_mem_prefix (aig : AIG α) (w : Nat) (input : AIG.RefVec aig w) (newWidth curr : Nat)
    (hcurr : curr ≤ newWidth) (s : AIG.RefVec aig curr) (start : Nat) (hstart) :
    ⟦
      (go aig w input newWidth curr hcurr s).aig,
      ⟨start, by apply Nat.lt_of_lt_of_le; exact hstart; apply go_le_size⟩,
      assign
    ⟧
      =
    ⟦aig, ⟨start, hstart⟩, assign⟧ := by
  apply denote.eq_of_isPrefix (entry := ⟨aig, start,hstart⟩)
  apply IsPrefix.of
  · intros
    apply go_decl_eq
  · intros
    apply go_le_size

theorem go_denote_eq (aig : AIG α) (w : Nat) (input : AIG.RefVec aig w) (newWidth curr : Nat)
    (hcurr : curr ≤ newWidth) (s : AIG.RefVec aig curr) (assign : α → Bool) :
    ∀ (idx : Nat) (hidx1 : idx < newWidth),
        curr ≤ idx
          →
        ⟦
          (go aig w input newWidth curr hcurr s).aig,
          (go aig w input newWidth curr hcurr s).vec.get idx hidx1,
          assign
        ⟧
          =
        if hidx : idx < w then
           ⟦aig, input.get idx hidx, assign⟧
        else
           false
    := by
  intro idx hidx1 hidx2
  generalize hgo : go aig w input newWidth curr hcurr s = res
  unfold go at hgo
  split at hgo
  · dsimp only at hgo
    cases Nat.eq_or_lt_of_le hidx2 with
    | inl heq =>
      split at hgo
      · next hsplit =>
        rw [heq] at hsplit
        simp only [hsplit, ↓reduceDIte]
        rw [← hgo]
        rw [go_get]
        rw [AIG.RefVec.get_push_ref_eq']
        · rw [go_denote_mem_prefix]
          · simp [heq]
          · simp [Ref.hgate]
        · omega
      · next hsplit =>
        rw [heq] at hsplit
        simp only [hsplit, ↓reduceDIte]
        rw [← hgo]
        rw [go_get]
        rw [AIG.RefVec.get_push_ref_eq']
        · rw [go_denote_mem_prefix]
          · simp [heq]
          · simp [Ref.hgate]
        · omega
    | inr =>
      split at hgo
      · rw [← hgo]
        rw [go_denote_eq]
        omega
      · rw [← hgo]
        rw [go_denote_eq]
        · split
          · omega
          · rfl
        · omega
  · omega
termination_by newWidth - curr

end blastZeroExtend

@[simp]
theorem denote_blastZeroExtend (aig : AIG α) (target : ExtendTarget aig newWidth)
    (assign : α → Bool) :
    ∀ (idx : Nat) (hidx : idx < newWidth),
        ⟦(blastZeroExtend aig target).aig, (blastZeroExtend aig target).vec.get idx hidx, assign⟧
          =
        if hidx : idx < target.w then
           ⟦aig, target.vec.get idx hidx, assign⟧
        else
           false
    := by
  intro idx hidx
  unfold blastZeroExtend
  apply blastZeroExtend.go_denote_eq
  omega

end bitblast
end BVExpr

end Std.Tactic.BVDecide
