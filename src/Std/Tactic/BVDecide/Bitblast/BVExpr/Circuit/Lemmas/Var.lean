/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Basic
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Var

/-!
This module contains the verification of the bitblaster for symbolic `BitVec` values from
`Impl.Var`.
-/

namespace Std.Tactic.BVDecide

open Std.Sat
open Std.Sat.AIG

namespace BVExpr
namespace bitblast
namespace blastVar

theorem go_get_aux (aig : AIG BVBit) (a : Nat) (curr : Nat) (hcurr : curr ≤ w)
    (s : AIG.RefVec aig curr) :
    -- `hfoo` makes it possible to `generalize` below. With a concrete proof term this
    -- `generalize` would produce a type incorrect term as the proof term would talk about
    -- a `go` application instead of the fresh variable.
    ∀ (idx : Nat) (hidx : idx < curr) (hfoo),
        (go aig w a curr s hcurr).vec.get idx (by omega) = (s.get idx hidx).cast hfoo := by
  intro idx hidx
  generalize hgo : go aig w a curr s hcurr = res
  unfold go at hgo
  split at hgo
  · dsimp only at hgo
    rw [← hgo]
    intro hfoo
    rw [go_get_aux]
    rw [AIG.RefVec.get_push_ref_lt]
    · simp only [Ref.cast, Ref.mk.injEq]
      rw [AIG.RefVec.get_cast]
      · simp
      · assumption
    · apply go_le_size
  · dsimp only at hgo
    rw [← hgo]
    simp only [Nat.le_refl]
    obtain rfl : curr = w := by omega
    simp
termination_by w - curr

theorem go_get (aig : AIG BVBit) (a : Nat) (curr : Nat) (hcurr : curr ≤ w)
    (s : AIG.RefVec aig curr) :
    ∀ (idx : Nat) (hidx : idx < curr),
        (go aig w a curr s hcurr).vec.get idx (by omega)
          =
        (s.get idx hidx).cast (by apply go_le_size) := by
  intros
  apply go_get_aux

theorem go_denote_mem_prefix (aig : AIG BVBit) (idx : Nat) (hidx) (s : AIG.RefVec aig idx)
    (a : Nat) (start : Nat) (hstart) :
    ⟦
      (go aig w a idx s hidx).aig,
      ⟨start, inv, by apply Nat.lt_of_lt_of_le; exact hstart; apply go_le_size⟩,
      assign
    ⟧
      =
    ⟦aig, ⟨start, inv, hstart⟩, assign⟧ := by
  apply denote.eq_of_isPrefix (entry := ⟨aig, start, inv, hstart⟩)
  apply IsPrefix.of
  · intros
    apply go_decl_eq
  · intros
    apply go_le_size

theorem go_denote_eq (aig : AIG BVBit) (a : Nat) (assign : Assignment) (curr : Nat)
    (hcurr : curr ≤ w) (s : AIG.RefVec aig curr) :
    ∀ (idx : Nat) (hidx1 : idx < w),
        curr ≤ idx
          →
        ⟦
          (go aig w a curr s hcurr).aig,
          (go aig w a curr s hcurr).vec.get idx hidx1,
          assign.toAIGAssignment
        ⟧
          =
        ((BVExpr.var (w := w) a).eval assign).getLsbD idx := by
  intro idx hidx1 hidx2
  generalize hgo : go aig w a curr s hcurr = res
  unfold go at hgo
  split at hgo
  · next hlt =>
    dsimp only at hgo
    cases Nat.eq_or_lt_of_le hidx2 with
    | inl heq =>
      rw [← hgo]
      rw [go_get]
      rw [AIG.RefVec.get_push_ref_eq']
      · rw [← heq]
        rw [go_denote_mem_prefix]
        · simp [hlt]
        · simp [Ref.hgate]
      · rw [heq]
    | inr =>
      rw [← hgo]
      simp only [eval_var]
      rw [go_denote_eq]
      · simp
      · omega
  · omega
termination_by w - curr

end blastVar

@[simp]
theorem denote_blastVar (aig : AIG BVBit) (var : BVVar w) (assign : Assignment) :
    ∀ (idx : Nat) (hidx : idx < w),
        ⟦(blastVar aig var).aig, (blastVar aig var).vec.get idx hidx, assign.toAIGAssignment⟧
          =
        ((BVExpr.var (w := w) var.ident).eval assign).getLsbD idx := by
  intros
  apply blastVar.go_denote_eq
  omega

end bitblast
end BVExpr

end Std.Tactic.BVDecide
