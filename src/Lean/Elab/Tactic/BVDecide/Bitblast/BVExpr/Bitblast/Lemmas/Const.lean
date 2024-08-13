/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Lean.Elab.Tactic.BVDecide.Bitblast.BVExpr.Bitblast.Lemmas.Basic
import Lean.Elab.Tactic.BVDecide.Bitblast.BVExpr.Bitblast.Impl.Const

/-!
This module contains the verification of the `BitVec` constant bitblaster from `Impl.Const`.
-/

namespace Lean.Elab.Tactic.BVDecide

open Std.Sat
open Std.Sat.AIG

namespace BVExpr
namespace bitblast

variable [Hashable α] [DecidableEq α]

namespace blastConst

theorem go_get_aux (aig : AIG α) (c : BitVec w) (curr : Nat) (hcurr : curr ≤ w)
    (s : AIG.RefVec aig curr) :
    -- `hfoo` makes it possible to `generalize` below. With a concrete proof term this
    -- `generalize` would produce a type incorrect term as the proof term would talk about
    -- a `go` application instead of the fresh variable.
    ∀ (idx : Nat) (hidx : idx < curr) (hfoo),
        (go aig c curr s hcurr).vec.get idx (by omega) = (s.get idx hidx).cast hfoo := by
  intro idx hidx
  generalize hgo : go aig c curr s hcurr = res
  unfold go at hgo
  split at hgo
  . dsimp only at hgo
    rw [← hgo]
    intro hfoo
    rw [go_get_aux]
    rw [AIG.RefVec.get_push_ref_lt]
    . simp only [Ref.cast, Ref.mk.injEq]
      rw [AIG.RefVec.get_cast]
      . simp
      . assumption
    . apply go_le_size
  . dsimp only at hgo
    rw [← hgo]
    simp only [Nat.le_refl, get, Ref.gate_cast, Ref.mk.injEq, true_implies]
    have : curr = w := by omega
    subst this
    simp
termination_by w - curr

theorem go_get (aig : AIG α) (c : BitVec w)
    (curr : Nat) (hcurr : curr ≤ w) (s : AIG.RefVec aig curr) :
    ∀ (idx : Nat) (hidx : idx < curr),
        (go aig c curr s hcurr).vec.get idx (by omega)
          =
        (s.get idx hidx).cast (by apply go_le_size) := by
  intros
  apply go_get_aux

theorem go_denote_mem_prefix (aig : AIG α) (idx : Nat) (hidx)
    (s : AIG.RefVec aig idx) (c : BitVec w) (start : Nat) (hstart) :
    ⟦
      (go aig c idx s hidx).aig,
      ⟨start, by apply Nat.lt_of_lt_of_le; exact hstart; apply go_le_size⟩,
      assign
    ⟧
      =
    ⟦aig, ⟨start, hstart⟩, assign⟧ := by
  apply denote.eq_of_isPrefix (entry := ⟨aig, start,hstart⟩)
  apply IsPrefix.of
  . intros
    apply go_decl_eq
  . intros
    apply go_le_size

theorem go_denote_eq (aig : AIG α) (c : BitVec w) (assign : α → Bool)
    (curr : Nat) (hcurr : curr ≤ w) (s : AIG.RefVec aig curr) :
    ∀ (idx : Nat) (hidx1 : idx < w),
        curr ≤ idx
          →
        ⟦
          (go aig c curr s hcurr).aig,
          (go aig c curr s hcurr).vec.get idx hidx1,
          assign
        ⟧
          =
        c.getLsb idx := by
  intro idx hidx1 hidx2
  generalize hgo : go aig c curr s hcurr = res
  unfold go at hgo
  split at hgo
  . dsimp only at hgo
    cases Nat.eq_or_lt_of_le hidx2 with
    | inl heq =>
      rw [← hgo]
      rw [go_get]
      rw [AIG.RefVec.get_push_ref_eq']
      . rw [← heq]
        rw [go_denote_mem_prefix]
        . simp
        . simp [Ref.hgate]
      . rw [heq]
    | inr =>
      rw [← hgo]
      rw [go_denote_eq]
      omega
  . omega
termination_by w - curr

end blastConst

@[simp]
theorem blastConst_denote_eq (aig : AIG α) (c : BitVec w) (assign : α → Bool) :
    ∀ (idx : Nat) (hidx : idx < w),
        ⟦(blastConst aig c).aig, (blastConst aig c).vec.get idx hidx, assign⟧
          =
        c.getLsb idx := by
  intros
  apply blastConst.go_denote_eq
  omega

end bitblast
end BVExpr

end Lean.Elab.Tactic.BVDecide
