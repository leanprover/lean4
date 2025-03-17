/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Basic
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Extract

/-!
This module contains the verification of the `BitVec.extract` bitblaster from `Impl.Operations.Extract`.
-/

namespace Std.Tactic.BVDecide

open Std.Sat
open Std.Sat.AIG

namespace BVExpr
namespace bitblast

variable [Hashable α] [DecidableEq α]

namespace blastExtract

theorem go_get_aux (aig : AIG α) (input : RefVec aig w) (lo : Nat) (curr : Nat)
    (hcurr : curr ≤ newWidth) (falseRef : Ref aig) (s : RefVec aig curr) :
    ∀ (idx : Nat) (hidx1 : idx < curr),
        (go input lo falseRef curr hcurr s).get idx (by omega) = s.get idx hidx1 := by
  intro idx hidx
  generalize hgo : go input lo falseRef curr hcurr s = res
  unfold go at hgo
  split at hgo
  · dsimp only at hgo
    rw [← hgo]
    rw [go_get_aux]
    rw [AIG.RefVec.get_push_ref_lt]
  · dsimp only at hgo
    rw [← hgo]
    simp only [RefVec.get, Ref.mk.injEq]
    have : curr = newWidth := by omega
    subst this
    simp
termination_by newWidth - curr

theorem go_get (aig : AIG α) (input : RefVec aig w) (lo : Nat) (curr : Nat)
    (hcurr : curr ≤ newWidth) (falseRef : Ref aig) (s : RefVec aig curr) :
    ∀ (idx : Nat) (hidx1 : idx < newWidth),
        curr ≤ idx → (go input lo falseRef curr hcurr s).get idx hidx1 = input.getD (lo + idx) falseRef
    := by
  intro idx hidx1 hidx2
  generalize hgo : go input lo falseRef curr hcurr s = res
  unfold go at hgo
  dsimp only at hgo
  split at hgo
  · rw [← hgo]
    cases Nat.eq_or_lt_of_le hidx2 with
    | inl heq =>
      rw [go_get_aux]
      rw [AIG.RefVec.get_push_ref_eq']
      · simp [heq]
      · simp [heq]
    | inr heq =>
      rw [go_get]
      omega
  · omega
termination_by newWidth - curr

end blastExtract

@[simp]
theorem denote_blastExtract (aig : AIG α) (target : ExtractTarget aig newWidth)
    (assign : α → Bool) :
    ∀ (idx : Nat) (hidx : idx < newWidth),
        ⟦(blastExtract aig target).aig, (blastExtract aig target).vec.get idx hidx, assign⟧
          =
        if h : (target.start + idx) < target.w then
          ⟦aig, target.vec.get (target.start + idx) h, assign⟧
        else
          false
    := by
  intro idx hidx
  generalize hextract : blastExtract aig target = res
  rcases target with ⟨input, start⟩
  dsimp only
  unfold blastExtract at hextract
  dsimp only at hextract
  · rw [← hextract]
    rw [blastExtract.go_get]
    · dsimp only
      split
      · rw [RefVec.get_in_bound]
        rw [LawfulOperator.denote_mem_prefix (f := mkConstCached)]
        · congr 1
        · assumption
      · rw [RefVec.get_out_bound]
        · simp
        · omega
    · omega

end bitblast
end BVExpr

end Std.Tactic.BVDecide
