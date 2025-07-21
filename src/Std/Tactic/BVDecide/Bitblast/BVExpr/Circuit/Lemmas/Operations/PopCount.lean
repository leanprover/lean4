/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luisa Cicolini, Siddharth Bhat, Henrik Böving
-/
prelude
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Basic
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.PopCount
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Const
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Sub
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Eq


/-!
This module contains the verification of the bitblaster for `BitVec.popCountAuxRec` from
`Impl.Operations.popCount`. We prove that the accumulator of the `go` function
at step`n` represents the portion of the `ite` nodes in the AIG constructed for
bits `0` until `n`.
-/

namespace Std.Tactic.BVDecide

open Std.Sat
open Std.Sat.AIG

variable [Hashable α] [DecidableEq α]

namespace BVExpr

namespace bitblast
namespace blastPopCount

example (x : Nat) (hx : 0 < x) : ∃ y, x = y + 1 := by
  exact Nat.exists_eq_add_one.mpr hx

theorem go_denote_eq {w fuel: Nat} (aig : AIG α)
    (acc : AIG.RefVec aig w) (xc : AIG.RefVec aig w) (x : BitVec w) (assign : α → Bool)
    (hx : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, xc.get idx hidx, assign⟧ = x.getLsbD idx)
    (hacc : ∀ (idx : Nat) (hidx : idx < w),
      if fuel = 0 then ⟦aig, acc.get idx hidx, assign⟧ = (BitVec.ofNat w curr).getLsbD idx
      else
        if x = 0#w then ⟦aig, acc.get idx hidx, assign⟧ = (BitVec.ofNat w curr).getLsbD idx
        else ⟦aig, acc.get idx hidx, assign⟧ = (BitVec.popCountAuxRec (x &&& (x - 1)) (curr + 1) (fuel - 1)).getLsbD idx)
    :
    ∀ (idx : Nat) (hidx : idx < w),
        ⟦
          (go aig xc curr acc).aig,
          (go aig xc curr acc).vec.get idx hidx,
          assign
        ⟧
          =
        (BitVec.popCountAuxRec x 0 w).getLsbD idx := by
    intro idx hidx
    generalize hgo: go aig xc curr acc = res
    unfold go at hgo
    split at hgo
    · case isTrue h =>
      simp at hgo
      rw [← hgo, go_denote_eq]
      · intro idx hidx
        simp
        rw [AIG.LawfulVecOperator.denote_mem_prefix (f := blastSub)]
        · rw [AIG.LawfulVecOperator.denote_mem_prefix (f := RefVec.ite)]
          · rw [AIG.LawfulOperator.denote_mem_prefix (f := BVPred.mkEq)]
            · rw [AIG.LawfulVecOperator.denote_mem_prefix (f := blastSub)]
              · sorry
              ·

                sorry
            · simp [Ref.hgate]
      · intro idx hidx
        simp
        split
        ·
          sorry
        ·
          sorry
      ·
        sorry
    · case isFalse h =>
      rw [← hgo]
      sorry

end blastPopCount

@[simp]
theorem denote_blastPopCount (aig : AIG α) (xc : RefVec aig w) (x : BitVec w) (assign : α → Bool)
      (hx : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, xc.get idx hidx, assign⟧ = x.getLsbD idx)
      :
      ∀ (idx : Nat) (hidx : idx < w),
        ⟦(blastPopCount aig xc).aig, (blastPopCount aig xc).vec.get idx hidx, assign⟧
          =
        (BitVec.popCountAuxRec x 0 w).getLsbD idx := by
  sorry

end bitblast
end BVExpr

end Std.Tactic.BVDecide
