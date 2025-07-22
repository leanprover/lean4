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

theorem go_denote_eq {w : Nat} (aig : AIG α) (h : curr ≤ w)
    (acc : AIG.RefVec aig w) (xc : AIG.RefVec aig w) (xc' : AIG.RefVec aig w) (x : BitVec w) (assign : α → Bool)
    (hx : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, xc.get idx hidx, assign⟧ = x.getLsbD idx)
    (hx' : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, xc'.get idx hidx, assign⟧ = (x.popCountAuxAnd curr).getLsbD idx)
    (hacc : ∀ (idx : Nat) (hidx : idx < w),
      ⟦aig, acc.get idx hidx, assign⟧ =
        if w - curr = 0 then (BitVec.ofNat w 0).getLsbD idx
        else (BitVec.popCountAuxRec x (w - curr - 1)).getLsbD idx)
    :
    ∀ (idx : Nat) (hidx : idx < w),
        ⟦
          (go aig xc' curr acc).aig,
          (go aig xc' curr acc).vec.get idx hidx,
          assign
        ⟧
          =
        (BitVec.popCountAuxRec x w).getLsbD idx := by sorry
    -- intro idx hidx
    -- generalize hgo: go aig xc curr acc = res
    -- unfold go at hgo
    -- split at hgo
    -- · case isTrue h =>
    --   simp only [BitVec.ofNat_eq_ofNat, BitVec.natCast_eq_ofNat, RefVec.cast_cast] at hgo
    --   rw [← hgo, go_denote_eq (x := x &&& (x - 1))]
    --   · let curr' := curr - 1
    --     simp [show curr = curr' + 1 by omega]
    --     rw [BitVec.popCountAuxRec_succ]

    --     sorry
    --   · simp
    --     omega
    --   · simp
    --     sorry
    --   · simp
    --     sorry
      -- go_denote_eq]
      -- · let curr' := curr - 1
      --   simp [show curr = curr' + 1 by omega]
      --   rw [BitVec.popCountAuxRec_succ]
      --   simp [show ¬ curr = 0 by omega] at hacc
      --   by_cases hx0 : x = 0#w
      --   · simp [hx0]
      --     simp [hx0] at hacc
      --     sorry
      --   · simp [hx0]
      --     sorry
      -- · sorry
      -- · sorry
      -- · sorry
      -- · sorry
      -- · sorry
      -- · intro  hidx
      --   simp
      --   rw [AIG.LawfulVecOperator.denote_mem_prefix (f := blastSub)]
      --   · rw [AIG.LawfulVecOperator.denote_mem_prefix (f := RefVec.ite)]
      --     · rw [AIG.LawfulOperator.denote_mem_prefix (f := BVPred.mkEq)]
      --       · rw [AIG.LawfulVecOperator.denote_mem_prefix (f := blastSub)]
      --         · sorry
      --         · apply LawfulVecOperator.lt_size_of_lt_aig_size (f := AIG.RefVec.ite)



      --           sorry
      --       · simp [Ref.hgate]
      -- · intro idx hidx
      --   simp
      --   split
      --   ·
      --     sorry
      --   ·
      --     sorry
      -- ·
    -- · case isFalse h =>
    --   rw [← hgo]
    --   simp [show curr = 0 by omega] at hacc
    --   simp [show curr = 0 by omega, BitVec.popCountAuxRec_zero]

end blastPopCount

@[simp]
theorem denote_blastPopCount (aig : AIG α) (xc : RefVec aig w) (x : BitVec w) (assign : α → Bool)
      (hx : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, xc.get idx hidx, assign⟧ = x.getLsbD idx)
      :
      ∀ (idx : Nat) (hidx : idx < w),
        ⟦(blastPopCount aig xc).aig, (blastPopCount aig xc).vec.get idx hidx, assign⟧
          =
        (BitVec.popCountAuxRec x w).getLsbD idx := by
  sorry

end bitblast
end BVExpr

end Std.Tactic.BVDecide
