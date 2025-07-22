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
    (hx' : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, xc'.get idx hidx, assign⟧ = (x.popCountAuxAnd (w - curr)).getLsbD idx)
    (hacc : ∀ (idx : Nat) (hidx : idx < w),
      ⟦aig, acc.get idx hidx, assign⟧ =
        (if curr = 0 then x.popCountAuxRec w
        else if (x.popCountAuxAnd curr) = 0#w then BitVec.ofNat w (w - curr) else (x.popCountAuxAnd (curr + 1)).popCountAuxRec (curr - 1)).getLsbD idx)
    :
    ∀ (idx : Nat) (hidx : idx < w),
        ⟦
          (go aig xc' curr acc).aig,
          (go aig xc' curr acc).vec.get idx hidx,
          assign
        ⟧
          =
        (BitVec.popCountAuxRec x w).getLsbD idx := by
    intro idx hidx
    generalize hgo: go aig xc' curr acc = res
    unfold go at hgo
    split at hgo
    · case isTrue h =>
      simp at hgo
      rw [← hgo, go_denote_eq]
      · omega
      ·
        exact
        (RefVec.zip
            (blastSub
                (RefVec.ite (BVPred.mkEq aig { lhs := xc', rhs := blastConst aig 0#w }).aig
                    { discr := (BVPred.mkEq aig { lhs := xc', rhs := blastConst aig 0#w }).ref,
                      lhs := (blastConst aig (BitVec.ofNat w w - BitVec.ofNat w curr)).cast ⋯,
                      rhs := acc.cast ⋯ }).aig
                { lhs := xc'.cast ⋯,
                  rhs :=
                    blastConst
                      (RefVec.ite (BVPred.mkEq aig { lhs := xc', rhs := blastConst aig 0#w }).aig
                          {
                            discr :=
                              (BVPred.mkEq aig { lhs := xc', rhs := blastConst aig 0#w }).ref,
                            lhs := (blastConst aig (BitVec.ofNat w w - BitVec.ofNat w curr)).cast ⋯,
                            rhs := acc.cast ⋯ }).aig
                      1#w }).aig
            { lhs := xc'.cast ⋯,
              rhs :=
                (blastSub
                    (RefVec.ite (BVPred.mkEq aig { lhs := xc', rhs := blastConst aig 0#w }).aig
                        { discr := (BVPred.mkEq aig { lhs := xc', rhs := blastConst aig 0#w }).ref,
                          lhs := (blastConst aig (BitVec.ofNat w w - BitVec.ofNat w curr)).cast ⋯,
                          rhs := acc.cast ⋯ }).aig
                    { lhs := xc'.cast ⋯,
                      rhs :=
                        blastConst
                          (RefVec.ite
                              (BVPred.mkEq aig { lhs := xc', rhs := blastConst aig 0#w }).aig
                              {
                                discr :=
                                  (BVPred.mkEq aig { lhs := xc', rhs := blastConst aig 0#w }).ref,
                                lhs :=
                                  (blastConst aig (BitVec.ofNat w w - BitVec.ofNat w curr)).cast ⋯,
                                rhs := acc.cast ⋯ }).aig
                          1#w }).vec }
            mkAndCached).vec
      · simp
        intros
        sorry
      · simp [show ¬ curr = 0 by omega] at *
        simp_all
        intros
        sorry
      · simp
        sorry
    · case isFalse h =>
      rw [← hgo]
      simp [show curr = 0 by omega] at *
      split
      · case _ h =>

        sorry
      · case _ h =>
        sorry

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
