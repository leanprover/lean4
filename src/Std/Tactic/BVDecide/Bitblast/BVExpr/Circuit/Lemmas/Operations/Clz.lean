/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luisa Cicolini
-/
prelude
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Basic
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Clz

/-!
This module contains the verification of the bitblaster for `BitVec.clz` from
`Impl.Operations.Clz`.
-/

namespace Std.Tactic.BVDecide

open Std.Sat
open Std.Sat.AIG

variable [Hashable α] [DecidableEq α]

namespace BVExpr

namespace bitblast
namespace blastClz


-- prove that blastClz does the same as clzAuxRec
-- theorem go_denote_eq (aig : AIG α) (distance : Nat) (input : AIG.RefVec aig w)
--     (curr : Nat) (hcurr : curr ≤ w) (s : AIG.RefVec aig curr) :
--     ⟦(go aig x curr acc).aig,
--      (go aig x curr acc).vec.get idx (by sorry),
--      assign
--     ⟧
--       =
--     (BitVec.)


theorem go_denote_eq {w : Nat} (aig : AIG α) (curr : Nat) (hcurr : curr + 1 ≤ w)
    (acc : AIG.RefVec aig w) (x : AIG.RefVec aig w) (xexpr : BitVec w) (assign : α → Bool)
    -- correctness of the denotation for x and xexpr
    (hx : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, x.get idx hidx, assign⟧ = xexpr.getLsbD idx)
    -- correctness of the denotation for the accumulator
    (hacc : ∀ (idx : Nat) (hidx : idx < w),
                ⟦aig, acc.get idx hidx, assign⟧
                  =
                (BitVec.clzAuxRec xexpr curr).getLsbD idx) :
    ∀ (idx : Nat) (hidx : idx < w),
        ⟦
          (go aig x (curr + 1) acc).aig,
          (go aig x (curr + 1) acc).vec.get idx hidx,
          assign
        ⟧
          =
        (BitVec.clzAuxRec xexpr (w - 1)).getLsbD idx := by
  sorry

end blastClz

@[simp]
theorem denote_blastClz (aig : AIG α) (target : RefVec aig w)
    (assign : α → Bool) :
    ∀ (idx : Nat) (hidx : idx < w),
        ⟦(blastClz aig target).aig, (blastClz aig target).vec.get idx hidx, assign⟧
          =
        (BitVec.clzAuxRec x (w - 1)).getLsbD idx:= by
  intro idx hidx
  simp [blastClz, AIG.RefVec.get]

  sorry


end bitblast
end BVExpr

end Std.Tactic.BVDecide
