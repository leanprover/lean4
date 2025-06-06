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

namespace BVExpr
namespace bitblast

variable [Hashable α] [DecidableEq α]

-- prove that blastClz does the same as clzAuxRec
-- theorem go_denote_eq (aig : AIG α) (distance : Nat) (input : AIG.RefVec aig w)
--     (curr : Nat) (hcurr : curr ≤ w) (s : AIG.RefVec aig curr) :
--     ⟦(go aig x curr acc).aig,
--      (go aig x curr acc).vec.get idx (by sorry),
--      assign
--     ⟧
--       =
--     (BitVec.)

-- theorem go_denote_eq (aig : AIG α) (distance : AIG.RefVec aig n) (curr : Nat)
--       (hcurr : curr ≤ n - 1) (acc : AIG.RefVec aig w)
--     (x : BitVec w) (assign : α → Bool)
--     (hacc : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, acc.get idx hidx, assign⟧ = (BitVec.clzAuxRec x (w - 1)).getLsbD idx)
--     (hright : ∀ (idx : Nat) (hidx : idx < n), ⟦aig, distance.get idx hidx, assign⟧ = (go aig acc (w-1)).getLsbD idx) :
--     ∀ (idx : Nat) (hidx : idx < w),
--         ⟦
--           (go aig distance curr acc).aig,
--           (go aig distance curr acc).vec.get idx hidx,
--           assign
--         ⟧
--           =
--         (BitVec.clzAuxRec x (w - 1)).getLsbD idx := by sorry

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
