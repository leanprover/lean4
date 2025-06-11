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

-- go aig x n acc = ite x[n] then (w - 1 - n) else acc
-- we prove that this is true for n = 0 
-- we prove that under the hypothesis that this holds until n, it will hold until n + 1
-- circuit: when curr = 0 → ite x[0] then (w - 1) else acc, where acc is w
-- circuit: when curr = w - 1 → ite x[w - 1] then 0 else acc, where acc is a chain of ite nodes
-- the actual base case of the recursion is 
    
theorem go_denote_zero_eq {w : Nat} (aig : AIG α) 
    (acc : AIG.RefVec aig w) (xc : AIG.RefVec aig w) (x : BitVec w) (assign : α → Bool)
    (hxbv : ∀ (idx : Nat) (hidx : 0 < idx), x.getLsbD idx = false) 
    (hx : ∀ (idx : Nat) (hidx : 0 < idx) (hidx' : idx < w), ⟦aig, (xc.get idx hidx'), assign⟧ = false) 
    : 
    ∀ (idx : Nat) (hidx : idx < w), 
      ⟦(go aig xc 0 acc).aig, (go aig xc 0 acc).vec.get idx hidx, assign⟧ = 
        (BitVec.clzAuxRec x 0).getLsbD idx := by 
    intro idx hidx 
    generalize hgo0 : go aig xc 0 acc = res 
    unfold go at hgo0 
    split at hgo0 
    · simp at hgo0
      rw [RefVec.denote_ite] at hgo0i

      sorry 
    · simp [show w = 0 by omega] at hidx 

theorem go_denote_eq {w : Nat} (aig : AIG α)
    (acc : AIG.RefVec aig w) (x : AIG.RefVec aig w) (xexpr : BitVec w) (assign : α → Bool)
    -- correctness of the denotation for x and xexpr
    (hx : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, x.get idx hidx, assign⟧ = xexpr.getLsbD idx)
    -- correctness of the denotation for the accumulator
    (hacc : ∀ (idx : Nat) (hidx : idx < w),
                ⟦aig, acc.get idx hidx, assign⟧
                  =
                (BitVec.clzAuxRec xexpr (w - 1)).getLsbD idx) :
    ∀ (idx : Nat) (hidx : idx < w),
        ⟦
          (go aig x 0 acc).aig,
          (go aig x 0 acc).vec.get idx hidx,
          assign
        ⟧
          =
        (BitVec.clzAuxRec xexpr (w - 1)).getLsbD idx := by
    generalize hgo: go aig x 0 acc = res
    unfold go at hgo
    split at hgo
    ·
      sorry
    · simp [show w = 0 by omega]

-- theorem go_denote_eq {w : Nat} (aig : AIG α) (hw : 0 < w)
--     (acc : AIG.RefVec aig w) (x : AIG.RefVec aig w) (xexpr : BitVec w) (assign : α → Bool)
--     -- correctness of the denotation for x and xexpr
--     (hx : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, x.get idx hidx, assign⟧ = xexpr.getLsbD idx)
--     -- correctness of the denotation for the accumulator
--     (hacc : ∀ (idx : Nat) (hidx : idx < w),
--                 ⟦aig, acc.get idx hidx, assign⟧
--                   =
--                 (BitVec.clzAuxRec xexpr (w - 1)).getLsbD idx) :
--     ∀ (idx : Nat) (hidx : idx < w),
--         ⟦
--           (go aig x (w - 1) acc).aig,
--           (go aig x (w - 1) acc).vec.get idx hidx,
--           assign
--         ⟧
--           =
--         (BitVec.clzAuxRec xexpr (w - 1)).getLsbD idx := by
--   intro idx hidx
--   generalize hgo: go aig x (w - 1) acc = resx
--   unfold go at hgo
--   split at hgo
--   · rw [← hgo]
--     simp only [BitVec.natCast_eq_ofNat, BitVec.ofNat_eq_ofNat, RefVec.cast_cast] at hgo

--     sorry
--   · omega

end blastClz

@[simp]
theorem denote_blastClz (aig : AIG α) (x : RefVec aig w) (xbv : BitVec w) (assign : α → Bool)
      (hleft : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, x.get idx hidx, assign⟧ = xbv.getLsbD idx) :
      ∀ (idx : Nat) (hidx : idx < w),
        ⟦(blastClz aig x).aig, (blastClz aig x).vec.get idx hidx, assign⟧
          =
        xbv.getLsbD idx := by
  intro idx hidx
  generalize hb : blastClz aig x = res
  unfold blastClz at hb
  dsimp only at hb
  -- blastClz.go (blastConst aig (w - 1).aig x 0 (blastConst aig (w - 1).vec = 

  -- split at hb
  -- · rw [← hb, blastMul.denote_blast] <;> assumption
  -- · rw [BitVec.mul_comm, ← hb, blastMul.denote_blast] <;> assumption
  sorry


end bitblast
end BVExpr

end Std.Tactic.BVDecide
