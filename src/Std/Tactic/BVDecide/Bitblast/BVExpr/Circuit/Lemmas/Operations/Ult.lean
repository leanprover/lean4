/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Basic
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Carry
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Not
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Ult

/-!
This module contains the verification of the bitblaster for `BitVec.ult` from `Impl.Operations.Ult`.
-/

namespace Std.Tactic.BVDecide

open Std.Sat
open Std.Sat.AIG

namespace BVPred

variable [Hashable α] [DecidableEq α]

theorem mkUlt_denote_eq (aig : AIG α) (lhs rhs : BitVec w) (input : BinaryRefVec aig w)
    (assign : α → Bool)
    (hleft : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, input.lhs.get idx hidx, assign⟧ = lhs.getLsbD idx)
    (hright : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, input.rhs.get idx hidx, assign⟧ = rhs.getLsbD idx) :
    ⟦mkUlt aig input, assign⟧ = BitVec.ult lhs rhs := by
  rw [BitVec.ult_eq_not_carry]
  unfold mkUlt
  simp only [denote_projected_entry, denote_mkNotCached]
  congr 1
  rw [BVExpr.bitblast.mkOverflowBit_eq_carry (input := ⟨w, _, _⟩) (lhs := lhs) (rhs := ~~~rhs)]
  · simp
  · dsimp only
    intro idx hidx
    rw [AIG.LawfulVecOperator.denote_mem_prefix (f := BVExpr.bitblast.blastNot)]
    apply hleft
  · dsimp only
    intro idx hidx
    simp only [hidx, BitVec.getLsbD_eq_getElem, BitVec.getElem_not]
    rw [BVExpr.bitblast.denote_blastNot, hright, BitVec.getLsbD_eq_getElem]

end BVPred

end Std.Tactic.BVDecide
