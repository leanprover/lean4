/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Lean.Elab.Tactic.BvDecide.BitBlast.BVExpr.BitBlast.Lemmas.Basic
import Lean.Elab.Tactic.BvDecide.BitBlast.BVExpr.BitBlast.Lemmas.Carry
import Lean.Elab.Tactic.BvDecide.BitBlast.BVExpr.BitBlast.Lemmas.Not
import Lean.Elab.Tactic.BvDecide.BitBlast.BVExpr.BitBlast.Impl.Ult

namespace Lean.Elab.Tactic.BvDecide

open Std.Sat
open Std.Sat.AIG

namespace BVPred

variable [Hashable α] [DecidableEq α]

theorem mkUlt_denote_eq (aig : AIG α) (lhs rhs : BitVec w) (input : BinaryRefVec aig w)
    (assign : α → Bool)
    (hleft : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, input.lhs.get idx hidx, assign⟧ = lhs.getLsb idx)
    (hright : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, input.rhs.get idx hidx, assign⟧ = rhs.getLsb idx) :
    ⟦(mkUlt aig input).aig, (mkUlt aig input).ref, assign⟧ = BitVec.ult lhs rhs := by
  rw [BitVec.ult_eq_not_carry]
  unfold mkUlt
  simp only [denote_projected_entry, denote_mkNotCached, denote_projected_entry']
  congr 1
  rw [BVExpr.bitblast.mkOverflowBit_eq_carry (input := ⟨w, _, _⟩) (lhs := lhs) (rhs := ~~~rhs)]
  . simp
  . dsimp only
    intro idx hidx
    rw [AIG.LawfulOperator.denote_mem_prefix (f := AIG.mkConstCached)]
    rw [AIG.LawfulVecOperator.denote_mem_prefix (f := BVExpr.bitblast.blastNot)]
    apply hleft
    assumption
  . dsimp only
    intro idx hidx
    rw [AIG.LawfulOperator.denote_mem_prefix (f := AIG.mkConstCached)]
    . simp only [RefVec.get_cast, Ref_cast', BitVec.getLsb_not, hidx, decide_True,
        Bool.true_and]
      rw [BVExpr.bitblast.blastNot_denote_eq]
      congr 1
      apply hright
    . simp [Ref.hgate]

end BVPred

end Lean.Elab.Tactic.BvDecide
