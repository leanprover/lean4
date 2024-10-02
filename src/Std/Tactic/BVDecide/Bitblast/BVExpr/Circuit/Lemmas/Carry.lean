/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Basic
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Add
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Carry

/-!
This module contains the verification of the overflow detection bitblaster from `Impl.Carry`.
-/

namespace Std.Tactic.BVDecide

open Std.Sat
open Std.Sat.AIG

namespace BVExpr
namespace bitblast

variable [Hashable α] [DecidableEq α]

namespace mkOverflowBit

theorem go_eq_carry (aig : AIG α) (curr : Nat) (hcurr : curr ≤ w) (cin : Ref aig) (origCin : Ref aig)
    (lhs rhs : RefVec aig w) (lhsExpr rhsExpr : BitVec w) (assign : α → Bool)
    (hleft : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, lhs.get idx hidx, assign⟧ = lhsExpr.getLsbD idx)
    (hright : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, rhs.get idx hidx, assign⟧ = rhsExpr.getLsbD idx)
    (hcin : ⟦aig, cin, assign⟧ = BitVec.carry curr lhsExpr rhsExpr ⟦aig, origCin, assign⟧) :
    ⟦go aig lhs rhs curr cin, assign⟧
      =
    BitVec.carry w lhsExpr rhsExpr ⟦aig, origCin, assign⟧ := by
  unfold go
  dsimp only
  split
  · rw [go_eq_carry]
    · congr 1
      rw [AIG.LawfulOperator.denote_mem_prefix (f := mkFullAdderCarry)]
    · omega
    · intros
      rw [AIG.LawfulOperator.denote_mem_prefix (f := mkFullAdderCarry)]
      · simp [hleft]
      · simp [Ref.hgate]
    · intros
      rw [AIG.LawfulOperator.denote_mem_prefix (f := mkFullAdderCarry)]
      · simp [hright]
      · simp [Ref.hgate]
    · simp only [denote_projected_entry, blastAdd.denote_mkFullAdderCarry, BitVec.carry_succ]
      rw [AIG.LawfulOperator.denote_mem_prefix (f := mkFullAdderCarry)]
      rw [hleft, hright, hcin]
      rw [blastAdd.atLeastTwo_eq_halfAdder]
  · have : w = curr := by omega
    rw [hcin]
    simp [this]
termination_by w - curr

end mkOverflowBit

theorem mkOverflowBit_eq_carry (aig : AIG α) (input : OverflowInput aig) (lhs rhs : BitVec input.w)
    (assign : α → Bool)
    (hleft : ∀ (idx : Nat) (hidx : idx < input.w), ⟦aig, input.vec.lhs.get idx hidx, assign⟧ = lhs.getLsbD idx)
    (hright : ∀ (idx : Nat) (hidx : idx < input.w), ⟦aig, input.vec.rhs.get idx hidx, assign⟧ = rhs.getLsbD idx) :
    ⟦mkOverflowBit aig input, assign⟧
      =
    BitVec.carry input.w lhs rhs ⟦aig, input.cin, assign⟧ := by
  unfold mkOverflowBit
  dsimp only
  apply mkOverflowBit.go_eq_carry
  · omega
  · assumption
  · assumption
  · simp [BitVec.carry_zero]

end bitblast
end BVExpr

end Std.Tactic.BVDecide
