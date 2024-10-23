/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Udiv
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Neg
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Sdiv
import Std.Tactic.BVDecide.Normalize.BitVec

/-!
This module contains the verification of the `BitVec.sdiv` bitblaster from `Impl.Operations.Sdiv`.
-/

namespace Std.Tactic.BVDecide

open Std.Sat
open Std.Sat.AIG

namespace BVExpr
namespace bitblast

variable [Hashable α] [DecidableEq α]

private theorem sdiv_of_pos_of_pos {lhs rhs : BitVec w} (h1 : lhs.msb = false) (h2 : rhs.msb = false) :
    lhs.sdiv rhs = lhs / rhs := by
  simp [BitVec.sdiv_eq, h1, h2]

private theorem sdiv_of_pos_of_neg {lhs rhs : BitVec w} (h1 : lhs.msb = false) (h2 : rhs.msb = true) :
    lhs.sdiv rhs = -(lhs / -rhs) := by
  simp [BitVec.sdiv_eq, h1, h2]

private theorem sdiv_of_neg_of_pos {lhs rhs : BitVec w} (h1 : lhs.msb = true) (h2 : rhs.msb = false) :
    lhs.sdiv rhs = -(-lhs / rhs) := by
  simp [BitVec.sdiv_eq, h1, h2]

private theorem sdiv_of_neg_of_neg {lhs rhs : BitVec w} (h1 : lhs.msb = true) (h2 : rhs.msb = true) :
    lhs.sdiv rhs = (-lhs) / (-rhs) := by
  simp [BitVec.sdiv_eq, h1, h2]

theorem denote_blastSdiv (aig : AIG α) (lhs rhs : BitVec w) (assign : α → Bool)
      (input : BinaryRefVec aig w)
      (hleft : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, input.lhs.get idx hidx, assign⟧ = lhs.getLsbD idx)
      (hright : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, input.rhs.get idx hidx, assign⟧ = rhs.getLsbD idx) :
      ∀ (idx : Nat) (hidx : idx < w),
        ⟦(blastSdiv aig input).aig, (blastSdiv aig input).vec.get idx hidx, assign⟧
          =
        (BitVec.sdiv lhs rhs).getLsbD idx := by sorry
/-
  intros
  generalize hres : blastSdiv aig input = res
  unfold blastSdiv at hres
  split at hres
  · omega
  · rw [← hres]
    clear hres
    simp only [RefVec.denote_ite, RefVec.get_cast, Ref.cast_eq]
    split
    · next h1 =>
      rw [AIG.LawfulVecOperator.denote_mem_prefix, AIG.LawfulVecOperator.denote_mem_prefix,
       AIG.LawfulVecOperator.denote_mem_prefix, AIG.LawfulVecOperator.denote_mem_prefix,
       AIG.LawfulVecOperator.denote_mem_prefix, AIG.LawfulVecOperator.denote_mem_prefix,
       AIG.LawfulVecOperator.denote_mem_prefix, AIG.LawfulVecOperator.denote_mem_prefix,
       AIG.LawfulVecOperator.denote_mem_prefix, AIG.LawfulVecOperator.denote_mem_prefix] at h1
      rw [hleft, ← BitVec.msb_eq_getLsbD_last ] at h1
      split
      · next h2 =>
        rw [AIG.LawfulVecOperator.denote_mem_prefix, AIG.LawfulVecOperator.denote_mem_prefix,
            AIG.LawfulVecOperator.denote_mem_prefix, AIG.LawfulVecOperator.denote_mem_prefix,
            AIG.LawfulVecOperator.denote_mem_prefix, AIG.LawfulVecOperator.denote_mem_prefix,
            AIG.LawfulVecOperator.denote_mem_prefix, AIG.LawfulVecOperator.denote_mem_prefix,
            AIG.LawfulVecOperator.denote_mem_prefix] at h2
        rw [hright, ← BitVec.msb_eq_getLsbD_last ] at h2
        rw [AIG.LawfulVecOperator.denote_mem_prefix]
        rw [denote_blastUdiv (lhs := -lhs) (rhs := -rhs)]
        · rw [sdiv_of_neg_of_neg h1 h2]
        · intros
          rw [AIG.LawfulVecOperator.denote_mem_prefix, AIG.LawfulVecOperator.denote_mem_prefix,
              AIG.LawfulVecOperator.denote_mem_prefix,
              AIG.LawfulVecOperator.denote_mem_prefix,
              AIG.LawfulVecOperator.denote_mem_prefix,
              AIG.LawfulVecOperator.denote_mem_prefix,
          ]
          · simp only [RefVec.get_cast, Ref.cast_eq]
            rw [denote_blastNeg]
            exact hleft
          · simp [Ref.hgate]
        · intros
          simp only [RefVec.get_cast, Ref.cast_eq]
          rw [AIG.LawfulVecOperator.denote_mem_prefix, AIG.LawfulVecOperator.denote_mem_prefix,
              AIG.LawfulVecOperator.denote_mem_prefix,
              AIG.LawfulVecOperator.denote_mem_prefix,
              AIG.LawfulVecOperator.denote_mem_prefix,
          ]
          rw [denote_blastNeg]
          intros
          simp only [RefVec.get_cast, Ref.cast_eq]
          rw [AIG.LawfulVecOperator.denote_mem_prefix]
          rw [hright]
      · next h2 =>
        rw [AIG.LawfulVecOperator.denote_mem_prefix, AIG.LawfulVecOperator.denote_mem_prefix,
            AIG.LawfulVecOperator.denote_mem_prefix, AIG.LawfulVecOperator.denote_mem_prefix,
            AIG.LawfulVecOperator.denote_mem_prefix, AIG.LawfulVecOperator.denote_mem_prefix,
            AIG.LawfulVecOperator.denote_mem_prefix, AIG.LawfulVecOperator.denote_mem_prefix,
            AIG.LawfulVecOperator.denote_mem_prefix] at h2
        rw [hright, ← BitVec.msb_eq_getLsbD_last, Bool.not_eq_true] at h2
        rw [AIG.LawfulVecOperator.denote_mem_prefix, AIG.LawfulVecOperator.denote_mem_prefix]
        rw [denote_blastNeg (value := (-lhs) / rhs)]
        · rw [sdiv_of_neg_of_pos h1 h2]
        · intros
          rw [denote_blastUdiv (lhs := -lhs) (rhs := rhs)]
          · intros
            rw [AIG.LawfulVecOperator.denote_mem_prefix, AIG.LawfulVecOperator.denote_mem_prefix,
                AIG.LawfulVecOperator.denote_mem_prefix, AIG.LawfulVecOperator.denote_mem_prefix,
            ]
            simp only [RefVec.get_cast, Ref.cast_eq]
            rw [denote_blastNeg (value := lhs)]
            · exact hleft
            · simp [Ref.hgate]
          · intros
            rw [AIG.LawfulVecOperator.denote_mem_prefix, AIG.LawfulVecOperator.denote_mem_prefix,
                AIG.LawfulVecOperator.denote_mem_prefix, AIG.LawfulVecOperator.denote_mem_prefix,
                AIG.LawfulVecOperator.denote_mem_prefix]
            · simp [hright]
            · simp [Ref.hgate]
    · next h1 =>
      rw [AIG.LawfulVecOperator.denote_mem_prefix, AIG.LawfulVecOperator.denote_mem_prefix,
          AIG.LawfulVecOperator.denote_mem_prefix, AIG.LawfulVecOperator.denote_mem_prefix,
          AIG.LawfulVecOperator.denote_mem_prefix, AIG.LawfulVecOperator.denote_mem_prefix,
          AIG.LawfulVecOperator.denote_mem_prefix, AIG.LawfulVecOperator.denote_mem_prefix,
          AIG.LawfulVecOperator.denote_mem_prefix, AIG.LawfulVecOperator.denote_mem_prefix] at h1
      rw [hleft, ← BitVec.msb_eq_getLsbD_last, Bool.not_eq_true] at h1
      rw [AIG.LawfulVecOperator.denote_mem_prefix (f := AIG.RefVec.ite)]
      rw [AIG.RefVec.denote_ite]
      split
      · next h2 =>
        rw [AIG.LawfulVecOperator.denote_mem_prefix, AIG.LawfulVecOperator.denote_mem_prefix,
         AIG.LawfulVecOperator.denote_mem_prefix, AIG.LawfulVecOperator.denote_mem_prefix,
         AIG.LawfulVecOperator.denote_mem_prefix, AIG.LawfulVecOperator.denote_mem_prefix,
         AIG.LawfulVecOperator.denote_mem_prefix, AIG.LawfulVecOperator.denote_mem_prefix,
        ] at h2
        simp only [RefVec.get_cast, Ref.cast_eq] at h2
        rw [hright, ← BitVec.msb_eq_getLsbD_last] at h2
        rw [AIG.LawfulVecOperator.denote_mem_prefix, AIG.LawfulVecOperator.denote_mem_prefix,
         AIG.LawfulVecOperator.denote_mem_prefix]
        · simp only [RefVec.get_cast, Ref.cast_eq]
          rw [denote_blastNeg (value := lhs / (-rhs))]
          · rw [sdiv_of_pos_of_neg h1 h2]
          · intros
            rw [denote_blastUdiv (lhs := lhs) (rhs := -rhs)]
            · intros
              rw [AIG.LawfulVecOperator.denote_mem_prefix, AIG.LawfulVecOperator.denote_mem_prefix,
                  AIG.LawfulVecOperator.denote_mem_prefix]
              · simp [hleft]
              · simp [Ref.hgate]
            · intros
              rw [AIG.LawfulVecOperator.denote_mem_prefix]
              · simp only [RefVec.get_cast, Ref.cast_eq]
                rw [denote_blastNeg (value := rhs)]
                intros
                rw [AIG.LawfulVecOperator.denote_mem_prefix]
                · simp [hright]
                · simp [Ref.hgate]
              · simp [Ref.hgate]
        · simp [Ref.hgate]
      · next h2 =>
        rw [AIG.LawfulVecOperator.denote_mem_prefix, AIG.LawfulVecOperator.denote_mem_prefix,
         AIG.LawfulVecOperator.denote_mem_prefix, AIG.LawfulVecOperator.denote_mem_prefix,
         AIG.LawfulVecOperator.denote_mem_prefix, AIG.LawfulVecOperator.denote_mem_prefix,
         AIG.LawfulVecOperator.denote_mem_prefix, AIG.LawfulVecOperator.denote_mem_prefix,
        ] at h2
        simp only [RefVec.get_cast, Ref.cast_eq] at h2
        rw [hright, ← BitVec.msb_eq_getLsbD_last, Bool.not_eq_true] at h2
        rw [AIG.LawfulVecOperator.denote_mem_prefix, AIG.LawfulVecOperator.denote_mem_prefix,
         AIG.LawfulVecOperator.denote_mem_prefix, AIG.LawfulVecOperator.denote_mem_prefix,
         AIG.LawfulVecOperator.denote_mem_prefix]
        simp only [RefVec.get_cast, Ref.cast_eq]
        · rw [denote_blastUdiv (lhs := lhs) (rhs := rhs)]
          · rw [sdiv_of_pos_of_pos h1 h2]
          · intros
            rw [AIG.LawfulVecOperator.denote_mem_prefix, AIG.LawfulVecOperator.denote_mem_prefix]
            · simp [hleft]
            · simp [Ref.hgate]
          · intros
            rw [AIG.LawfulVecOperator.denote_mem_prefix, AIG.LawfulVecOperator.denote_mem_prefix]
            · simp [hright]
            · simp [Ref.hgate]
        · simp [Ref.hgate]-/

end bitblast
end BVExpr

end Std.Tactic.BVDecide
