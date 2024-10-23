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

namespace blastSdiv

theorem denote_signBranch {aig : AIG α} (input : SignBranchInput aig len) (lhs rhs : BitVec input.w)
    (lposRpos lposRneg lnegRpos lnegRneg : BitVec len)
    (hleft : ∀ (idx : Nat) (hidx : idx < input.w), ⟦aig, input.lhs.get idx hidx, assign⟧ = lhs.getLsbD idx)
    (hright : ∀ (idx : Nat) (hidx : idx < input.w), ⟦aig, input.rhs.get idx hidx, assign⟧ = rhs.getLsbD idx)
    (hlprp : ∀ (idx : Nat) (hidx : idx < len), ⟦aig, input.lposRpos.get idx hidx, assign⟧ = lposRpos.getLsbD idx)
    (hlprn : ∀ (idx : Nat) (hidx : idx < len), ⟦aig, input.lposRneg.get idx hidx, assign⟧ = lposRneg.getLsbD idx)
    (hlnrp : ∀ (idx : Nat) (hidx : idx < len), ⟦aig, input.lnegRpos.get idx hidx, assign⟧ = lnegRpos.getLsbD idx)
    (hlnrn : ∀ (idx : Nat) (hidx : idx < len), ⟦aig, input.lnegRneg.get idx hidx, assign⟧ = lnegRneg.getLsbD idx) :
    ∀ (idx : Nat) (hidx : idx < len),
      ⟦(signBranch aig input).aig, (signBranch aig input).vec.get idx hidx, assign⟧
        =
      (match lhs.msb, rhs.msb with
      | false, false => lposRpos
      | false, true => lposRneg
      | true, false => lnegRpos
      | true, true => lnegRneg).getLsbD idx
      := by
  intros
  unfold signBranch
  simp only [ne_eq, RefVec.denote_ite, RefVec.get_cast, Ref.cast_eq]
  split
  · next h1 =>
    rw [AIG.LawfulVecOperator.denote_mem_prefix, AIG.LawfulVecOperator.denote_mem_prefix] at h1
    rw [hleft, ← BitVec.msb_eq_getLsbD_last] at h1
    rw [h1]
    split
    · next h2 =>
      rw [AIG.LawfulVecOperator.denote_mem_prefix] at h2
      rw [hright, ← BitVec.msb_eq_getLsbD_last] at h2
      rw [h2]
      rw [AIG.LawfulVecOperator.denote_mem_prefix, hlnrn]
    · next h2 =>
      rw [AIG.LawfulVecOperator.denote_mem_prefix] at h2
      rw [hright, ← BitVec.msb_eq_getLsbD_last, Bool.not_eq_true] at h2
      rw [h2]
      rw [AIG.LawfulVecOperator.denote_mem_prefix, hlnrp]
  · next h1 =>
    rw [AIG.LawfulVecOperator.denote_mem_prefix, AIG.LawfulVecOperator.denote_mem_prefix] at h1
    rw [hleft, ← BitVec.msb_eq_getLsbD_last, Bool.not_eq_true] at h1
    rw [h1]
    rw [AIG.LawfulVecOperator.denote_mem_prefix]
    rw [AIG.RefVec.denote_ite]
    split
    · next h2 =>
      rw [hright, ← BitVec.msb_eq_getLsbD_last] at h2
      rw [h2]
      simp [hlprn]
    · next h2 =>
      rw [hright, ← BitVec.msb_eq_getLsbD_last, Bool.not_eq_true] at h2
      rw [h2]
      simp [hlprp]

end blastSdiv

theorem denote_blastSdiv (aig : AIG α) (lhs rhs : BitVec w) (assign : α → Bool)
    (input : BinaryRefVec aig w)
    (hleft : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, input.lhs.get idx hidx, assign⟧ = lhs.getLsbD idx)
    (hright : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, input.rhs.get idx hidx, assign⟧ = rhs.getLsbD idx) :
    ∀ (idx : Nat) (hidx : idx < w),
      ⟦(blastSdiv aig input).aig, (blastSdiv aig input).vec.get idx hidx, assign⟧
        =
      (BitVec.sdiv lhs rhs).getLsbD idx := by
  intros
  generalize hres : blastSdiv aig input = res
  unfold blastSdiv at hres
  split at hres
  · omega
  · dsimp only at hres
    rw [← hres]
    clear hres
    rw [blastSdiv.denote_signBranch
        (lhs := lhs)
        (rhs := rhs)
        (lposRpos := lhs / rhs)
        (lposRneg := -(lhs / (-rhs)))
        (lnegRpos := -((-lhs) / rhs))
        (lnegRneg := ((-lhs) / (-rhs)))
      ]
    · rw [BitVec.sdiv_eq]
      rfl
    · simp only [RefVec.get_cast, Ref.cast_eq]
      intros
      rw [AIG.LawfulVecOperator.denote_mem_prefix, AIG.LawfulVecOperator.denote_mem_prefix,
        AIG.LawfulVecOperator.denote_mem_prefix, AIG.LawfulVecOperator.denote_mem_prefix,
        AIG.LawfulVecOperator.denote_mem_prefix, AIG.LawfulVecOperator.denote_mem_prefix,
        AIG.LawfulVecOperator.denote_mem_prefix, AIG.LawfulVecOperator.denote_mem_prefix]
      rw [hleft]
    · simp only [RefVec.get_cast, Ref.cast_eq]
      intros
      rw [AIG.LawfulVecOperator.denote_mem_prefix, AIG.LawfulVecOperator.denote_mem_prefix,
        AIG.LawfulVecOperator.denote_mem_prefix, AIG.LawfulVecOperator.denote_mem_prefix,
        AIG.LawfulVecOperator.denote_mem_prefix, AIG.LawfulVecOperator.denote_mem_prefix,
        AIG.LawfulVecOperator.denote_mem_prefix, AIG.LawfulVecOperator.denote_mem_prefix]
      rw [hright]
    · simp only [RefVec.get_cast, Ref.cast_eq]
      intros
      rw [AIG.LawfulVecOperator.denote_mem_prefix, AIG.LawfulVecOperator.denote_mem_prefix,
        AIG.LawfulVecOperator.denote_mem_prefix, AIG.LawfulVecOperator.denote_mem_prefix,
        AIG.LawfulVecOperator.denote_mem_prefix]
      rw [denote_blastUdiv (lhs := lhs) (rhs := rhs)]
      · intros
        rw [AIG.LawfulVecOperator.denote_mem_prefix, AIG.LawfulVecOperator.denote_mem_prefix]
        · simp [hleft]
        · simp [Ref.hgate]
      · intros
        rw [AIG.LawfulVecOperator.denote_mem_prefix, AIG.LawfulVecOperator.denote_mem_prefix]
        · simp [hright]
        · simp [Ref.hgate]
    · simp only [RefVec.get_cast, Ref.cast_eq]
      intros
      rw [AIG.LawfulVecOperator.denote_mem_prefix, AIG.LawfulVecOperator.denote_mem_prefix,
        AIG.LawfulVecOperator.denote_mem_prefix]
      rw [denote_blastNeg (value := lhs / (-rhs))]
      intros
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
    · simp only [RefVec.get_cast, Ref.cast_eq]
      intros
      rw [AIG.LawfulVecOperator.denote_mem_prefix]
      rw [denote_blastNeg (value := (-lhs) / rhs)]
      intros
      rw [denote_blastUdiv (lhs := -lhs) (rhs := rhs)]
      · intros
        rw [AIG.LawfulVecOperator.denote_mem_prefix, AIG.LawfulVecOperator.denote_mem_prefix,
          AIG.LawfulVecOperator.denote_mem_prefix, AIG.LawfulVecOperator.denote_mem_prefix]
        · simp only [RefVec.get_cast, Ref.cast_eq]
          rw [denote_blastNeg (value := lhs)]
          simp [hleft]
        · simp [Ref.hgate]
      · intros
        rw [AIG.LawfulVecOperator.denote_mem_prefix, AIG.LawfulVecOperator.denote_mem_prefix,
          AIG.LawfulVecOperator.denote_mem_prefix, AIG.LawfulVecOperator.denote_mem_prefix,
          AIG.LawfulVecOperator.denote_mem_prefix]
        · simp [hright]
        · simp [Ref.hgate]
    · simp only
      intros
      rw [denote_blastUdiv (lhs := -lhs) (rhs := - rhs)]
      · intros
        simp only [RefVec.get_cast, Ref.cast_eq]
        rw [AIG.LawfulVecOperator.denote_mem_prefix, AIG.LawfulVecOperator.denote_mem_prefix,
          AIG.LawfulVecOperator.denote_mem_prefix, AIG.LawfulVecOperator.denote_mem_prefix,
          AIG.LawfulVecOperator.denote_mem_prefix, AIG.LawfulVecOperator.denote_mem_prefix]
        rw [denote_blastNeg (value := lhs)]
        simp [hleft]
      · intros
        simp only [RefVec.get_cast, Ref.cast_eq]
        rw [AIG.LawfulVecOperator.denote_mem_prefix, AIG.LawfulVecOperator.denote_mem_prefix,
          AIG.LawfulVecOperator.denote_mem_prefix, AIG.LawfulVecOperator.denote_mem_prefix,
          AIG.LawfulVecOperator.denote_mem_prefix]
        rw [denote_blastNeg (value := rhs)]
        intros
        rw [AIG.LawfulVecOperator.denote_mem_prefix]
        · simp [hright]
        · simp [Ref.hgate]


end bitblast
end BVExpr

end Std.Tactic.BVDecide
