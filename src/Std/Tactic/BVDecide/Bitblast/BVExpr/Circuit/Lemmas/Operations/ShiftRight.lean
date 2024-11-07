/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Basic
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.ShiftRight

/-!
This module contains the verification of the bitblasters for `BitVec.shiftRight` from
`Impl.Operations.ShiftRight`.
-/

namespace Std.Tactic.BVDecide

open Std.Sat
open Std.Sat.AIG

namespace BVExpr
namespace bitblast

variable [Hashable α] [DecidableEq α]

namespace blastShiftRightConst

theorem go_get_aux (aig : AIG α) (distance : Nat) (input : AIG.RefVec aig w)
    (curr : Nat) (hcurr : curr ≤ w) (s : AIG.RefVec aig curr) :
    ∀ (idx : Nat) (hidx : idx < curr) (hfoo),
        (go aig input distance curr hcurr s).vec.get idx (by omega)
          =
        (s.get idx hidx).cast hfoo := by
  intro idx hidx
  generalize hgo : go aig input distance curr hcurr s = res
  unfold go at hgo
  split at hgo
  · dsimp only at hgo
    split at hgo
    · rw [← hgo]
      intros
      rw [go_get_aux]
      rw [AIG.RefVec.get_push_ref_lt]
    · rw [← hgo]
      intros
      rw [go_get_aux]
      rw [AIG.RefVec.get_push_ref_lt]
      · simp only [Ref.cast, Ref.mk.injEq]
        rw [AIG.RefVec.get_cast]
        · simp
        · assumption
      · apply go_le_size
  · dsimp only at hgo
    rw [← hgo]
    simp only [Nat.le_refl, get, Ref.gate_cast, Ref.mk.injEq, true_implies]
    obtain rfl : curr = w := by omega
    simp
termination_by w - curr

theorem go_get (aig : AIG α) (distance : Nat) (input : AIG.RefVec aig w)
    (curr : Nat) (hcurr : curr ≤ w) (s : AIG.RefVec aig curr) :
    ∀ (idx : Nat) (hidx : idx < curr),
        (go aig input distance curr hcurr s).vec.get idx (by omega)
          =
        (s.get idx hidx).cast (by apply go_le_size) := by
  intros
  apply go_get_aux

theorem go_denote_mem_prefix (aig : AIG α) (distance : Nat) (input : AIG.RefVec aig w)
    (curr : Nat) (hcurr : curr ≤ w) (s : AIG.RefVec aig curr) (start : Nat) (hstart) :
    ⟦
      (go aig input distance curr hcurr s).aig,
      ⟨start, by apply Nat.lt_of_lt_of_le; exact hstart; apply go_le_size⟩,
      assign
    ⟧
      =
    ⟦aig, ⟨start, hstart⟩, assign⟧ := by
  apply denote.eq_of_isPrefix (entry := ⟨aig, start,hstart⟩)
  apply IsPrefix.of
  · intros
    apply go_decl_eq
  · intros
    apply go_le_size

theorem go_denote_eq (aig : AIG α) (distance : Nat) (input : AIG.RefVec aig w)
    (assign : α → Bool) (curr : Nat) (hcurr : curr ≤ w) (s : AIG.RefVec aig curr) :
    ∀ (idx : Nat) (hidx1 : idx < w),
        curr ≤ idx
          →
        ⟦
          (go aig input distance curr hcurr s).aig,
          (go aig input distance curr hcurr s).vec.get idx hidx1,
          assign
        ⟧
          =
        if hidx : (distance + idx) < w then
          ⟦aig, input.get (distance + idx) (by omega), assign⟧
        else
          false
        := by
  intro idx hidx1 hidx2
  generalize hgo : go aig input distance curr hcurr s = res
  unfold go at hgo
  split at hgo
  · dsimp only at hgo
    cases Nat.eq_or_lt_of_le hidx2 with
    | inl heq =>
      split at hgo
      · split
        · rw [← hgo]
          rw [go_get]
          rw [AIG.RefVec.get_push_ref_eq']
          · rw [go_denote_mem_prefix]
            · simp [heq]
            · simp [Ref.hgate]
          · rw [heq]
        · omega
      · split
        · omega
        · rw [← hgo]
          rw [go_get]
          rw [AIG.RefVec.get_push_ref_eq']
          · rw [go_denote_mem_prefix]
            · simp
            · simp [Ref.hgate]
          · rw [heq]
    | inr =>
      split at hgo
      · split
        all_goals
          next hidx =>
            rw [← hgo]
            rw [go_denote_eq]
            · simp [hidx]
            · omega
      · split
        · omega
        · next hidx =>
          rw [← hgo]
          rw [go_denote_eq]
          · simp [hidx]
          · omega
  · omega
termination_by w - curr

end blastShiftRightConst

@[simp]
theorem denote_blastShiftRightConst (aig : AIG α) (target : ShiftTarget aig w)
    (assign : α → Bool) :
    ∀ (idx : Nat) (hidx : idx < w),
        ⟦
          (blastShiftRightConst aig target).aig,
          (blastShiftRightConst aig target).vec.get idx hidx,
          assign
        ⟧
          =
        if hidx : (target.distance + idx) < w then
          ⟦aig, target.vec.get (target.distance + idx) (by omega), assign⟧
        else
          false
        := by
  intros
  unfold blastShiftRightConst
  apply blastShiftRightConst.go_denote_eq
  omega

namespace blastArithShiftRightConst

theorem go_get (aig : AIG α) (distance : Nat) (input : AIG.RefVec aig w)
    (curr : Nat) (hcurr : curr ≤ w) (s : AIG.RefVec aig curr) :
    ∀ (idx : Nat) (hidx : idx < curr),
        (go input distance curr hcurr s).get idx (by omega)
          =
        s.get idx hidx := by
  intro idx hidx
  unfold go
  split
  · split
    all_goals
      rw [go_get]
      rw [AIG.RefVec.get_push_ref_lt]
  · simp only [get, Ref.mk.injEq]
    have : curr = w := by omega
    subst this
    simp

theorem go_denote_eq (aig : AIG α) (distance : Nat) (input : AIG.RefVec aig w)
    (assign : α → Bool) (curr : Nat) (hcurr : curr ≤ w) (s : AIG.RefVec aig curr) :
    ∀ (idx : Nat) (hidx1 : idx < w),
        curr ≤ idx
          →
        ⟦
          aig,
          (go input distance curr hcurr s).get idx hidx1,
          assign
        ⟧
          =
        if hidx : (distance + idx) < w then
          ⟦aig, input.get (distance + idx) (by omega), assign⟧
        else
          ⟦aig, input.get (w - 1) (by omega), assign⟧
        := by
  intro idx hidx1 hidx2
  generalize hgo : go input distance curr hcurr s = res
  unfold go at hgo
  split at hgo
  · cases Nat.eq_or_lt_of_le hidx2 with
    | inl heq =>
      split at hgo
      · next hlt =>
        rw [heq] at hlt
        simp only [hlt, ↓reduceDIte]
        dsimp only at hgo
        rw [← hgo]
        rw [go_get]
        rw [AIG.RefVec.get_push_ref_eq']
        · simp [heq]
        · omega
      · next hlt =>
        rw [heq] at hlt
        simp only [hlt, ↓reduceDIte]
        dsimp only at hgo
        rw [← hgo]
        rw [go_get]
        rw [AIG.RefVec.get_push_ref_eq']
        · simp [heq]
    | inr =>
      split at hgo
      all_goals
        split
        all_goals
          next hidx =>
            rw [← hgo]
            rw [go_denote_eq]
            · simp [hidx]
            · omega
  · omega

end blastArithShiftRightConst

@[simp]
theorem denote_blastArithShiftRightConst (aig : AIG α) (target : ShiftTarget aig w)
    (assign : α → Bool) :
    ∀ (idx : Nat) (hidx : idx < w),
        ⟦
          (blastArithShiftRightConst aig target).aig,
          (blastArithShiftRightConst aig target).vec.get idx hidx,
          assign
        ⟧
          =
        if hidx : (target.distance + idx) < w then
          ⟦aig, target.vec.get (target.distance + idx) (by omega), assign⟧
        else
          ⟦aig, target.vec.get (w - 1) (by omega), assign⟧
        := by
  intros
  unfold blastArithShiftRightConst
  rw [blastArithShiftRightConst.go_denote_eq]
  omega

namespace blastShiftRight

theorem twoPowShift_eq (aig : AIG α) (target : TwoPowShiftTarget aig w) (lhs : BitVec w)
    (rhs : BitVec target.n) (assign : α → Bool)
    (hleft : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, target.lhs.get idx hidx, assign⟧ = lhs.getLsbD idx)
    (hright : ∀ (idx : Nat) (hidx : idx < target.n), ⟦aig, target.rhs.get idx hidx, assign⟧ = rhs.getLsbD idx) :
    ∀ (idx : Nat) (hidx : idx < w),
        ⟦
          (twoPowShift aig target).aig,
          (twoPowShift aig target).vec.get idx hidx,
          assign
        ⟧
          =
        (lhs >>> (rhs &&& BitVec.twoPow target.n target.pow)).getLsbD idx := by
  intro idx hidx
  generalize hg : twoPowShift aig target = res
  rcases target with ⟨n, lvec, rvec, pow⟩
  simp only [BitVec.and_twoPow]
  unfold twoPowShift at hg
  dsimp only at hg
  split at hg
  · split
    · next hif1 =>
      rw [← hg]
      simp only [RefVec.denote_ite, RefVec.get_cast, Ref.cast_eq,
        denote_blastShiftRightConst]
      rw [AIG.LawfulVecOperator.denote_mem_prefix (f := blastShiftRightConst)]
      rw [hright]
      simp only [hif1, ↓reduceIte]
      have hmod : 2 ^ pow % 2 ^ n = 2 ^ pow := by
        apply Nat.mod_eq_of_lt
        apply Nat.pow_lt_pow_of_lt <;> omega
      split
      · rw [hleft]
        simp [hmod]
      · simp only [BitVec.ushiftRight_eq', BitVec.toNat_twoPow, BitVec.getLsbD_ushiftRight,
        Bool.false_eq]
        apply BitVec.getLsbD_ge
        omega
    · next hif1 =>
      simp only [Bool.not_eq_true] at hif1
      rw [← hg]
      simp only [RefVec.denote_ite, RefVec.get_cast, Ref.cast_eq,
        denote_blastShiftRightConst]
      rw [AIG.LawfulVecOperator.denote_mem_prefix (f := blastShiftRightConst)]
      rw [hright]
      simp only [hif1, Bool.false_eq_true, ↓reduceIte]
      rw [AIG.LawfulVecOperator.denote_mem_prefix (f := blastShiftRightConst)]
      rw [hleft]
      simp
  · have : rhs.getLsbD pow = false := by
      apply BitVec.getLsbD_ge
      dsimp only
      omega
    simp only [this, Bool.false_eq_true, ↓reduceIte]
    rw [← hg]
    rw [hleft]
    simp

theorem go_denote_eq (aig : AIG α) (distance : AIG.RefVec aig n) (curr : Nat)
      (hcurr : curr ≤ n - 1) (acc : AIG.RefVec aig w)
    (lhs : BitVec w) (rhs : BitVec n) (assign : α → Bool)
    (hacc : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, acc.get idx hidx, assign⟧ = (BitVec.ushiftRightRec lhs rhs curr).getLsbD idx)
    (hright : ∀ (idx : Nat) (hidx : idx < n), ⟦aig, distance.get idx hidx, assign⟧ = rhs.getLsbD idx) :
    ∀ (idx : Nat) (hidx : idx < w),
        ⟦
          (go aig distance curr acc).aig,
          (go aig distance curr acc).vec.get idx hidx,
          assign
        ⟧
          =
        (BitVec.ushiftRightRec lhs rhs (n - 1)).getLsbD idx := by
  intro idx hidx
  generalize hgo : go aig distance curr acc = res
  unfold go at hgo
  dsimp only at hgo
  split at hgo
  · rw [← hgo]
    rw [go_denote_eq]
    · omega
    · intro idx hidx
      simp only [BitVec.ushiftRightRec_succ]
      rw [twoPowShift_eq (lhs := BitVec.ushiftRightRec lhs rhs curr)]
      · simp [hacc]
      · simp [hright]
    · intro idx hidx
      rw [AIG.LawfulVecOperator.denote_mem_prefix (f := twoPowShift)]
      · simp [hright]
      · simp [Ref.hgate]
  · have : curr = n - 1 := by omega
    rw [← hgo]
    simp [hacc, this]
termination_by n - 1 - curr

end blastShiftRight

theorem denote_blastShiftRight (aig : AIG α) (target : ArbitraryShiftTarget aig w0)
    (lhs : BitVec w0) (rhs : BitVec target.n) (assign : α → Bool)
    (hleft : ∀ (idx : Nat) (hidx : idx < w0), ⟦aig, target.target.get idx hidx, assign⟧ = lhs.getLsbD idx)
    (hright : ∀ (idx : Nat) (hidx : idx < target.n), ⟦aig, target.distance.get idx hidx, assign⟧ = rhs.getLsbD idx) :
    ∀ (idx : Nat) (hidx : idx < w0),
        ⟦
          (blastShiftRight aig target).aig,
          (blastShiftRight aig target).vec.get idx hidx,
          assign
        ⟧
          =
        (lhs >>> rhs).getLsbD idx := by
  intro idx hidx
  rw [BitVec.shiftRight_eq_ushiftRightRec]
  generalize hres : blastShiftRight aig target = res
  rcases target with ⟨n, target, distance⟩
  unfold blastShiftRight at hres
  dsimp only at hres
  split at hres
  · next hzero =>
    dsimp only
    subst hzero
    rw [← hres]
    simp [hleft, BitVec.and_twoPow]
  · rw [← hres]
    rw [blastShiftRight.go_denote_eq]
    · omega
    · intro idx hidx
      simp only [BitVec.ushiftRightRec_zero]
      rw [blastShiftRight.twoPowShift_eq]
      · simp [hleft]
      · simp [hright]
    · intros
      rw [AIG.LawfulVecOperator.denote_mem_prefix (f := blastShiftRight.twoPowShift)]
      · simp [hright]
      · simp [Ref.hgate]

namespace blastArithShiftRight

theorem twoPowShift_eq (aig : AIG α) (target : TwoPowShiftTarget aig w) (lhs : BitVec w)
    (rhs : BitVec target.n) (assign : α → Bool)
    (hleft : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, target.lhs.get idx hidx, assign⟧ = lhs.getLsbD idx)
    (hright : ∀ (idx : Nat) (hidx : idx < target.n), ⟦aig, target.rhs.get idx hidx, assign⟧ = rhs.getLsbD idx) :
    ∀ (idx : Nat) (hidx : idx < w),
        ⟦
          (twoPowShift aig target).aig,
          (twoPowShift aig target).vec.get idx hidx,
          assign
        ⟧
          =
        (BitVec.sshiftRight' lhs (rhs &&& BitVec.twoPow target.n target.pow)).getLsbD idx := by
  intro idx hidx
  generalize hg : twoPowShift aig target = res
  rcases target with ⟨n, lvec, rvec, pow⟩
  simp only [BitVec.and_twoPow]
  unfold twoPowShift at hg
  dsimp only at hg
  split at hg
  · split
    · next hif1 =>
      rw [← hg]
      simp only [RefVec.denote_ite, RefVec.get_cast, Ref.cast_eq,
        denote_blastArithShiftRightConst]
      rw [AIG.LawfulVecOperator.denote_mem_prefix (f := blastArithShiftRightConst)]
      rw [hright]
      simp only [hif1, ↓reduceIte]
      have hmod : 2 ^ pow % 2 ^ n = 2 ^ pow := by
        apply Nat.mod_eq_of_lt
        apply Nat.pow_lt_pow_of_lt <;> omega
      split
      · next hlt =>
        rw [hleft]
        simp [hmod, BitVec.getLsbD_sshiftRight, hlt, hidx]
      · next hlt =>
        rw [hleft]
        simp [BitVec.getLsbD_sshiftRight, hmod, hlt, hidx, BitVec.msb_eq_getLsbD_last]
    · next hif1 =>
      simp only [Bool.not_eq_true] at hif1
      rw [← hg]
      simp only [RefVec.denote_ite, RefVec.get_cast, Ref.cast_eq,
        denote_blastArithShiftRightConst]
      rw [AIG.LawfulVecOperator.denote_mem_prefix (f := blastArithShiftRightConst)]
      rw [hright]
      simp only [hif1, Bool.false_eq_true, ↓reduceIte]
      rw [AIG.LawfulVecOperator.denote_mem_prefix (f := blastArithShiftRightConst)]
      rw [hleft]
      simp
  · have : rhs.getLsbD pow = false := by
      apply BitVec.getLsbD_ge
      dsimp only
      omega
    simp only [this, Bool.false_eq_true, ↓reduceIte]
    rw [← hg]
    rw [hleft]
    simp

theorem go_denote_eq (aig : AIG α) (distance : AIG.RefVec aig n) (curr : Nat)
      (hcurr : curr ≤ n - 1) (acc : AIG.RefVec aig w)
    (lhs : BitVec w) (rhs : BitVec n) (assign : α → Bool)
    (hacc : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, acc.get idx hidx, assign⟧ = (BitVec.sshiftRightRec lhs rhs curr).getLsbD idx)
    (hright : ∀ (idx : Nat) (hidx : idx < n), ⟦aig, distance.get idx hidx, assign⟧ = rhs.getLsbD idx) :
    ∀ (idx : Nat) (hidx : idx < w),
        ⟦
          (go aig distance curr acc).aig,
          (go aig distance curr acc).vec.get idx hidx,
          assign
        ⟧
          =
        (BitVec.sshiftRightRec lhs rhs (n - 1)).getLsbD idx := by
  intro idx hidx
  generalize hgo : go aig distance curr acc = res
  unfold go at hgo
  dsimp only at hgo
  split at hgo
  · rw [← hgo]
    rw [go_denote_eq]
    · omega
    · intro idx hidx
      simp only [BitVec.sshiftRightRec_succ_eq]
      rw [twoPowShift_eq (lhs := BitVec.sshiftRightRec lhs rhs curr)]
      · simp [hacc]
      · simp [hright]
    · intro idx hidx
      rw [AIG.LawfulVecOperator.denote_mem_prefix (f := twoPowShift)]
      · simp [hright]
      · simp [Ref.hgate]
  · have : curr = n - 1 := by omega
    rw [← hgo]
    simp [hacc, this]
termination_by n - 1 - curr

end blastArithShiftRight

theorem denote_blastArithShiftRight (aig : AIG α) (target : ArbitraryShiftTarget aig w0)
    (lhs : BitVec w0) (rhs : BitVec target.n) (assign : α → Bool)
    (hleft : ∀ (idx : Nat) (hidx : idx < w0), ⟦aig, target.target.get idx hidx, assign⟧ = lhs.getLsbD idx)
    (hright : ∀ (idx : Nat) (hidx : idx < target.n), ⟦aig, target.distance.get idx hidx, assign⟧ = rhs.getLsbD idx) :
    ∀ (idx : Nat) (hidx : idx < w0),
        ⟦
          (blastArithShiftRight aig target).aig,
          (blastArithShiftRight aig target).vec.get idx hidx,
          assign
        ⟧
          =
        (BitVec.sshiftRight' lhs rhs).getLsbD idx := by
  intro idx hidx
  rw [BitVec.sshiftRight_eq_sshiftRightRec]
  generalize hres : blastArithShiftRight aig target = res
  rcases target with ⟨n, target, distance⟩
  unfold blastArithShiftRight at hres
  dsimp only at hres
  split at hres
  · next hzero =>
    dsimp only
    subst hzero
    rw [← hres]
    simp [hleft, BitVec.and_twoPow]
  · rw [← hres]
    rw [blastArithShiftRight.go_denote_eq]
    · omega
    · intro idx hidx
      simp only [BitVec.sshiftRightRec_zero_eq]
      rw [blastArithShiftRight.twoPowShift_eq]
      · simp [hleft]
      · simp [hright]
    · intros
      rw [AIG.LawfulVecOperator.denote_mem_prefix (f := blastArithShiftRight.twoPowShift)]
      · simp [hright]
      · simp [Ref.hgate]

end bitblast
end BVExpr

end Std.Tactic.BVDecide
