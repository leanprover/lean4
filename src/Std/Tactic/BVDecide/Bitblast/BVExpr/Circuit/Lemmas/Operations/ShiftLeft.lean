/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Basic
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.ShiftLeft

/-!
This module contains the verification of the bitblasters for `BitVec.shiftLeft` from
`Impl.Operations.ShiftLeft`.
-/

namespace Std.Tactic.BVDecide

open Std.Sat
open Std.Sat.AIG

namespace BVExpr
namespace bitblast

variable [Hashable α] [DecidableEq α]

namespace blastShiftLeftConst

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
      · simp only [Ref.cast, Ref.mk.injEq]
        rw [AIG.RefVec.get_cast]
        · simp
        · assumption
      · apply go_le_size
    · rw [← hgo]
      intros
      rw [go_get_aux]
      rw [AIG.RefVec.get_push_ref_lt]
  · dsimp only at hgo
    rw [← hgo]
    simp only [Nat.le_refl, get, Ref.gate_cast, Ref.mk.injEq, true_implies]
    obtain rfl : curr = w := by omega
    simp
termination_by w - curr

theorem go_get (aig : AIG α) (distance : Nat) (input : AIG.RefVec aig w) (curr : Nat)
    (hcurr : curr ≤ w) (s : AIG.RefVec aig curr) :
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
        if hidx : idx < distance then
          false
        else
          ⟦aig, input.get (idx - distance) (by omega), assign⟧
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
            · simp
            · simp [Ref.hgate]
          · rw [heq]
        · omega
      · split
        · omega
        · rw [← hgo]
          rw [go_get]
          rw [AIG.RefVec.get_push_ref_eq']
          · rw [go_denote_mem_prefix]
            · simp [heq]
            · simp [Ref.hgate]
          · rw [heq]
    | inr =>
      split at hgo
      · split
        · next hidx =>
          rw [← hgo]
          rw [go_denote_eq]
          · simp [hidx]
          · omega
        · next hidx =>
          rw [← hgo]
          rw [go_denote_eq]
          · simp only [hidx, ↓reduceDIte, RefVec.get_cast, Ref.cast_eq]
            rw [AIG.LawfulOperator.denote_mem_prefix (f := AIG.mkConstCached)]
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

end blastShiftLeftConst

@[simp]
theorem denote_blastShiftLeftConst (aig : AIG α) (target : ShiftTarget aig w)
    (assign : α → Bool) :
    ∀ (idx : Nat) (hidx : idx < w),
        ⟦
          (blastShiftLeftConst aig target).aig,
          (blastShiftLeftConst aig target).vec.get idx hidx,
          assign
        ⟧
          =
        if hidx : idx < target.distance then
          false
        else
          ⟦aig, target.vec.get (idx - target.distance) (by omega), assign⟧
        := by
  intros
  unfold blastShiftLeftConst
  apply blastShiftLeftConst.go_denote_eq
  omega

namespace blastShiftLeft

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
        (lhs <<< (rhs &&& BitVec.twoPow target.n target.pow)).getLsbD idx := by
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
        denote_blastShiftLeftConst]
      rw [AIG.LawfulVecOperator.denote_mem_prefix (f := blastShiftLeftConst)]
      rw [hright]
      simp only [hif1, ↓reduceIte]
      have hmod : 2 ^ pow % 2 ^ n = 2 ^ pow := by
        apply Nat.mod_eq_of_lt
        apply Nat.pow_lt_pow_of_lt <;> omega
      split
      · simp only [BitVec.shiftLeft_eq', BitVec.toNat_twoPow, BitVec.getLsbD_shiftLeft,
        Bool.false_eq, Bool.and_eq_false_imp, Bool.and_eq_true, decide_eq_true_eq,
        Bool.not_eq_true', decide_eq_false_iff_not, Nat.not_lt, and_imp]
        intros
        apply BitVec.getLsbD_ge
        omega
      · rw [hleft]
        simp only [BitVec.shiftLeft_eq', BitVec.toNat_twoPow, hmod, BitVec.getLsbD_shiftLeft, hidx,
          decide_true, Bool.true_and, Bool.iff_and_self, Bool.not_eq_true', decide_eq_false_iff_not,
          Nat.not_lt]
        omega
    · next hif1 =>
      simp only [Bool.not_eq_true] at hif1
      rw [← hg]
      simp only [RefVec.denote_ite, RefVec.get_cast, Ref.cast_eq,
        denote_blastShiftLeftConst]
      rw [AIG.LawfulVecOperator.denote_mem_prefix (f := blastShiftLeftConst)]
      rw [hright]
      simp only [hif1, Bool.false_eq_true, ↓reduceIte]
      rw [AIG.LawfulVecOperator.denote_mem_prefix (f := blastShiftLeftConst)]
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
    (hacc : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, acc.get idx hidx, assign⟧ = (BitVec.shiftLeftRec lhs rhs curr).getLsbD idx)
    (hright : ∀ (idx : Nat) (hidx : idx < n), ⟦aig, distance.get idx hidx, assign⟧ = rhs.getLsbD idx) :
    ∀ (idx : Nat) (hidx : idx < w),
        ⟦
          (go aig distance curr acc).aig,
          (go aig distance curr acc).vec.get idx hidx,
          assign
        ⟧
          =
        (BitVec.shiftLeftRec lhs rhs (n - 1)).getLsbD idx := by
  intro idx hidx
  generalize hgo : go aig distance curr acc = res
  unfold go at hgo
  dsimp only at hgo
  split at hgo
  · rw [← hgo]
    rw [go_denote_eq]
    · omega
    · intro idx hidx
      simp only [BitVec.shiftLeftRec_succ]
      rw [twoPowShift_eq (lhs := BitVec.shiftLeftRec lhs rhs curr)]
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

end blastShiftLeft

theorem denote_blastShiftLeft (aig : AIG α) (target : ArbitraryShiftTarget aig w0)
    (lhs : BitVec w0) (rhs : BitVec target.n) (assign : α → Bool)
    (hleft : ∀ (idx : Nat) (hidx : idx < w0), ⟦aig, target.target.get idx hidx, assign⟧ = lhs.getLsbD idx)
    (hright : ∀ (idx : Nat) (hidx : idx < target.n), ⟦aig, target.distance.get idx hidx, assign⟧ = rhs.getLsbD idx) :
    ∀ (idx : Nat) (hidx : idx < w0),
        ⟦
          (blastShiftLeft aig target).aig,
          (blastShiftLeft aig target).vec.get idx hidx,
          assign
        ⟧
          =
        (lhs <<< rhs).getLsbD idx := by
  intro idx hidx
  rw [BitVec.shiftLeft_eq_shiftLeftRec]
  generalize hg : blastShiftLeft aig target = res
  rcases target with ⟨n, target, distance⟩
  unfold blastShiftLeft at hg
  dsimp only at hg
  split at hg
  · next hzero =>
    dsimp only
    subst hzero
    rw [← hg]
    simp only [hleft, Nat.zero_sub, BitVec.shiftLeftRec_zero, BitVec.and_twoPow, Nat.le_refl,
      BitVec.getLsbD_ge, Bool.false_eq_true, ↓reduceIte, BitVec.reduceHShiftLeft',
      BitVec.getLsbD_shiftLeft, Nat.sub_zero, Bool.iff_and_self, Bool.and_eq_true, decide_eq_true_eq,
      Bool.not_eq_true', decide_eq_false_iff_not, Nat.not_lt, Nat.zero_le, and_true]
    apply BitVec.lt_of_getLsbD
  · rw [← hg]
    rw [blastShiftLeft.go_denote_eq]
    · omega
    · intro idx hidx
      simp only [BitVec.shiftLeftRec_zero]
      rw [blastShiftLeft.twoPowShift_eq]
      · simp [hleft]
      · simp [hright]
    · intros
      rw [AIG.LawfulVecOperator.denote_mem_prefix (f := blastShiftLeft.twoPowShift)]
      · simp [hright]
      · simp [Ref.hgate]

end bitblast
end BVExpr

end Std.Tactic.BVDecide
