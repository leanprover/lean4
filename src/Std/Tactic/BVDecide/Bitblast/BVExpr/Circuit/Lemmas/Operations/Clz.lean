/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luisa Cicolini, Siddharth Bhat, Henrik Böving
-/
prelude
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Basic
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Clz
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Const

/-!
This module contains the verification of the bitblaster for `BitVec.clz` from
`Impl.Operations.Clz`. We prove that the accumulator of the `go` function
at step`n` represents the portion of the `ite` nodes in the AIG constructed for
bits `0` until `n`.
-/

namespace Std.Tactic.BVDecide

open Std.Sat
open Std.Sat.AIG

variable [Hashable α] [DecidableEq α]

namespace BVExpr

namespace bitblast
namespace blastClz

example (x : Nat) (hx : 0 < x) : ∃ y, x = y + 1 := by
  exact Nat.exists_eq_add_one.mpr hx

theorem go_denote_eq {w : Nat} (aig : AIG α)
    (acc : AIG.RefVec aig w) (xc : AIG.RefVec aig w) (x : BitVec w) (assign : α → Bool)
    (hx : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, xc.get idx hidx, assign⟧ = x.getLsbD idx)
    (hacc : ∀ (idx : Nat) (hidx : idx < w),
      if curr = 0 then ⟦aig, acc.get idx hidx, assign⟧ = (BitVec.ofNat w w).getLsbD idx
      else ⟦aig, acc.get idx hidx, assign⟧ = (BitVec.clzAuxRec x (curr - 1)).getLsbD idx)
    :
    ∀ (idx : Nat) (hidx : idx < w),
        ⟦
          (go aig xc curr acc).aig,
          (go aig xc curr acc).vec.get idx hidx,
          assign
        ⟧
          =
        (BitVec.clzAuxRec x (w - 1)).getLsbD idx := by
    intro idx hidx
    generalize hgo: go aig xc curr acc = res
    unfold go at hgo
    split at hgo
    · case isTrue h =>
        simp only [BitVec.natCast_eq_ofNat, BitVec.ofNat_eq_ofNat] at hgo
        rw [← hgo, go_denote_eq]
        · intro idx hidx
          rw [AIG.LawfulVecOperator.denote_mem_prefix (f := RefVec.ite)]
          · simp [hx]
          · simp [Ref.hgate]
        · intro idx hidx
          simp only [Nat.add_eq_zero, Nat.succ_ne_self, and_false, reduceIte, 
            Nat.add_one_sub_one]
          rw [RefVec.denote_ite]
          split
          · next h =>
            rw [hx] at h
            have : 1 < 2 ^ w := by exact Nat.one_lt_two_pow_iff.mpr (by omega)
            rcases curr with _|curr
            · simp [denote_blastConst, BitVec.clzAuxRec_zero, h, BitVec.ofNat_sub_ofNat_of_le (x := w) (y := 1) (by omega) (by omega)]
            · have := Nat.lt_pow_self (n := curr + 1) (a := 2) (by omega)
              have := Nat.pow_lt_pow_of_lt (a := 2) (n := curr + 1) (m := w) (by omega) (by omega)
              simp only [denote_blastConst, BitVec.clzAuxRec_succ, h, reduceIte]
              rw [BitVec.ofNat_sub_ofNat_of_le (x := w) (y := 1) (by omega) (by omega),
                  BitVec.ofNat_sub_ofNat_of_le (x := w - 1) (y := curr + 1) (by omega) (by omega)]
          · split at hacc
            · next h1 h2 =>
              have hxc : x.getLsbD 0 = false := by rw [hx] at h1; simp [h2] at h1; exact h1
              simp [hacc, h2, BitVec.clzAuxRec_zero, hxc]
            · next h1 h2 =>
              obtain ⟨curr, hcurr⟩ : ∃ curr', curr = curr' + 1 := by apply Nat.exists_eq_add_one.mpr (by omega)
              subst hcurr
              have hxc : x.getLsbD (curr + 1) = false := by rw [hx] at h1; simp at h1; exact h1
              simp [hacc, BitVec.clzAuxRec_succ, hxc]
    · case isFalse h =>
      rw [← hgo]
      simp only [show ¬curr = 0 by omega, reduceIte] at hacc
      simp only [hacc, BitVec.clzAuxRec_eq_clzAuxRec_of_le (x := x) (n := curr - 1) (by omega)]

end blastClz

@[simp]
theorem denote_blastClz (aig : AIG α) (xc : RefVec aig w) (x : BitVec w) (assign : α → Bool)
      (hx : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, xc.get idx hidx, assign⟧ = x.getLsbD idx)
      :
      ∀ (idx : Nat) (hidx : idx < w),
        ⟦(blastClz aig xc).aig, (blastClz aig xc).vec.get idx hidx, assign⟧
          =
        (BitVec.clzAuxRec x (w - 1)).getLsbD idx := by
  intro idx hidx
  generalize hb : blastClz aig xc = res
  unfold blastClz at hb
  dsimp only at hb
  rw [← hb, blastClz.go_denote_eq (x := x) (w := w)]
  · exact hx
  · intro idx hidx
    simp only [reduceIte, BitVec.natCast_eq_ofNat]
    rw [denote_blastConst]

end bitblast
end BVExpr

end Std.Tactic.BVDecide
