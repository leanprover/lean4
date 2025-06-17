/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luisa Cicolini, Siddharth Bhat, Henrik Böving
-/
prelude
import Init.Data.BitVec.Bitblast
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
          simp only [Nat.add_eq_zero, Nat.succ_ne_self, and_false, reduceIte, RefVec.get_cast,
            Ref.cast_eq, Nat.add_one_sub_one]
          rw [RefVec.denote_ite]
          rcases curr with _|curr
          · split
            · next hx' =>
              have hx0 : x.getLsbD 0 = true := by rw [hx] at hx'; exact hx'
              have : 1 < 2 ^ w := by exact Nat.one_lt_two_pow_iff.mpr (by omega)
              simp only [BitVec.sub_zero, denote_blastConst, BitVec.clzAuxRec, hx0, reduceIte]
              congr
              rw [BitVec.toNat_eq, BitVec.ofNat_sub_ofNat, Nat.mod_eq_of_lt (by omega),
                show 2 ^ w - 1 + w = 2 ^ w + (w - 1) by omega]
              simp only [BitVec.toNat_ofNat, Nat.add_mod_left]
            · next hx' =>
              have hx0 : x.getLsbD 0 = false := by rw [hx, Bool.not_eq_true] at hx'; exact hx'
              simp only [reduceIte] at hacc
              simp [BitVec.clzAuxRec, hx0, hacc]
          · split
            · next hx' =>
              have hxc : x.getLsbD (curr + 1) = true := by rw [hx] at hx'; exact hx'
              have := Nat.lt_pow_self (n := curr + 1) (a := 2) (by omega)
              have := Nat.pow_lt_pow_of_lt (a := 2) (n := curr + 1) (m := w) (by omega) (by omega)
              simp only [denote_blastConst,BitVec.clzAuxRec, hxc, reduceIte]
              congr
              simp only [BitVec.ofNat_sub_ofNat, Nat.zero_lt_succ, Nat.one_mod_two_pow,
                Nat.add_one_sub_one]
              rw [BitVec.toNat_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := curr + 1) (by omega),
                Nat.mod_eq_of_lt (a := 1) (by omega),
                show 2 ^ w - (curr + 1) + (2 ^ w - 1 + w) = (2 ^ w) + (2 ^ w + (w - curr - 1 - 1)) by omega]
              simp [Nat.add_mod_left, Nat.sub_add_eq, Nat.sub_right_comm]
            · next hx' =>
              simp only [Nat.add_eq_zero, Nat.succ_ne_self, and_false, reduceIte,
                Nat.add_one_sub_one] at hacc
              simp [hacc, BitVec.clzAuxRec, show x.getLsbD (curr + 1) = false by rw [hx] at hx'; simp at hx'; exact hx']
    · case isFalse h =>
      rw [← hgo]
      simp only [show ¬curr = 0 by omega, reduceIte] at hacc
      simp [hacc,
        ← BitVec.clz_eq_clzAuxRec_of_le (x := x) (n := curr - 1) (by omega),
        ← BitVec.clz_eq_clzAuxRec_of_le (x := x) (n := w - 1) (by omega)]

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
