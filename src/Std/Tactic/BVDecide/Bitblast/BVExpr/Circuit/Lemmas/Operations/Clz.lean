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

-- it 0

-- clzAuxRec x 0 = ite x[0] then w - 1 else w

-- if x[0] then w - 1 else acc ; acc = w

-- it 1
/-

clzAuxRec x 1 :

if x[1] then w - 1 - 1 else clzAuxRec x 0

if x[1] then w - 1 - 1 else acc; acc = if x[0] then w - 1 else w


clzAuxRec x n

if x[n] then w - 1 - n ; go aig x n acc s.t. acc = what clzAuxRec x (n - 1) produces
  else if x [n - 1] then w - 1 - (n - 1) ; go aig x (n - 1) acc s.t. acc = what clzAuxRec x (n - 2) produces
    else if x[n - 2] then w - 1 - (n - 2) ; go aig x (n - 2) acc s.t. acc = what clzAuxRec x (n - 3) produces
                                       ; go aig x 2 acc s.t. acc = what clzAuxRec x 1 produces
      ...                              ; go aig x 1 acc s.t. acc = what clzAuxRec x 0 produces
        else if x[0] then w - 1 else w ; go aig x 0 w

we phrase it the other way around:

go aig x i acc; where acc = clzAuxRec (i - 1) :=
  if i < w then
    ite x[i] then w - 1 - i else acc
    go aig x (i + 1) acc

-/


-- go aig x n acc = ite x[n] then (w - 1 - n) else acc
-- we prove that this is true for n = 0
-- we prove that under the hypothesis that this holds until n, it will hold until n + 1
-- circuit: when curr = 0 → ite x[0] then (w - 1) else acc, where acc is the rec. call
-- circuit: when curr = w - 1 → ite x[w - 1] then 0 else acc, where acc is a chain of ite nodes
-- the actual base case of the recursion is
-- acc[0] contains the ite node formed at curr = 0
-- acc n = ite curr [n]
theorem go_denote_base_eq {w : Nat} (aig : AIG α)
    (acc : AIG.RefVec aig w) (xc : AIG.RefVec aig w) (x : BitVec w) (assign : α → Bool)
    (hacc : ∀ (idx : Nat) (hidx : idx < w),
                ⟦aig, acc.get idx hidx, assign⟧
                  =
                (BitVec.clzAuxRec x (w - 1)).getLsbD idx) :
    ∀ (idx : Nat) (hidx : idx < w),
      ⟦(go aig xc w acc).aig, (go aig xc w acc).vec.get idx hidx, assign⟧ =
        (BitVec.clzAuxRec x (w - 1)).getLsbD idx := by
    intro idx hidx
    generalize hgo0 : go aig xc w acc = res
    unfold go at hgo0
    split at hgo0
    · omega
    · rw [← hgo0]
      simp [hacc]

theorem go_denote_eq {w : Nat} (aig : AIG α)
    (acc : AIG.RefVec aig w) (xc : AIG.RefVec aig w) (x : BitVec w) (assign : α → Bool)
    -- correctness of the denotation for blastConst and w
    -- (hw : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, (blastConst aig (BitVec.ofNat w w)).get idx hidx, assign⟧ = (BitVec.ofNat w w).getLsbD idx)
    -- correctness of the denotation for x and xexpr
    (hx : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, xc.get idx hidx, assign⟧ = x.getLsbD idx)
    -- correctness of the denotation for the accumulator
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
    · -- curr < w
      case isTrue h =>
        simp at hgo
        rw [← hgo]
        rw [go_denote_eq]
        · intro idx hidx
          rw [AIG.LawfulVecOperator.denote_mem_prefix (f := RefVec.ite)]
          simp [hx]
          simp [Ref.hgate]
        · intro  idx hidx
          simp only [Nat.add_eq_zero, Nat.succ_ne_self, and_false, ↓reduceIte, RefVec.get_cast,
            Ref.cast_eq, Nat.add_one_sub_one]
          rcases curr
          · case zero =>
            sorry
          · case succ n =>
            sorry
    · case isFalse h =>
      rw [← hgo]
      simp [show w ≤ curr by omega, show ¬ curr = 0 by omega] at hacc
      simp [hacc]
      by_cases hcw : curr = w
      · subst hcw; rfl
      · rw [BitVec.clzAuxRec_eq_of_le]
        omega

end blastClz

@[simp]
theorem denote_blastClz (aig : AIG α) (xc : RefVec aig w) (x : BitVec w) (assign : α → Bool)
      (hx : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, xc.get idx hidx, assign⟧ = x.getLsbD idx)
      (hw : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, (blastConst aig (BitVec.ofNat w w)).get idx hidx, assign⟧ = (BitVec.ofNat w w).getLsbD idx)
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
    simp only [↓reduceIte, BitVec.natCast_eq_ofNat, hw]

end bitblast
end BVExpr

end Std.Tactic.BVDecide
