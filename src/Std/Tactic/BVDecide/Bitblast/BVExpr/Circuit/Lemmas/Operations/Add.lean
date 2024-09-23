/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Basic
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Add

/-!
This module contains the verification of the `BitVec.add` bitblaster from `Impl.Operations.Add`.
-/

namespace Std.Tactic.BVDecide

open Std.Sat
open Std.Sat.AIG

namespace BVExpr
namespace bitblast

variable [Hashable α] [DecidableEq α]

namespace blastAdd

@[simp]
theorem denote_mkFullAdderOut (assign : α → Bool) (aig : AIG α) (input : FullAdderInput aig) :
    ⟦mkFullAdderOut aig input, assign⟧
      =
    ((⟦aig, input.lhs, assign⟧ ^^ ⟦aig, input.rhs, assign⟧) ^^ ⟦aig, input.cin, assign⟧)
    := by
  simp only [mkFullAdderOut, Ref.cast_eq, denote_mkXorCached, denote_projected_entry, Bool.bne_assoc,
    Bool.bne_left_inj]
  rw [LawfulOperator.denote_mem_prefix (f := mkXorCached)]

@[simp]
theorem denote_mkFullAdderCarry (assign : α → Bool) (aig : AIG α) (input : FullAdderInput aig) :
    ⟦mkFullAdderCarry aig input, assign⟧
      =
      ((⟦aig, input.lhs, assign⟧ ^^ ⟦aig, input.rhs, assign⟧) && ⟦aig, input.cin, assign⟧ ||
       ⟦aig, input.lhs, assign⟧ && ⟦aig, input.rhs, assign⟧)
    := by
  simp only [mkFullAdderCarry, Ref.cast_eq, Int.reduceNeg, denote_mkOrCached,
    LawfulOperator.denote_input_entry, denote_mkAndCached, denote_projected_entry',
    denote_mkXorCached, denote_projected_entry]
  congr 2
  · rw [LawfulOperator.denote_mem_prefix (f := mkXorCached) (h := input.cin.hgate)]
  · rw [LawfulOperator.denote_mem_prefix
        (f := mkAndCached)
        (h := by
          apply LawfulOperator.lt_size_of_lt_aig_size (f := mkXorCached)
          apply Ref.hgate),
      LawfulOperator.denote_mem_prefix (f := mkXorCached) (h := input.lhs.hgate)]
  · rw [
      LawfulOperator.denote_mem_prefix
        (f := mkAndCached)
        (h := by
          apply LawfulOperator.lt_size_of_lt_aig_size (f := mkXorCached)
          apply Ref.hgate),
      LawfulOperator.denote_mem_prefix (f := mkXorCached) (h := input.rhs.hgate)]

theorem mkFullAdder_denote_mem_prefix (aig : AIG α) (input : FullAdderInput aig) (start : Nat)
    (hstart) :
    ⟦
      (mkFullAdder aig input).aig,
      ⟨start, Nat.lt_of_lt_of_le hstart (FullAdderOutput.hle _)⟩,
      assign
    ⟧
      =
    ⟦aig, ⟨start, hstart⟩, assign⟧ := by
  unfold mkFullAdder
  dsimp only
  rw [AIG.LawfulOperator.denote_mem_prefix (f := mkFullAdderCarry)]
  rw [AIG.LawfulOperator.denote_mem_prefix (f := mkFullAdderOut)]

theorem go_denote_mem_prefix (aig : AIG α) (curr : Nat) (hcurr : curr ≤ w) (cin : Ref aig)
    (s : AIG.RefVec aig curr) (lhs rhs : AIG.RefVec aig w) (start : Nat) (hstart) :
    ⟦
      (go aig lhs rhs curr hcurr cin s).aig,
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

theorem go_get_aux (aig : AIG α) (curr : Nat) (hcurr : curr ≤ w) (cin : Ref aig)
    (s : AIG.RefVec aig curr) (lhs rhs : AIG.RefVec aig w) :
    -- `hfoo` makes it possible to `generalize` below. With a concrete proof term this
    -- `generalize` would produce a type incorrect term as the proof term would talk about
    -- a `go` application instead of the fresh variable.
    ∀ (idx : Nat) (hidx : idx < curr) (hfoo),
        (go aig lhs rhs curr hcurr cin s).vec.get idx (by omega)
          =
        (s.get idx hidx).cast hfoo := by
  intro idx hidx
  generalize hgo : go aig lhs rhs curr hcurr cin s = res
  unfold go at hgo
  dsimp only at hgo
  split at hgo
  · rw [← hgo]
    intro hfoo
    rw [go_get_aux]
    rw [AIG.RefVec.get_push_ref_lt]
    · simp only [Ref.cast, Ref.mk.injEq]
      rw [AIG.RefVec.get_cast]
      · simp
      · assumption
    · apply go_le_size
  · rw [← hgo]
    simp only [Nat.le_refl, get, Ref.gate_cast, Ref.mk.injEq, true_implies]
    obtain rfl : curr = w := by omega
    simp
termination_by w - curr

theorem go_get (aig : AIG α) (curr : Nat) (hcurr : curr ≤ w) (cin : Ref aig)
    (s : AIG.RefVec aig curr) (lhs rhs : AIG.RefVec aig w) :
    ∀ (idx : Nat) (hidx : idx < curr),
        (go aig lhs rhs curr hcurr cin s).vec.get idx (by omega)
          =
        (s.get idx hidx).cast (by apply go_le_size) := by
  intros
  apply go_get_aux

theorem atLeastTwo_eq_halfAdder (lhsBit rhsBit carry : Bool) :
    Bool.atLeastTwo lhsBit rhsBit carry
      =
    (((lhsBit ^^ rhsBit) && carry) || (lhsBit && rhsBit)) := by
  revert lhsBit rhsBit carry
  decide

theorem go_denote_eq (aig : AIG α) (curr : Nat) (hcurr : curr ≤ w) (cin : Ref aig)
    (s : AIG.RefVec aig curr) (lhs rhs : AIG.RefVec aig w) (assign : α → Bool)
    (lhsExpr rhsExpr : BitVec w)
    (hleft : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, lhs.get idx hidx, assign⟧ = lhsExpr.getLsbD idx)
    (hright : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, rhs.get idx hidx, assign⟧ = rhsExpr.getLsbD idx)
    (hcin : ⟦aig, cin, assign⟧ = BitVec.carry curr lhsExpr rhsExpr false) :
    ∀ (idx : Nat) (hidx1 : idx < w),
        curr ≤ idx
          →
        ⟦
          (go aig lhs rhs curr hcurr cin s).aig,
          (go aig lhs rhs curr hcurr cin s).vec.get idx hidx1,
          assign
        ⟧
          =
        ⟦aig, lhs.get idx hidx1, assign⟧.xor
          (⟦aig, rhs.get idx hidx1, assign⟧.xor
            (BitVec.carry idx lhsExpr rhsExpr false)) := by
  intro idx hidx1 hidx2
  generalize hgo : go aig lhs rhs curr hcurr cin s = res
  unfold go at hgo
  dsimp only at hgo
  split at hgo
  · next hlt =>
    cases Nat.eq_or_lt_of_le hidx2 with
    | inl heq =>
      rw [← hgo]
      rw [go_get (hidx := by omega)]
      rw [AIG.RefVec.get_push_ref_eq' (hidx := by rw [heq])]
      simp only [← heq]
      rw [go_denote_mem_prefix]
      · unfold mkFullAdder
        simp [hcin]
      · simp only [Ref.gate_cast]
        apply Ref.hgate
    | inr hlt =>
      rw [← hgo]
      rw [go_denote_eq (lhsExpr := lhsExpr) (rhsExpr := rhsExpr) (curr := curr + 1)]
      · rw [mkFullAdder_denote_mem_prefix]
        rw [mkFullAdder_denote_mem_prefix]
        · simp
        · simp [Ref.hgate]
        · simp [Ref.hgate]
      · intro idx hidx
        rw [mkFullAdder_denote_mem_prefix]
        rw [← hleft idx hidx]
        · simp
        · simp [Ref.hgate]
      · intro idx hidx
        rw [mkFullAdder_denote_mem_prefix]
        rw [← hright idx hidx]
        · simp
        · simp [Ref.hgate]
      · unfold mkFullAdder
        simp only [Ref.cast_eq, id_eq, Int.reduceNeg, denote_projected_entry, denote_mkFullAdderCarry,
          FullAdderInput.lhs_cast, FullAdderInput.rhs_cast, FullAdderInput.cin_cast,
          BitVec.carry_succ]
        rw [AIG.LawfulOperator.denote_mem_prefix (f := mkFullAdderOut)]
        rw [AIG.LawfulOperator.denote_mem_prefix (f := mkFullAdderOut)]
        rw [AIG.LawfulOperator.denote_mem_prefix (f := mkFullAdderOut)]
        rw [hleft, hright, hcin]
        simp [atLeastTwo_eq_halfAdder]
      · omega
  · omega
termination_by w - curr

end blastAdd

theorem denote_blastAdd (aig : AIG α) (lhs rhs : BitVec w) (assign : α → Bool)
      (input : BinaryRefVec aig w)
      (hleft : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, input.lhs.get idx hidx, assign⟧ = lhs.getLsbD idx)
      (hright : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, input.rhs.get idx hidx, assign⟧ = rhs.getLsbD idx) :
      ∀ (idx : Nat) (hidx : idx < w),
          ⟦(blastAdd aig input).aig, (blastAdd aig input).vec.get idx hidx, assign⟧
            =
          (lhs + rhs).getLsbD idx := by
  intro idx hidx
  rw [BitVec.getLsbD_add]
  · rw [← hleft idx hidx]
    rw [← hright idx hidx]
    unfold blastAdd
    dsimp only
    rw [blastAdd.go_denote_eq _ 0 (by omega) _ _ _ _ assign lhs rhs _ _]
    · simp only [BinaryRefVec.lhs_get_cast, Ref.cast_eq, BinaryRefVec.rhs_get_cast]
      rw [LawfulOperator.denote_mem_prefix (f := mkConstCached)]
      rw [LawfulOperator.denote_mem_prefix (f := mkConstCached)]
    · simp
    · omega
    · intros
      simp only [BinaryRefVec.lhs_get_cast, Ref.cast_eq]
      rw [LawfulOperator.denote_mem_prefix (f := mkConstCached)]
      rw [hleft]
    · intros
      simp only [BinaryRefVec.rhs_get_cast, Ref.cast_eq]
      rw [LawfulOperator.denote_mem_prefix (f := mkConstCached)]
      rw [hright]
  · assumption

end bitblast
end BVExpr

end Std.Tactic.BVDecide
