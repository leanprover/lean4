/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Lean.Elab.Tactic.BvDecide.BitBlast.BVExpr.BitBlast.Lemmas.Basic
import Lean.Elab.Tactic.BvDecide.BitBlast.BVExpr.BitBlast.Impl.Add

/-!
This module contains the verification of the `BitVec.add` bitblaster from `Impl.Add`.
-/

namespace Lean.Elab.Tactic.BvDecide

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
    xor (xor ⟦aig, input.lhs, assign⟧ ⟦aig, input.rhs, assign⟧) ⟦aig, input.cin, assign⟧
    := by
  simp only [mkFullAdderOut, Ref_cast', denote_mkXorCached, denote_projected_entry, Bool.bne_assoc,
    Bool.bne_left_inj]
  rw [LawfulOperator.denote_mem_prefix (f := mkXorCached)]

@[simp]
theorem denote_mkFullAdderCarry (assign : α → Bool) (aig : AIG α) (input : FullAdderInput aig) :
    ⟦mkFullAdderCarry aig input, assign⟧
      =
    or
      (and
        (xor
          ⟦aig, input.lhs, assign⟧
          ⟦aig, input.rhs, assign⟧)
        ⟦aig, input.cin, assign⟧)
      (and
        ⟦aig, input.lhs, assign⟧
        ⟦aig, input.rhs, assign⟧)
    := by
  simp only [mkFullAdderCarry, Ref_cast', Int.reduceNeg, denote_mkOrCached,
    LawfulOperator.denote_input_entry, denote_mkAndCached, denote_projected_entry',
    denote_mkXorCached, denote_projected_entry]
  -- The underlying term here is huge -> conv mode to speed up the proof
  conv =>
    lhs
    lhs
    rw [LawfulOperator.denote_mem_prefix (f := mkXorCached) (h := input.cin.hgate)]
  conv =>
    lhs
    rhs
    lhs
    rw [
      LawfulOperator.denote_mem_prefix
        (f := mkAndCached)
        (h := by
          apply LawfulOperator.lt_size_of_lt_aig_size (f := mkXorCached)
          apply Ref.hgate
        )
    ]
  conv =>
    lhs
    rhs
    lhs
    rw [LawfulOperator.denote_mem_prefix (f := mkXorCached) (h := input.lhs.hgate)]
  conv =>
    lhs
    rhs
    rhs
    rw [
      LawfulOperator.denote_mem_prefix
        (f := mkAndCached)
        (h := by
          apply LawfulOperator.lt_size_of_lt_aig_size (f := mkXorCached)
          apply Ref.hgate
        )
    ]
  conv =>
    lhs
    rhs
    rhs
    rw [LawfulOperator.denote_mem_prefix (f := mkXorCached) (h := input.rhs.hgate)]

theorem mkFullAdder_denote_mem_prefix (aig : AIG α) (input : FullAdderInput aig) (start : Nat)
    (hstart) :
    ⟦
      (mkFullAdder aig input).aig,
      ⟨start, by apply Nat.lt_of_lt_of_le; exact hstart; apply FullAdderOutput.hle⟩,
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
  . intros
    apply go_decl_eq
  . intros
    apply go_le_size

theorem go_get_aux (aig : AIG α) (curr : Nat) (hcurr : curr ≤ w) (cin : Ref aig)
    (s : AIG.RefVec aig curr) (lhs rhs : AIG.RefVec aig w) :
    -- The hfoo here is a trick to make the dependent type gods happy
    ∀ (idx : Nat) (hidx : idx < curr) (hfoo),
        (go aig lhs rhs curr hcurr cin s).vec.get idx (by omega)
          =
        (s.get idx hidx).cast hfoo := by
  intro idx hidx
  generalize hgo : go aig lhs rhs curr hcurr cin s = res
  unfold go at hgo
  dsimp only at hgo
  split at hgo
  . rw [← hgo]
    intro hfoo
    rw [go_get_aux]
    rw [AIG.RefVec.get_push_ref_lt]
    . simp only [Ref.cast, Ref.mk.injEq]
      rw [AIG.RefVec.get_cast]
      . simp
      . assumption
    . apply go_le_size
  . rw [← hgo]
    simp only [Nat.le_refl, get, Ref_cast', Ref.mk.injEq, true_implies]
    have : curr = w := by omega
    subst this
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
    (((xor lhsBit rhsBit) && carry) || (lhsBit && rhsBit)) := by
  revert lhsBit rhsBit carry
  decide

theorem go_denote_eq (aig : AIG α) (curr : Nat) (hcurr : curr ≤ w) (cin : Ref aig)
    (s : AIG.RefVec aig curr) (lhs rhs : AIG.RefVec aig w) (assign : α → Bool)
    (lhsExpr rhsExpr : BitVec w)
    (hleft : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, lhs.get idx hidx, assign⟧ = lhsExpr.getLsb idx)
    (hright : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, rhs.get idx hidx, assign⟧ = rhsExpr.getLsb idx)
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
  . next hlt =>
    cases Nat.eq_or_lt_of_le hidx2 with
    | inl heq =>
      rw [← hgo]
      rw [go_get (hidx := by omega)]
      rw [AIG.RefVec.get_push_ref_eq' (hidx := by rw [heq])]
      simp only [← heq]
      rw [go_denote_mem_prefix]
      . unfold mkFullAdder
        simp [hcin]
      . simp only [Ref_cast']
        apply Ref.hgate
    | inr hlt =>
      rw [← hgo]
      rw [go_denote_eq (lhsExpr := lhsExpr) (rhsExpr := rhsExpr) (curr := curr + 1)]
      . rw [mkFullAdder_denote_mem_prefix]
        rw [mkFullAdder_denote_mem_prefix]
        . simp
        . simp [Ref.hgate]
        . simp [Ref.hgate]
      . intro idx hidx
        rw [mkFullAdder_denote_mem_prefix]
        rw [← hleft idx hidx]
        . simp
        . simp [Ref.hgate]
      . intro idx hidx
        rw [mkFullAdder_denote_mem_prefix]
        rw [← hright idx hidx]
        . simp
        . simp [Ref.hgate]
      . unfold mkFullAdder
        simp only [Ref_cast', id_eq, Int.reduceNeg, denote_projected_entry, denote_mkFullAdderCarry,
          FullAdderInput.lhs_cast, FullAdderInput.rhs_cast, FullAdderInput.cin_cast,
          BitVec.carry_succ]
        rw [AIG.LawfulOperator.denote_mem_prefix (f := mkFullAdderOut)]
        rw [AIG.LawfulOperator.denote_mem_prefix (f := mkFullAdderOut)]
        rw [AIG.LawfulOperator.denote_mem_prefix (f := mkFullAdderOut)]
        rw [hleft, hright, hcin]
        simp [atLeastTwo_eq_halfAdder]
      . omega
  . omega
termination_by w - curr

end blastAdd

theorem blastAdd_denote_eq (aig : AIG α) (lhs rhs : BitVec w) (assign : α → Bool)
      (input : BinaryRefVec aig w)
      (hleft : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, input.lhs.get idx hidx, assign⟧ = lhs.getLsb idx)
      (hright : ∀ (idx : Nat) (hidx : idx < w), ⟦aig, input.rhs.get idx hidx, assign⟧ = rhs.getLsb idx) :
      ∀ (idx : Nat) (hidx : idx < w),
          ⟦(blastAdd aig input).aig, (blastAdd aig input).vec.get idx hidx, assign⟧
            =
          (lhs + rhs).getLsb idx := by
  intro idx hidx
  rw [BitVec.getLsb_add]
  . rw [← hleft idx hidx]
    rw [← hright idx hidx]
    unfold blastAdd
    dsimp only
    rw [blastAdd.go_denote_eq _ 0 (by omega) _ _ _ _ assign lhs rhs _ _]
    . simp only [BinaryRefVec.lhs_get_cast, Ref_cast', BinaryRefVec.rhs_get_cast]
      rw [LawfulOperator.denote_mem_prefix (f := mkConstCached)]
      rw [LawfulOperator.denote_mem_prefix (f := mkConstCached)]
    . simp
    . omega
    . intros
      simp only [BinaryRefVec.lhs_get_cast, Ref_cast']
      rw [LawfulOperator.denote_mem_prefix (f := mkConstCached)]
      rw [hleft]
    . intros
      simp only [BinaryRefVec.rhs_get_cast, Ref_cast']
      rw [LawfulOperator.denote_mem_prefix (f := mkConstCached)]
      rw [hright]
  . assumption

end bitblast
end BVExpr

end Lean.Elab.Tactic.BvDecide
