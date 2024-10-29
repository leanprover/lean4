/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Std.Sat.AIG.CachedGates
import Std.Sat.AIG.CachedGatesLemmas
import Std.Tactic.BVDecide.Bitblast.BoolExpr.Basic
import Std.Sat.AIG.If

/-!
This module contains the logic to turn a `BoolExpr Nat` into an `AIG` with maximum subterm sharing,
through the use of a cache that re-uses sub-circuits if possible.
-/

namespace Std.Tactic.BVDecide

open Std.Sat Std.Sat.AIG

variable {β : Type} [Hashable β] [DecidableEq β]

/--
Turn a `BoolExpr` into an `Entrypoint`.
-/
@[specialize]
def ofBoolExprCached (expr : BoolExpr α) (atomHandler : AIG β → α → Entrypoint β)
    [LawfulOperator β (fun _ => α) atomHandler] : Entrypoint β :=
  go AIG.empty expr atomHandler |>.val
where
  @[specialize]
  go (aig : AIG β) (expr : BoolExpr α) (atomHandler : AIG β → α → Entrypoint β)
      [LawfulOperator β (fun _ => α) atomHandler] :
      ExtendingEntrypoint aig :=
    match expr with
    | .literal var => ⟨atomHandler aig var, by apply LawfulOperator.le_size⟩
    | .const val => ⟨aig.mkConstCached val, (by apply LawfulOperator.le_size)⟩
    | .not expr =>
      let ⟨⟨aig, exprRef⟩, _⟩ := go aig expr atomHandler
      let ret := aig.mkNotCached exprRef
      have := LawfulOperator.le_size (f := mkNotCached) aig exprRef
      ⟨ret, by dsimp only [ret] at *; omega⟩
    | .ite discr lhs rhs =>
      let ⟨⟨aig, discrRef⟩, dextend⟩ := go aig discr atomHandler
      let ⟨⟨aig, lhsRef⟩, lextend⟩ := go aig lhs atomHandler
      let ⟨⟨aig, rhsRef⟩, rextend⟩ := go aig rhs atomHandler
      let discrRef := discrRef.cast <| by
        dsimp only at lextend rextend ⊢
        omega
      let lhsRef := lhsRef.cast <| by
        dsimp only at rextend ⊢
        omega

      let input := ⟨discrRef, lhsRef, rhsRef⟩
      let ret := aig.mkIfCached input
      have := LawfulOperator.le_size (f := mkIfCached) aig input
      ⟨ret, by dsimp only [ret] at lextend rextend dextend ⊢; omega⟩
    | .gate g lhs rhs =>
      let ⟨⟨aig, lhsRef⟩, lextend⟩ := go aig lhs atomHandler
      let ⟨⟨aig, rhsRef⟩, rextend⟩ := go aig rhs atomHandler
      let lhsRef := lhsRef.cast <| by
        dsimp only at rextend ⊢
        omega
      let input := ⟨lhsRef, rhsRef⟩
      match g with
      | .and =>
        let ret := aig.mkAndCached input
        have := LawfulOperator.le_size (f := mkAndCached) aig input
        ⟨ret, by dsimp only [ret] at lextend rextend ⊢; omega⟩
      | .xor =>
        let ret := aig.mkXorCached input
        have := LawfulOperator.le_size (f := mkXorCached) aig input
        ⟨ret, by dsimp only [ret] at lextend rextend ⊢; omega⟩
      | .beq =>
        let ret := aig.mkBEqCached input
        have := LawfulOperator.le_size (f := mkBEqCached) aig input
        ⟨ret, by dsimp only [ret] at lextend rextend ⊢; omega⟩
      | .imp =>
        let ret := aig.mkImpCached input
        have := LawfulOperator.le_size (f := mkImpCached) aig input
        ⟨ret, by dsimp only [ret] at lextend rextend ⊢; omega⟩

namespace ofBoolExprCached

variable (atomHandler : AIG β → α → Entrypoint β) [LawfulOperator β (fun _ => α) atomHandler]

theorem go_le_size (expr : BoolExpr α) (aig : AIG β) :
    aig.decls.size ≤ (ofBoolExprCached.go aig expr atomHandler).val.aig.decls.size :=
  (ofBoolExprCached.go aig expr atomHandler).property

theorem go_decl_eq (idx) (aig : AIG β) (h : idx < aig.decls.size) (hbounds) :
    (ofBoolExprCached.go aig expr atomHandler).val.aig.decls[idx]'hbounds = aig.decls[idx] := by
  induction expr generalizing aig with
  | const =>
    simp only [go]
    rw [AIG.LawfulOperator.decl_eq (f := mkConstCached)]
  | literal =>
    simp only [go]
    rw [AIG.LawfulOperator.decl_eq (f := atomHandler)]
  | not expr ih =>
    simp only [go]
    have := go_le_size atomHandler expr aig
    specialize ih aig (by omega) (by omega)
    rw [AIG.LawfulOperator.decl_eq (f := mkNotCached)]
    assumption
  | ite discr lhs rhs dih lih rih =>
    have := go_le_size atomHandler discr aig
    have := go_le_size atomHandler lhs (go aig discr atomHandler).val.aig
    have := go_le_size atomHandler rhs (go (go aig discr atomHandler).val.aig lhs atomHandler).val.aig
    specialize dih aig (by omega) (by omega)
    specialize lih (go aig discr atomHandler).val.aig (by omega) (by omega)
    specialize rih (go (go aig discr atomHandler).val.aig lhs atomHandler).val.aig (by omega) (by omega)
    simp only [go]
    rw [AIG.LawfulOperator.decl_eq (f := mkIfCached), rih, lih, dih]
  | gate g lhs rhs lih rih =>
    have := go_le_size atomHandler lhs aig
    have := go_le_size atomHandler rhs (go aig lhs atomHandler).val.aig
    specialize lih aig (by omega) (by omega)
    specialize rih (go aig lhs atomHandler).val.aig (by omega) (by omega)
    cases g with
    | and =>
      simp only [go]
      rw [AIG.LawfulOperator.decl_eq (f := mkAndCached), rih, lih]
    | xor =>
      simp only [go]
      rw [AIG.LawfulOperator.decl_eq (f := mkXorCached), rih, lih]
    | beq =>
      simp only [go]
      rw [AIG.LawfulOperator.decl_eq (f := mkBEqCached), rih, lih]
    | imp =>
      simp only [go]
      rw [AIG.LawfulOperator.decl_eq (f := mkImpCached), rih, lih]

theorem go_isPrefix_aig {aig : AIG β} :
    IsPrefix aig.decls (go aig expr atomHandler).val.aig.decls := by
  apply IsPrefix.of
  · intro idx h
    apply ofBoolExprCached.go_decl_eq
  · apply go_le_size

theorem go_denote_mem_prefix :
    ⟦
      (go aig expr atomHandler).val.aig,
      ⟨start, by apply Nat.lt_of_lt_of_le; exact hstart; apply go_le_size⟩,
      assign
    ⟧
      =
    ⟦aig, ⟨start, hstart⟩, assign⟧ := by
  apply denote.eq_of_isPrefix (entry := ⟨aig, start,hstart⟩)
  apply go_isPrefix_aig

@[simp]
theorem go_denote_entry (entry : Entrypoint β) {h} :
    ⟦(go entry.aig expr atomHandler).val.aig, ⟨entry.ref.gate, h⟩, assign⟧ = ⟦entry, assign⟧ := by
  apply denote.eq_of_isPrefix
  apply ofBoolExprCached.go_isPrefix_aig

end ofBoolExprCached

end Std.Tactic.BVDecide
