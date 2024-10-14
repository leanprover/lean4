/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Std.Sat.AIG.CachedGates
import Std.Sat.AIG.CachedGatesLemmas
import Std.Tactic.BVDecide.Bitblast.BoolExpr.Basic

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

variable (atomHandler : AIG β → α → Entrypoint β) [LawfulOperator β (fun _ => α) atomHandler]

theorem ofBoolExprCached.go_decls_size_le (expr : BoolExpr α) (aig : AIG β) :
    aig.decls.size ≤ (ofBoolExprCached.go aig expr atomHandler).val.aig.decls.size :=
  (ofBoolExprCached.go aig expr atomHandler).property

theorem ofBoolExprCached.go_decl_eq (idx) (aig : AIG β) (h : idx < aig.decls.size) (hbounds) :
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
    have := go_decls_size_le atomHandler expr aig
    specialize ih aig (by omega) (by omega)
    rw [AIG.LawfulOperator.decl_eq (f := mkNotCached)]
    assumption
  | gate g lhs rhs lih rih =>
    have := go_decls_size_le atomHandler lhs aig
    have := go_decls_size_le atomHandler rhs (go aig lhs atomHandler).val.aig
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

theorem ofBoolExprCached.go_isPrefix_aig {aig : AIG β} :
    IsPrefix aig.decls (go aig expr atomHandler).val.aig.decls := by
  apply IsPrefix.of
  · intro idx h
    apply ofBoolExprCached.go_decl_eq
  · apply ofBoolExprCached.go_decls_size_le

@[simp]
theorem ofBoolExprCached.go_denote_entry (entry : Entrypoint β) {h} :
    ⟦(go entry.aig expr atomHandler).val.aig, ⟨entry.ref.gate, h⟩, assign⟧ = ⟦entry, assign⟧ := by
  apply denote.eq_of_isPrefix
  apply ofBoolExprCached.go_isPrefix_aig

end Std.Tactic.BVDecide
