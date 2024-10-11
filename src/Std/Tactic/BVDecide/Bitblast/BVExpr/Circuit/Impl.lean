/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Pred

-- TODO

/-!
This module contains the implementation of a bitblaster for general `BitVec` problems with boolean
substructure (`BVLogicalExpr`). It is the main entrypoint into the bitblasting framework.
-/

/-!
This module contains the logic to turn a `BoolExpr Nat` into an `AIG` with maximum subterm sharing,
through the use of a cache that re-uses sub-circuits if possible.
-/


namespace Std.Tactic.BVDecide

open Std.Sat Std.Sat.AIG

namespace BVLogicalExpr

def bitblast (expr : BVLogicalExpr) : Entrypoint BVBit :=
  go AIG.empty expr |>.val
where
  go (aig : AIG BVBit) (expr : BVLogicalExpr) : ExtendingEntrypoint aig :=
    match expr with
    | .literal pred => ⟨BVPred.bitblast aig pred, by apply LawfulOperator.le_size⟩
    | .const val => ⟨aig.mkConstCached val, (by apply LawfulOperator.le_size)⟩
    | .not expr =>
      let ⟨⟨aig, exprRef⟩, _⟩ := go aig expr
      let ret := aig.mkNotCached exprRef
      have := LawfulOperator.le_size (f := mkNotCached) aig exprRef
      ⟨ret, by dsimp only [ret] at *; omega⟩
    | .gate g lhs rhs =>
      let ⟨⟨aig, lhsRef⟩, lextend⟩ := go aig lhs
      let ⟨⟨aig, rhsRef⟩, rextend⟩ := go aig rhs
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

namespace bitblast

theorem go_decls_size_le (expr : BVLogicalExpr) (aig : AIG BVBit) :
    aig.decls.size ≤ (bitblast.go aig expr).val.aig.decls.size :=
  (bitblast.go aig expr).property

theorem go_decl_eq (idx) (aig : AIG BVBit) (h : idx < aig.decls.size) (hbounds) :
    (bitblast.go aig expr).val.aig.decls[idx]'hbounds = aig.decls[idx] := by
  induction expr generalizing aig with
  | const =>
    simp only [go]
    rw [AIG.LawfulOperator.decl_eq (f := mkConstCached)]
  | literal =>
    simp only [go]
    rw [AIG.LawfulOperator.decl_eq (f := BVPred.bitblast)]
  | not expr ih =>
    simp only [go]
    have := go_decls_size_le expr aig
    specialize ih aig (by omega) (by omega)
    rw [AIG.LawfulOperator.decl_eq (f := mkNotCached)]
    assumption
  | gate g lhs rhs lih rih =>
    have := go_decls_size_le lhs aig
    have := go_decls_size_le rhs (go aig lhs).val.aig
    specialize lih aig (by omega) (by omega)
    specialize rih (go aig lhs).val.aig (by omega) (by omega)
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

theorem go_isPrefix_aig {aig : AIG BVBit} :
    IsPrefix aig.decls (go aig expr).val.aig.decls := by
  apply IsPrefix.of
  · intro idx h
    apply go_decl_eq
  · apply go_decls_size_le

@[simp]
theorem go_denote_entry (entry : Entrypoint BVBit) {h} :
    ⟦(go entry.aig expr).val.aig, ⟨entry.ref.gate, h⟩, assign⟧ = ⟦entry, assign⟧ := by
  apply denote.eq_of_isPrefix
  apply go_isPrefix_aig

end bitblast

end BVLogicalExpr

end Std.Tactic.BVDecide
