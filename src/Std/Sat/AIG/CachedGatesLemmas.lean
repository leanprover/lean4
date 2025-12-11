/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Std.Sat.AIG.CachedGates
import Init.Grind

@[expose] public section

/-!
This module contains the theory of the cached gate creation functions, mostly enabled by the
`LawfulOperator` framework. It is mainly concerned with proving lemmas about the denotational
semantics of the gate functions in different scenarios.
-/

namespace Std
namespace Sat

namespace AIG

/--
Encoding of or as boolean expression in AIG form.
-/
private theorem or_as_aig : ∀ (a b : Bool), (!(!a && !b)) = (a || b) := by
  decide

/--
Encoding of XOR as boolean expression in AIG form.
-/
private theorem xor_as_aig : ∀ (a b : Bool), (!(a && b) && !(!a && !b)) = (a ^^ b) := by
  decide

/--
Encoding of BEq as boolean expression in AIG form.
-/
private theorem beq_as_aig : ∀ (a b : Bool), (!(a && !b) && !(!a && b)) = (a == b) := by
  decide

/--
Encoding of implication as boolean expression in AIG form.
-/
private theorem imp_as_aig : ∀ (a b : Bool), (!(a && !b)) = (!a || b) := by
  decide

variable {α : Type} [Hashable α] [DecidableEq α]

@[grind! .]
theorem mkNotCached_le_size (aig : AIG α) (gate : Ref aig) :
    aig.decls.size ≤ (aig.mkNotCached gate).aig.decls.size := by
  simp [mkNotCached]

@[grind =]
theorem mkNotCached_decl_eq idx (aig : AIG α) (gate : Ref aig) {h : idx < aig.decls.size} {h2} :
    (aig.mkNotCached gate).aig.decls[idx]'h2 = aig.decls[idx]'h := by
  simp [mkNotCached]

instance : LawfulOperator α Ref mkNotCached where
  le_size := mkNotCached_le_size
  decl_eq := by
    intros
    apply mkNotCached_decl_eq

@[simp]
theorem denote_mkNotCached {aig : AIG α} {gate : Ref aig} :
    ⟦aig.mkNotCached gate, assign⟧ = !⟦aig, gate, assign⟧ := by
  simp [mkNotCached]

@[grind! .]
theorem mkAndCached_le_size (aig : AIG α) (input : BinaryInput aig) :
    aig.decls.size ≤ (aig.mkAndCached input).aig.decls.size := by
  simp only [mkAndCached]
  grind

@[grind =]
theorem mkAndCached_decl_eq idx (aig : AIG α) (input : BinaryInput aig) {h : idx < aig.decls.size}
    {h2} :
    (aig.mkAndCached input).aig.decls[idx]'h2 = aig.decls[idx] := by
  simp only [mkAndCached]
  grind

instance : LawfulOperator α BinaryInput mkAndCached where
  le_size := mkAndCached_le_size
  decl_eq := by intros; apply mkAndCached_decl_eq

@[simp]
theorem denote_mkAndCached {aig : AIG α} {input : BinaryInput aig} :
    ⟦aig.mkAndCached input, assign⟧ = (⟦aig, input.lhs, assign⟧ && ⟦aig, input.rhs, assign⟧) := by
  simp [mkAndCached]

@[grind! .]
theorem mkOrCached_le_size (aig : AIG α) (input : BinaryInput aig) :
    aig.decls.size ≤ (aig.mkOrCached input).aig.decls.size := by
  simp only [mkOrCached]
  grind

@[grind =]
theorem mkOrCached_decl_eq idx (aig : AIG α) (input : BinaryInput aig) {h : idx < aig.decls.size}
    {h2} :
    (aig.mkOrCached input).aig.decls[idx]'h2 = aig.decls[idx] := by
  simp only [mkOrCached]
  grind

instance : LawfulOperator α BinaryInput mkOrCached where
  le_size := mkOrCached_le_size
  decl_eq := by intros; apply mkOrCached_decl_eq

@[simp]
theorem denote_mkOrCached {aig : AIG α} {input : BinaryInput aig} :
    ⟦aig.mkOrCached input, assign⟧ = (⟦aig, input.lhs, assign⟧ || ⟦aig, input.rhs, assign⟧) := by
  rw [← or_as_aig]
  simp [mkOrCached]

@[grind! .]
theorem mkXorCached_le_size (aig : AIG α) {input : BinaryInput aig} :
    aig.decls.size ≤ (aig.mkXorCached input).aig.decls.size := by
  simp only [mkXorCached]
  grind

@[grind =]
theorem mkXorCached_decl_eq idx (aig : AIG α) (input : BinaryInput aig) {h : idx < aig.decls.size}
    {h2} :
    (aig.mkXorCached input).aig.decls[idx]'h2 = aig.decls[idx] := by
  simp only [mkXorCached]
  grind

instance : LawfulOperator α BinaryInput mkXorCached where
  le_size := mkXorCached_le_size
  decl_eq := by intros; apply mkXorCached_decl_eq

@[simp]
theorem denote_mkXorCached {aig : AIG α} {input : BinaryInput aig} :
    ⟦aig.mkXorCached input, assign⟧ = (⟦aig, input.lhs, assign⟧ ^^ ⟦aig, input.rhs, assign⟧) := by
  rw [← xor_as_aig]
  simp [
    mkXorCached,
    LawfulOperator.denote_mem_prefix (f := mkGateCached) input.lhs.hgate,
    LawfulOperator.denote_mem_prefix (f := mkGateCached) input.rhs.hgate
  ]

@[grind! .]
theorem mkBEqCached_le_size (aig : AIG α) {input : BinaryInput aig} :
    aig.decls.size ≤ (aig.mkBEqCached input).aig.decls.size := by
  simp only [mkBEqCached]
  grind

@[grind =]
theorem mkBEqCached_decl_eq idx (aig : AIG α) (input : BinaryInput aig) {h : idx < aig.decls.size}
    {h2} :
    (aig.mkBEqCached input).aig.decls[idx]'h2 = aig.decls[idx] := by
  simp only [mkBEqCached]
  grind

instance : LawfulOperator α BinaryInput mkBEqCached where
  le_size := mkBEqCached_le_size
  decl_eq := by intros; apply mkBEqCached_decl_eq

@[simp]
theorem denote_mkBEqCached {aig : AIG α} {input : BinaryInput aig} :
    ⟦aig.mkBEqCached input, assign⟧ = (⟦aig, input.lhs, assign⟧ == ⟦aig, input.rhs, assign⟧) := by
  rw [← beq_as_aig]
  simp [
    mkBEqCached,
    LawfulOperator.denote_mem_prefix (f := mkGateCached) input.lhs.hgate,
    LawfulOperator.denote_mem_prefix (f := mkGateCached) input.rhs.hgate
  ]

@[grind! .]
theorem mkImpCached_le_size (aig : AIG α) (input : BinaryInput aig) :
    aig.decls.size ≤ (aig.mkImpCached input).aig.decls.size := by
  simp only [mkImpCached]
  grind

@[grind =]
theorem mkImpCached_decl_eq idx (aig : AIG α) (input : BinaryInput aig) {h : idx < aig.decls.size}
    {h2} :
    (aig.mkImpCached input).aig.decls[idx]'h2 = aig.decls[idx] := by
  simp only [mkImpCached]
  grind

instance : LawfulOperator α BinaryInput mkImpCached where
  le_size := mkImpCached_le_size
  decl_eq := by intros; apply mkImpCached_decl_eq

@[simp]
theorem denote_mkImpCached {aig : AIG α} {input : BinaryInput aig} :
    ⟦aig.mkImpCached input, assign⟧ = ( !⟦aig, input.lhs, assign⟧ || ⟦aig, input.rhs, assign⟧) := by
  rw [← imp_as_aig]
  simp [mkImpCached]

end AIG

end Sat
end Std
