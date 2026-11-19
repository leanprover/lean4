/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Std.Sat.AIG.Cached
import Init.Data.Nat.Order
import Init.Data.Order.Lemmas

@[expose] public section

/-!
This module contains the theory of the cached AIG node creation functions.
It is mainly concerned with proving lemmas about the denotational semantics of the gate functions
in different scenarios, in particular reductions to the semantics of the non cached versions.
-/

namespace Std
namespace Sat

namespace AIG

variable {α : Type} [Hashable α] [DecidableEq α]

/--
If we find a cached atom declaration in the AIG, denoting it yields the value of the atom.
-/
theorem denote_mkAtom_cached {aig : AIG α} {hit} :
    aig.cache.get? (.atom v) = some hit
      →
    ⟦aig, ⟨hit.idx, false, hit.hbound⟩, assign⟧ = assign v := by
  simp [denote_idx_atom hit.hvalid]

/--
`mkAtomCached` does not modify the input AIG upon a cache hit.
-/
theorem mkAtomCached_hit_aig (aig : AIG α) {hit} (hcache : aig.cache.get? (.atom var) = some hit) :
    (aig.mkAtomCached var).aig = aig := by
  simp only [mkAtomCached]
  split <;> simp_all

/--
`mkAtomCached` pushes to the input AIG upon a cache miss.
-/
theorem mkAtomCached_miss_aig (aig : AIG α) (hcache : aig.cache.get? (.atom var) = none) :
    (aig.mkAtomCached var).aig.decls = aig.decls.push (.atom var) := by
  simp only [mkAtomCached]
  split <;> simp_all

/--
The AIG produced by `AIG.mkAtomCached` agrees with the input AIG on all indices that are valid for
both.
-/
theorem mkAtomCached_decl_eq (aig : AIG α) (var : α) (idx : Nat) {h : idx < aig.decls.size}
    {hbound} :
    (aig.mkAtomCached var).aig.decls[idx]'hbound = aig.decls[idx] := by
  match hcache : aig.cache.get? (.atom var) with
  | some gate =>
    have := mkAtomCached_hit_aig aig hcache
    simp [this]
  | none =>
    have := mkAtomCached_miss_aig aig hcache
    simp only [this, Array.getElem_push]
    split
    · rfl
    · contradiction

/--
`AIG.mkAtomCached` never shrinks the underlying AIG.
-/
theorem mkAtomCached_le_size (aig : AIG α) (var : α) :
    aig.decls.size ≤ (aig.mkAtomCached var).aig.decls.size := by
  dsimp only [mkAtomCached]
  split
  · simp
  · simp +arith

instance : LawfulOperator α (fun _ => α) mkAtomCached where
  le_size := mkAtomCached_le_size
  decl_eq := mkAtomCached_decl_eq

/--
Denoting `mkAtomCached` yields the value of the atom.
-/
@[simp]
theorem denote_mkAtomCached {aig : AIG α} :
    ⟦aig.mkAtomCached var, assign⟧ = assign var := by
  simp only [mkAtomCached]
  split
  next heq1 =>
    rw [denote_mkAtom_cached heq1]
  · unfold denote denote.go
    split
    · simp_all
    · simp_all
    · next heq => simp at heq

/--
Denoting `mkConstCached` yields the constant.
-/
@[simp]
theorem denote_mkConstCached {aig : AIG α} :
    ⟦aig, aig.mkConstCached val, assign⟧ = val := by
  simp only [mkConstCached]
  unfold denote denote.go
  split
  · simp
  next heq => simp [aig.hconst] at heq
  next heq => simp [aig.hconst] at heq

/--
If we find a cached gate declaration in the AIG, denoting it yields the conjunction of its inputs.
-/
theorem denote_mkGate_cached {aig : AIG α} {input : BinaryInput aig} {hit} :
    aig.cache.get? (.gate (.mk input.lhs.gate input.lhs.invert) (.mk input.rhs.gate input.rhs.invert)) = some hit
      →
    ⟦⟨aig, hit.idx, false, hit.hbound⟩, assign⟧
      =
    (⟦aig, input.lhs, assign⟧ && ⟦aig, input.rhs, assign⟧) := by
  intros
  have := hit.hvalid
  conv =>
    lhs
    unfold denote denote.go
  split <;> simp_all [denote]

theorem mkGateCached.go_le_size (aig : AIG α) (input : BinaryInput aig) :
    aig.decls.size ≤ (go aig input).aig.decls.size := by
  dsimp only [go]
  split
  · simp
  · split <;> try simp
    split
    · split <;> simp
    · simp

/--
`AIG.mkGateCached` never shrinks the underlying AIG.
-/
theorem mkGateCached_le_size (aig : AIG α) (input : BinaryInput aig) :
    aig.decls.size ≤ (aig.mkGateCached input).aig.decls.size := by
  dsimp only [mkGateCached]
  split
  · apply mkGateCached.go_le_size
  · apply mkGateCached.go_le_size

theorem mkGateCached.go_decl_eq (aig : AIG α) (input : BinaryInput aig) :
    ∀ (idx : Nat) (h1) (h2), (go aig input).aig.decls[idx]'h1 = aig.decls[idx]'h2 := by
    generalize hres : go aig input = res
    unfold go at hres
    dsimp only at hres
    split at hres
    · rw [← hres]
      intros
      simp
    · split at hres
      · rw [← hres]
        simp
      · rw [← hres]
        simp
      · rw [← hres]
        intros
        simp
      · rw [← hres]
        intros
        simp
      · split at hres
        · split at hres
          · rw [← hres]
            intros
            simp
          · rw [← hres]
            intros
            simp
        · rw [← hres]
          dsimp only
          intro idx h1 h2
          rw [Array.getElem_push]
          simp [h2]

/--
The AIG produced by `AIG.mkGateCached` agrees with the input AIG on all indices that are valid for
both.
-/
theorem mkGateCached_decl_eq (aig : AIG α) (input : BinaryInput aig) :
    ∀ (idx : Nat) (h1) (h2), (aig.mkGateCached input).aig.decls[idx]'h1 = aig.decls[idx]'h2 := by
    generalize hres : mkGateCached aig input = res
    unfold mkGateCached at hres
    dsimp only at hres
    split at hres
    all_goals
      rw [← hres]
      intros
      rw [mkGateCached.go_decl_eq]

instance : LawfulOperator α BinaryInput mkGateCached where
  le_size := mkGateCached_le_size
  decl_eq := by
    intros
    apply mkGateCached_decl_eq

/--
Denoting a gate that was just pushed onto an AIG yields the conjunction of its inputs.
-/
theorem denote_gate_push {aig1 aig2 : AIG α} {input : BinaryInput aig1} {hidx}
    (h : aig2.decls = aig1.decls.push (.gate (.mk input.lhs.gate input.lhs.invert) (.mk input.rhs.gate input.rhs.invert))) :
    ⟦aig2, ⟨aig1.decls.size, false, hidx⟩, assign⟧
      =
    (⟦aig1, input.lhs, assign⟧ && ⟦aig1, input.rhs, assign⟧) := by
  have hprefix : IsPrefix aig1.decls aig2.decls := by rw [h]; exact IsPrefix_push
  have hgate : aig2.decls[aig1.decls.size]'hidx = .gate (.mk input.lhs.gate input.lhs.invert) (.mk input.rhs.gate input.rhs.invert) := by
    simp [h]
  rw [denote_idx_gate hgate]
  simp only [Fanin.gate_mk, Fanin.invert_mk, Bool.bne_false]
  rw [denote.eq_of_isPrefix ⟨aig1, input.lhs⟩ aig2 hprefix,
    denote.eq_of_isPrefix ⟨aig1, input.rhs⟩ aig2 hprefix]

theorem mkGateCached.denote_go {aig : AIG α} {input : BinaryInput aig} :
    ⟦go aig input, assign⟧ = (⟦aig, input.lhs, assign⟧ && ⟦aig, input.rhs, assign⟧) := by
  simp only [go]
  split
  next heq1 =>
    rw [denote_mkGate_cached heq1]
  · split
    · simp_all [denote_getConstant]
    · simp_all [denote_getConstant]
    · simp_all [denote_getConstant]
    · simp_all [denote_getConstant]
    · rcases input with ⟨⟨lhs, linv, hlgate⟩, ⟨rhs, rinv, hrgate⟩⟩
      split
      · split
        · simp_all
        next hif =>
          simp_all
          have := Bool.eq_not_of_ne hif
          simp_all
      · exact denote_gate_push rfl

/--
Denoting `mkGateCached` yields the conjunction of its inputs.
-/
@[simp]
theorem denote_mkGateCached {aig : AIG α} {input : BinaryInput aig} :
    ⟦aig.mkGateCached input, assign⟧ = (⟦aig, input.lhs, assign⟧ && ⟦aig, input.rhs, assign⟧) := by
  simp only [mkGateCached]
  split
  · rw [mkGateCached.denote_go]
  · rw [mkGateCached.denote_go]
    rw [Bool.and_comm]

end AIG

end Sat
end Std
