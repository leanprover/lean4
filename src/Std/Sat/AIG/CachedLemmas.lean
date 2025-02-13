/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Std.Sat.AIG.Cached

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
If we find a cached atom declaration in the AIG, denoting it is equivalent to denoting `AIG.mkAtom`.
-/
theorem denote_mkAtom_cached {aig : AIG α} {hit} :
    aig.cache.get? (.atom v) = some hit
      →
    ⟦aig, ⟨hit.idx, hit.hbound⟩, assign⟧ = ⟦aig.mkAtom v, assign⟧ := by
  have := hit.hvalid
  simp only [denote_mkAtom]
  unfold denote denote.go
  split <;> simp_all

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
The central equality theorem between `mkAtomCached` and `mkAtom`.
-/
@[simp]
theorem mkAtomCached_eval_eq_mkAtom_eval {aig : AIG α} :
    ⟦aig.mkAtomCached var, assign⟧ = ⟦aig.mkAtom var, assign⟧ := by
  simp only [mkAtomCached]
  split
  · next heq1 =>
    rw [denote_mkAtom_cached heq1]
  · simp [mkAtom, denote]

/--
If we find a cached const declaration in the AIG, denoting it is equivalent to denoting
`AIG.mkConst`.
-/
theorem denote_mkConst_cached {aig : AIG α} {hit} :
    aig.cache.get? (.const b) = some hit
      →
    ⟦aig, ⟨hit.idx, hit.hbound⟩, assign⟧ = ⟦aig.mkConst b, assign⟧ := by
  have := hit.hvalid
  simp only [denote_mkConst]
  unfold denote denote.go
  split <;> simp_all

/--
`mkConstCached` does not modify the input AIG upon a cache hit.
-/
theorem mkConstCached_hit_aig (aig : AIG α) {hit}
    (hcache : aig.cache.get? (.const val) = some hit) :
    (aig.mkConstCached val).aig = aig := by
  simp only [mkConstCached]
  split <;> simp_all

/--
`mkConstCached` pushes to the input AIG upon a cache miss.
-/
theorem mkConstCached_miss_aig (aig : AIG α) (hcache : aig.cache.get? (.const val) = none) :
    (aig.mkConstCached val).aig.decls = aig.decls.push (.const val) := by
  simp only [mkConstCached]
  split <;> simp_all

/--
The AIG produced by `AIG.mkConstCached` agrees with the input AIG on all indices that are valid for
both.
-/
theorem mkConstCached_decl_eq (aig : AIG α) (val : Bool) (idx : Nat) {h : idx < aig.decls.size}
    {hbound} :
    (aig.mkConstCached val).aig.decls[idx]'hbound = aig.decls[idx] := by
  match hcache : aig.cache.get? (.const val) with
  | some gate =>
    have := mkConstCached_hit_aig aig hcache
    simp [this]
  | none =>
    have := mkConstCached_miss_aig aig hcache
    simp only [this, Array.getElem_push]
    split
    · rfl
    · contradiction

/--
`AIG.mkConstCached` never shrinks the underlying AIG.
-/
theorem mkConstCached_le_size (aig : AIG α) (val : Bool) :
    aig.decls.size ≤ (aig.mkConstCached val).aig.decls.size := by
  dsimp only [mkConstCached]
  split
  · simp
  · simp +arith

instance : LawfulOperator α (fun _ => Bool) mkConstCached where
  le_size := mkConstCached_le_size
  decl_eq := by
    intros
    apply mkConstCached_decl_eq

/--
The central equality theorem between `mkConstCached` and `mkConst`.
-/
@[simp]
theorem mkConstCached_eval_eq_mkConst_eval {aig : AIG α} :
    ⟦aig.mkConstCached val, assign⟧ = ⟦aig.mkConst val, assign⟧ := by
  simp only [mkConstCached]
  split
  · next heq1 =>
    rw [denote_mkConst_cached heq1]
  · simp [mkConst, denote]

/--
If we find a cached gate declaration in the AIG, denoting it is equivalent to denoting `AIG.mkGate`.
-/
theorem denote_mkGate_cached {aig : AIG α} {input} {hit} :
    aig.cache.get? (.gate input.lhs.ref.gate input.rhs.ref.gate input.lhs.inv input.rhs.inv) = some hit
      →
    ⟦⟨aig, hit.idx, hit.hbound⟩, assign⟧
      =
    ⟦aig.mkGate input, assign⟧ := by
  intros
  have := hit.hvalid
  simp only [denote_mkGate]
  conv =>
    lhs
    unfold denote denote.go
  split <;> simp_all[denote]

theorem mkGateCached.go_le_size (aig : AIG α) (input : GateInput aig) :
    aig.decls.size ≤ (go aig input).aig.decls.size := by
  dsimp only [go]
  split
  · simp
  · split <;> try simp +arith [mkConstCached_le_size]
    split
    · simp +arith
    · split <;> simp +arith [mkConstCached_le_size]

/--
`AIG.mkGateCached` never shrinks the underlying AIG.
-/
theorem mkGateCached_le_size (aig : AIG α) (input : GateInput aig)
    : aig.decls.size ≤ (aig.mkGateCached input).aig.decls.size := by
  dsimp only [mkGateCached]
  split
  · apply mkGateCached.go_le_size
  · apply mkGateCached.go_le_size

theorem mkGateCached.go_decl_eq (aig : AIG α) (input : GateInput aig) :
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
        intros
        rw [LawfulOperator.decl_eq (f := AIG.mkConstCached)]
      · rw [← hres]
        intros
        rw [LawfulOperator.decl_eq (f := AIG.mkConstCached)]
      · rw [← hres]
        intros
        rw [LawfulOperator.decl_eq (f := AIG.mkConstCached)]
      · rw [← hres]
        intros
        rw [LawfulOperator.decl_eq (f := AIG.mkConstCached)]
      · rw [← hres]
        intros
        simp
      · rw [← hres]
        intros
        simp
      · rw [← hres]
        intros
        simp
      · rw [← hres]
        intros
        simp
      · split at hres
        · rw [← hres]
          intros
          simp
        · split at hres
          · rw [← hres]
            intros
            rw [AIG.LawfulOperator.decl_eq (f := AIG.mkConstCached)]
          · rw [← hres]
            dsimp only
            intro idx h1 h2
            rw [Array.getElem_push]
            simp [h2]

/--
The AIG produced by `AIG.mkGateCached` agrees with the input AIG on all indices that are valid for
both.
-/
theorem mkGateCached_decl_eq (aig : AIG α) (input : GateInput aig) :
    ∀ (idx : Nat) (h1) (h2), (aig.mkGateCached input).aig.decls[idx]'h1 = aig.decls[idx]'h2 := by
    generalize hres : mkGateCached aig input = res
    unfold mkGateCached at hres
    dsimp only at hres
    split at hres
    all_goals
      rw [← hres]
      intros
      rw [mkGateCached.go_decl_eq]

instance : LawfulOperator α GateInput mkGateCached where
  le_size := mkGateCached_le_size
  decl_eq := by
    intros
    apply mkGateCached_decl_eq

theorem mkGateCached.go_eval_eq_mkGate_eval {aig : AIG α} {input : GateInput aig} :
    ⟦go aig input, assign⟧ = ⟦aig.mkGate input, assign⟧ := by
  simp only [go]
  split
  · next heq1 =>
    rw [denote_mkGate_cached heq1]
  · split
    · next heq _ =>
      simp_all [denote_idx_const heq]
    · next heq _ =>
      simp_all [denote_idx_const heq]
    · next heq _ _ _ =>
      simp_all [denote_idx_const heq]
    · next heq _ _ _ =>
      simp_all [denote_idx_const heq]
    · next heq _ _ _ =>
      simp_all [denote_idx_const heq]
    · next heq _ _ _ =>
      simp_all [denote_idx_const heq]
    · next heq _ _ _ _ =>
      simp_all [denote_idx_const heq]
    · next heq _ _ _ =>
      simp_all [denote_idx_const heq]
    · split
      · next hif =>
        simp only [beq_false, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hif
        rcases hif with ⟨⟨hifeq, hlinv⟩, hrinv⟩
        replace hifeq : input.lhs.ref = input.rhs.ref := by
          rcases input with ⟨⟨⟨_, _⟩, _⟩, ⟨⟨_, _⟩, _⟩⟩
          simpa using hifeq
        simp [hlinv, hrinv, hifeq]
      · split
        · next hif =>
          simp only [Bool.and_eq_true, beq_iff_eq] at hif
          rcases hif with ⟨hifeq, hinv⟩
          replace hifeq : input.lhs.ref = input.rhs.ref := by
            rcases input with ⟨⟨⟨_, _⟩, _⟩, ⟨⟨_, _⟩, _⟩⟩
            simpa using hifeq
          simp [hifeq, hinv]
        · simp [mkGate, denote]

/--
The central equality theorem between `mkGateCached` and `mkGate`.
-/
@[simp]
theorem mkGateCached_eval_eq_mkGate_eval {aig : AIG α} {input : GateInput aig} :
    ⟦aig.mkGateCached input, assign⟧ = ⟦aig.mkGate input, assign⟧ := by
  simp only [mkGateCached]
  split
  · rw [mkGateCached.go_eval_eq_mkGate_eval]
  · rw [mkGateCached.go_eval_eq_mkGate_eval]
    simp only [denote_mkGate]
    rw [Bool.and_comm]

end AIG

end Sat
end Std
