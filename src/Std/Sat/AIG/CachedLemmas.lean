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
    ⟦aig, ⟨hit.idx, false, hit.hbound⟩, assign⟧ = ⟦aig.mkAtom v, assign⟧ := by
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
  | some and =>
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

theorem mkConstCached_aig (aig : AIG α) (val : Bool) : (aig.mkConstCached val).aig = aig := by
  simp [mkConstCached]

/--
The AIG produced by `AIG.mkConstCached` agrees with the input AIG on all indices that are valid for
both.
-/
theorem mkConstCached_decl_eq (aig : AIG α) (val : Bool) (idx : Nat) {h : idx < aig.decls.size} :
    (aig.mkConstCached val).aig.decls[idx]'h = aig.decls[idx] := by
  simp [mkConstCached_aig]

/--
`AIG.mkConstCached` never shrinks the underlying AIG.
-/
theorem mkConstCached_le_size (aig : AIG α) (val : Bool) :
    aig.decls.size ≤ (aig.mkConstCached val).aig.decls.size := by
  simp [mkConstCached_aig]

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
  simp only [mkConstCached, denote_mkConst]
  unfold denote denote.go
  split
  all_goals
  · next heq => simp [aig.hconst] at heq <;> simp

/--
If we find a cached and gate declaration in the AIG, denoting it is equivalent to denoting `AIG.mkAndGate`.
-/
theorem denote_mkAndGate_cached {aig : AIG α} {input} {hit} :
    aig.cache.get? (.and (.mk input.lhs.gate input.lhs.invert) (.mk input.rhs.gate input.rhs.invert)) = some hit
      →
    ⟦⟨aig, hit.idx, false, hit.hbound⟩, assign⟧
      =
    ⟦aig.mkAndGate input, assign⟧ := by
  intros
  have := hit.hvalid
  simp only [denote_mkAndGate]
  conv =>
    lhs
    unfold denote denote.go
  split <;> simp_all [denote]

theorem mkAndGateCached.go_le_size (aig : AIG α) (input : BinaryInput aig) :
    aig.decls.size ≤ (go aig input).aig.decls.size := by
  dsimp only [go]
  split
  · simp
  · split <;> try simp [mkConstCached_le_size]
    split
    · split
      · simp
      · simp [mkConstCached_le_size]
    · simp

/--
`AIG.mkAndGateCached` never shrinks the underlying AIG.
-/
theorem mkAndGateCached_le_size (aig : AIG α) (input : BinaryInput aig)
    : aig.decls.size ≤ (aig.mkAndGateCached input).aig.decls.size := by
  dsimp only [mkAndGateCached]
  split
  · apply mkAndGateCached.go_le_size
  · apply mkAndGateCached.go_le_size

theorem mkAndGateCached.go_decl_eq (aig : AIG α) (input : BinaryInput aig) :
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
            rw [AIG.LawfulOperator.decl_eq (f := AIG.mkConstCached)]
        · rw [← hres]
          dsimp only
          intro idx h1 h2
          rw [Array.getElem_push]
          simp [h2]

/--
The AIG produced by `AIG.mkAndGateCached` agrees with the input AIG on all indices that are valid for
both.
-/
theorem mkAndGateCached_decl_eq (aig : AIG α) (input : BinaryInput aig) :
    ∀ (idx : Nat) (h1) (h2), (aig.mkAndGateCached input).aig.decls[idx]'h1 = aig.decls[idx]'h2 := by
    generalize hres : mkAndGateCached aig input = res
    unfold mkAndGateCached at hres
    dsimp only at hres
    split at hres
    all_goals
      rw [← hres]
      intros
      rw [mkAndGateCached.go_decl_eq]

instance : LawfulOperator α BinaryInput mkAndGateCached where
  le_size := mkAndGateCached_le_size
  decl_eq := by
    intros
    apply mkAndGateCached_decl_eq

theorem mkAndGateCached.go_eval_eq_mkAndGate_eval {aig : AIG α} {input : BinaryInput aig} :
    ⟦go aig input, assign⟧ = ⟦aig.mkAndGate input, assign⟧ := by
  simp only [go]
  split
  · next heq1 =>
    rw [denote_mkAndGate_cached heq1]
  · split
    · simp_all [denote_getConstant]
    · simp_all [denote_getConstant]
    · simp_all [denote_getConstant]
    · simp_all [denote_getConstant]
    · rcases input with ⟨⟨lhs, linv, hlgate⟩, ⟨rhs, rinv, hrgate⟩⟩
      split
      · split
        · simp_all
        · next hif =>
          simp_all
          have := Bool.eq_not_of_ne hif
          simp_all
      · simp [mkAndGate, denote]

/--
The central equality theorem between `mkAndGateCached` and `mkAndGate`.
-/
@[simp]
theorem mkAndGateCached_eval_eq_mkAndGate_eval {aig : AIG α} {input : BinaryInput aig} :
    ⟦aig.mkAndGateCached input, assign⟧ = ⟦aig.mkAndGate input, assign⟧ := by
  simp only [mkAndGateCached]
  split
  · rw [mkAndGateCached.go_eval_eq_mkAndGate_eval]
  · rw [mkAndGateCached.go_eval_eq_mkAndGate_eval]
    simp only [denote_mkAndGate]
    rw [Bool.and_comm]

/--
If we find a cached xor gate declaration in the AIG, denoting it is equivalent to denoting `AIG.mkXorGate`.
-/
theorem denote_mkXorGate_cached {aig : AIG α} {input} {hit} :
    aig.cache.get? (.xor (.mk input.lhs.gate input.lhs.invert) (.mk input.rhs.gate input.rhs.invert)) = some hit
      →
    ⟦⟨aig, hit.idx, false, hit.hbound⟩, assign⟧
      =
    ⟦aig.mkXorGate input, assign⟧ := by
  intros
  have := hit.hvalid
  simp only [denote_mkXorGate]
  conv =>
    lhs
    unfold denote denote.go
  split <;> simp_all [denote]

theorem mkXorGateCached.go_le_size (aig : AIG α) (input : BinaryInput aig) :
    aig.decls.size ≤ (go aig input).aig.decls.size := by
  dsimp only [go]
  split
  · simp
  · split <;> try simp [mkConstCached_le_size]
    split
    · simp [mkConstCached_le_size]
    · simp

/--
`AIG.mkXorGateCached` never shrinks the underlying AIG.
-/
theorem mkXorGateCached_le_size (aig : AIG α) (input : BinaryInput aig)
    : aig.decls.size ≤ (aig.mkXorGateCached input).aig.decls.size := by
  dsimp only [mkXorGateCached]
  split
  · apply mkXorGateCached.go_le_size
  · apply mkXorGateCached.go_le_size

theorem mkXorGateCached.go_decl_eq (aig : AIG α) (input : BinaryInput aig) :
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
        simp
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
The AIG produced by `AIG.mkXorGateCached` agrees with the input AIG on all indices that are valid for
both.
-/
theorem mkXorGateCached_decl_eq (aig : AIG α) (input : BinaryInput aig) :
    ∀ (idx : Nat) (h1) (h2), (aig.mkXorGateCached input).aig.decls[idx]'h1 = aig.decls[idx]'h2 := by
    generalize hres : mkXorGateCached aig input = res
    unfold mkXorGateCached at hres
    dsimp only at hres
    split at hres
    all_goals
      rw [← hres]
      intros
      rw [mkXorGateCached.go_decl_eq]

instance : LawfulOperator α BinaryInput mkXorGateCached where
  le_size := mkXorGateCached_le_size
  decl_eq := by
    intros
    apply mkXorGateCached_decl_eq

theorem mkXorGateCached.go_eval_eq_mkXorGate_eval {aig : AIG α} {input : BinaryInput aig} :
    ⟦go aig input, assign⟧ = ⟦aig.mkXorGate input, assign⟧ := by
  simp only [go]
  split
  · next heq1 =>
    rw [denote_mkXorGate_cached heq1]
  · split
    · next invert _ =>
      by_cases invert
      all_goals
      · simp_all [denote_getConstant]
    · next invert _ hconst =>
      have := hconst invert
      by_cases invert
      all_goals
      · simp_all [denote_getConstant]
    · rcases input with ⟨⟨lhs, linv, hlgate⟩, ⟨rhs, rinv, hrgate⟩⟩
      split
      · by_cases (linv = rinv)
        · simp_all
        · next hne => simp_all [Bool.eq_not_of_ne hne]
      · simp [mkXorGate, denote]

/--
The central equality theorem between `mkAndGateCached` and `mkAndGate`.
-/
@[simp]
theorem mkXorGateCached_eval_eq_mkXorGate_eval {aig : AIG α} {input : BinaryInput aig} :
    ⟦aig.mkXorGateCached input, assign⟧ = ⟦aig.mkXorGate input, assign⟧ := by
  simp only [mkXorGateCached]
  split
  · rw [mkXorGateCached.go_eval_eq_mkXorGate_eval]
  · rw [mkXorGateCached.go_eval_eq_mkXorGate_eval]
    simp only [denote_mkXorGate]
    rw [Bool.xor_comm]

end AIG

end Sat
end Std
