/-
Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Clune
-/
prelude
import Std.Tactic.BVDecide.LRAT.Internal.Formula.Implementation
import Std.Tactic.BVDecide.LRAT.Internal.CNF

/-!
This module contains basic statements about the invariants that are satisfied by the LRAT checker
implementation in `Implementation`.
-/

namespace Std.Tactic.BVDecide
namespace LRAT
namespace Internal

namespace DefaultFormula

open Std.Sat
open DefaultClause DefaultFormula Assignment

attribute [local grind] insert ofArray

/--
This invariant states that if the `assignments` field of a default formula `f` indicates that `f`
contains an assignment `b` at index `i`, then the unit literal `(i, b)` must be included in `f`.
Default formulas are expected to satisfy this invariant at all times except during intermediate
stages of unit propagation (during which, default formulas are only expected to satisfy the more
lenient `AssignmentsInvariant` defined below).
-/
def StrongAssignmentsInvariant {n : Nat} (f : DefaultFormula n) : Prop :=
  ∃ hsize : f.assignments.size = n, ∀ i : PosFin n, ∀ b : Bool,
    hasAssignment b (f.assignments[i.1]'(by rw [hsize]; exact i.2.2)) →
    (unit (i, b)) ∈ toList f

/--
This invariant states that if the `assignments` field of a default formula `f` indicates that `f`
contains an assignment `b` at index `i`, then the unit literal `(i, b)` is entailed by `f`. This is
distinct from the `StrongAssignmentsInvariant` defined above in that the entailment described here
does not require explicitly containing the literal `(i, b)`. For example, if `f` contains `(i, b) ∨ (j, b')`
as well as `(i, b) ∨ (j, ¬b')`, then the `AssignmentsInvariant` would permit the `assignments` field of `f`
to contain assignment `b` at index `i`, but the `StrongAssignmentsInvariant` would not.
-/
def AssignmentsInvariant {n : Nat} (f : DefaultFormula n) : Prop :=
  ∃ hsize : f.assignments.size = n, ∀ i : PosFin n, ∀ b : Bool,
    hasAssignment b (f.assignments[i.1]'(by rw [hsize]; exact i.2.2)) →
    Limplies (PosFin n) f (i, b)

theorem assignmentsInvariant_of_strongAssignmentsInvariant {n : Nat} (f : DefaultFormula n) :
    StrongAssignmentsInvariant f → AssignmentsInvariant f := by
  intro ⟨hsize, h⟩
  apply Exists.intro hsize
  intro i b hb p pf
  specialize h i b hb
  simp only [(· ⊨ ·), 
    Bool.decide_coe, List.all_eq_true] at pf
  specialize pf (unit (i, b)) h
  simpa [(· ⊨ ·), Clause.eval, unit_eq, Clause.toList] using pf

theorem limplies_of_assignmentsInvariant {n : Nat} (f : DefaultFormula n)
    (f_AssignmentsInvariant : AssignmentsInvariant f) :
    Limplies (PosFin n) f f.assignments := by
  intro p pf
  rcases f_AssignmentsInvariant with ⟨hsize, f_AssignmentsInvariant⟩
  simp only [(· ⊨ ·), Bool.not_eq_true]
  intro i
  specialize f_AssignmentsInvariant i (decide (p i = false))
  by_cases hasAssignment (decide (p i = false)) (f.assignments[i.1]'(by rw [hsize]; exact i.2.2))
  · next h =>
    specialize f_AssignmentsInvariant h p pf
    by_cases hpi : p i <;> simp [hpi, Entails.eval] at f_AssignmentsInvariant
  · next h => simp_all [i.2.2]

/--
performRupAdd adds to f.rupUnits and then clears f.rupUnits. If f begins with some units in f.rupUnits,
then performRupAdd will clear more than it intended to which will break the correctness of rupAdd_result.
-/
def ReadyForRupAdd {n : Nat} (f : DefaultFormula n) : Prop := f.rupUnits = #[] ∧ StrongAssignmentsInvariant f

/--
performRatAdd adds to f.rupUnits and f.ratUnits and then clears both. If f begins with some units in either,
then performRatAdd will clear more than it intended to which will break the correctness of ratAdd_result
-/
def ReadyForRatAdd {n : Nat} (f : DefaultFormula n) : Prop := f.ratUnits = #[] ∧ ReadyForRupAdd f

theorem rupUnits_insert {n : Nat} (f : DefaultFormula n) (c : DefaultClause n) :
    (insert f c).rupUnits = f.rupUnits := by
  simp only [insert]
  grind

theorem ratUnits_insert {n : Nat} (f : DefaultFormula n) (c : DefaultClause n) :
    (insert f c).ratUnits = f.ratUnits := by
  simp only [insert]
  grind

theorem size_ofArray_fold_fn {n : Nat} (assignments : Array Assignment)
    (cOpt : Option (DefaultClause n)) :
    (ofArray_fold_fn assignments cOpt).size = assignments.size := by
  rw [ofArray_fold_fn.eq_def]
  grind

theorem readyForRupAdd_ofArray {n : Nat} (arr : Array (Option (DefaultClause n))) :
    ReadyForRupAdd (ofArray arr) := by
  constructor
  · grind
  · have hsize : (ofArray arr).assignments.size = n := by
      simp only [ofArray, ← Array.foldl_toList]
      have hb : (Array.replicate n unassigned).size = n := by simp only [Array.size_replicate]
      have hl (acc : Array Assignment) (ih : acc.size = n) (cOpt : Option (DefaultClause n)) (_cOpt_in_arr : cOpt ∈ arr.toList) :
        (ofArray_fold_fn acc cOpt).size = n := by rw [size_ofArray_fold_fn acc cOpt, ih]
      exact List.foldlRecOn arr.toList ofArray_fold_fn hb hl
    apply Exists.intro hsize
    let ModifiedAssignmentsInvariant (assignments : Array Assignment) : Prop :=
      ∃ hsize : assignments.size = n,
        ∀ i : PosFin n, ∀ b : Bool, hasAssignment b (assignments[i.1]'(by rw [hsize]; exact i.2.2)) →
        (unit (i, b)) ∈ toList (ofArray arr)
    have hb : ModifiedAssignmentsInvariant (.replicate n unassigned) := by
      have hsize : (Array.replicate n unassigned).size = n := by simp only [Array.size_replicate]
      apply Exists.intro hsize
      intro i b h
      by_cases hb : b <;> simp [hasAssignment, hb, hasPosAssignment, hasNegAssignment] at h
    have hl (acc : Array Assignment) (ih : ModifiedAssignmentsInvariant acc) (cOpt : Option (DefaultClause n))
      (cOpt_in_arr : cOpt ∈ arr.toList) : ModifiedAssignmentsInvariant (ofArray_fold_fn acc cOpt) := by
      have hsize : (ofArray_fold_fn acc cOpt).size = n := by rw [size_ofArray_fold_fn, ih.1]
      apply Exists.intro hsize
      intro i b h
      simp only [ofArray_fold_fn] at h
      split at h
      · exact ih.2 i b h
      · next cOpt c =>
        match heq : isUnit c with
        | none =>
          simp only [heq] at h
          exact ih.2 i b h
        | some (l, true) =>
          simp only [heq] at h
          rcases ih with ⟨hsize, ih⟩
          by_cases i = l.1
          · next i_eq_l =>
            simp only [i_eq_l, Array.getElem_modify_self] at h
            by_cases b
            · next b_eq_true =>
              rw [isUnit_iff, DefaultClause.toList] at heq
              simp only [toList, ofArray, List.map, List.append_nil, List.mem_filterMap, id_eq, exists_eq_right]
              have i_eq_l : i = l := Subtype.ext i_eq_l
              simp only [unit, b_eq_true, i_eq_l]
              have c_def : c = ⟨c.clause, c.nodupkey, c.nodup⟩ := rfl
              simp only [heq] at c_def
              grind
            · next b_eq_false =>
              simp only [Bool.not_eq_true] at b_eq_false
              simp only [hasAssignment, b_eq_false, ite_false, hasNeg_addPos, reduceCtorEq] at h
              specialize ih l false
              simp only [hasAssignment] at ih
              rw [b_eq_false, Subtype.ext i_eq_l]
              exact ih h
          · next i_ne_l => grind
        | some (l, false) =>
          simp only [heq] at h
          rcases ih with ⟨hsize, ih⟩
          by_cases i = l.1
          · next i_eq_l =>
            simp only [i_eq_l, Array.getElem_modify_self] at h
            by_cases b
            · next b_eq_true =>
              simp only [hasAssignment, b_eq_true, ite_true, hasPos_addNeg] at h
              specialize ih l true
              simp only [hasAssignment] at ih
              rw [b_eq_true, Subtype.ext i_eq_l]
              grind
            · next b_eq_false =>
              rw [isUnit_iff, DefaultClause.toList] at heq
              simp only [toList, ofArray, List.map, List.append_nil, List.mem_filterMap, id_eq, exists_eq_right]
              have i_eq_l : i = l := Subtype.ext i_eq_l
              simp only [unit, b_eq_false, i_eq_l]
              have c_def : c = ⟨c.clause, c.nodupkey, c.nodup⟩ := rfl
              simp only [heq] at c_def
              grind
          · next i_ne_l => grind
    rcases List.foldlRecOn arr.toList ofArray_fold_fn hb hl with ⟨_h_size, h'⟩
    grind [ofArray]

theorem readyForRatAdd_ofArray {n : Nat} (arr : Array (Option (DefaultClause n))) :
    ReadyForRatAdd (ofArray arr) := by
  constructor
  · grind
  · grind [readyForRupAdd_ofArray]

theorem insert_iff {n : Nat} (f : DefaultFormula n) (c1 : DefaultClause n) (c2 : DefaultClause n) :
    c2 ∈ toList (insert f c1) ↔ c2 = c1 ∨ c2 ∈ toList f := by
  simp only [toList, List.mem_append, List.mem_filterMap, id_eq, exists_eq_right]
  simp only [insert]
  grind

theorem limplies_insert {n : Nat} (f : DefaultFormula n) (c : DefaultClause n) :
    Limplies (PosFin n) (insert f c) f := by
  simp only [Limplies, formulaEntails_def, List.all_eq_true]
  grind [insert_iff]

theorem size_assignments_insert {n : Nat} (f : DefaultFormula n) (c : DefaultClause n) :
    (insert f c).assignments.size = f.assignments.size := by
  simp only [insert]
  grind

theorem readyForRupAdd_insert {n : Nat} (f : DefaultFormula n) (c : DefaultClause n) :
    ReadyForRupAdd f → ReadyForRupAdd (insert f c) := by
  intro f_readyForRupAdd
  simp only [insert]
  split
  · refine ⟨f_readyForRupAdd.1, f_readyForRupAdd.2.1, ?_⟩
    intro i b hb
    have hf := f_readyForRupAdd.2.2 i b hb
    simp only [toList] at hf ⊢
    grind
  · next l hc =>
    have hsize : (Array.modify f.assignments l.1 addPosAssignment).size = n := by
      rw [Array.size_modify, f_readyForRupAdd.2.1]
    refine ⟨f_readyForRupAdd.1, hsize, ?_⟩
    intro i b hb
    have hf := f_readyForRupAdd.2.2 i b
    have i_in_bounds : i.1 < f.assignments.size := by rw [f_readyForRupAdd.2.1]; exact i.2.2
    simp only at hb
    by_cases (i, b) = (l, true)
    · next ib_eq_c =>
      simp only [toList, Array.toList_push, List.append_assoc, List.mem_append, List.mem_filterMap,
        List.mem_singleton, id_eq, exists_eq_right, Option.some.injEq, List.mem_map, Prod.exists, Bool.exists_bool]
      apply Or.inl ∘ Or.inr
      rw [isUnit_iff, DefaultClause.toList, ← ib_eq_c] at hc
      apply DefaultClause.ext
      simp only [unit, hc]
    · next ib_ne_c =>
      have hb' : hasAssignment b f.assignments[i.1] := by
        by_cases l.1 = i.1
        · next l_eq_i =>
          have b_eq_false : b = false := by
            by_cases b = true
            · next b_eq_true =>
              simp only [b_eq_true, Subtype.ext l_eq_i, not_true] at ib_ne_c
            · next b_eq_false => grind
          simp only [hasAssignment, b_eq_false, l_eq_i, Array.getElem_modify_self, ite_false, hasNeg_addPos, reduceCtorEq] at hb
          grind [hasAssignment]
        · next l_ne_i => grind
      specialize hf hb'
      simp only [toList] at hf ⊢
      grind
  · next l hc =>
    have hsize : (Array.modify f.assignments l.1 addNegAssignment).size = n := by
      rw [Array.size_modify, f_readyForRupAdd.2.1]
    refine ⟨f_readyForRupAdd.1, hsize, ?_⟩
    intro i b hb
    have hf := f_readyForRupAdd.2.2 i b
    have i_in_bounds : i.1 < f.assignments.size := by rw [f_readyForRupAdd.2.1]; exact i.2.2
    simp only at hb
    by_cases (i, b) = (l, false)
    · next ib_eq_c =>
      simp only [toList, Array.toList_push, List.append_assoc, List.mem_append, List.mem_filterMap,
        List.mem_singleton, id_eq, exists_eq_right, Option.some.injEq, List.mem_map, Prod.exists, Bool.exists_bool]
      apply Or.inl ∘ Or.inr
      rw [isUnit_iff, DefaultClause.toList, ← ib_eq_c] at hc
      apply DefaultClause.ext
      simp only [unit, hc]
    · next ib_ne_c =>
      have hb' : hasAssignment b f.assignments[i.1] := by
        by_cases l.1 = i.1
        · next l_eq_i =>
          have b_eq_false : b = true := by
            by_cases b = true
            · assumption
            · next b_eq_false =>
              simp only [b_eq_false, Subtype.ext l_eq_i, not_true] at ib_ne_c
          grind [hasAssignment, hasPos_addNeg]
        · next l_ne_i => grind
      specialize hf hb'
      simp only [toList] at hf ⊢
      grind

theorem readyForRatAdd_insert {n : Nat} (f : DefaultFormula n) (c : DefaultClause n) :
    ReadyForRatAdd f → ReadyForRatAdd (insert f c) := by
  intro h
  constructor
  · simp only [insert, h.1]
    grind
  · exact readyForRupAdd_insert f c h.2

theorem mem_of_insertRupUnits {n : Nat} (f : DefaultFormula n) (units : CNF.Clause (PosFin n))
    (c : DefaultClause n) :
    c ∈ toList (insertRupUnits f units).1 → c ∈ units.map Clause.unit ∨ c ∈ toList f := by
  simp only [toList, insertRupUnits, List.append_assoc, List.mem_append,
    List.mem_filterMap, id_eq, exists_eq_right, List.mem_map, Prod.exists, Bool.exists_bool]
  intro h
  have hb : ∀ l : Literal (PosFin n), l ∈ (f.rupUnits, f.assignments, false).1.toList → (l ∈ f.rupUnits.toList ∨ l ∈ units) := by
    grind
  have hl (acc : Array (Literal (PosFin n)) × Array Assignment × Bool)
    (ih : ∀ l : Literal (PosFin n), l ∈ acc.1.toList → l ∈ f.rupUnits.toList ∨ l ∈ units)
    (unit : Literal (PosFin n)) (unit_in_units : unit ∈ units) :
    ∀ l : Literal (PosFin n), l ∈ (insertUnit acc unit).1.toList → (l ∈ f.rupUnits.toList ∨ l ∈ units) := by
    intro l hl
    rw [insertUnit.eq_def] at hl
    grind
  have h_insertUnit_fold := List.foldlRecOn units insertUnit hb hl
  rcases h with h | ⟨i, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ | h
  · grind
  · rcases h_insertUnit_fold (i, false) h1 with h_insertUnit_fold | h_insertUnit_fold
    · apply Or.inr ∘ Or.inr ∘ Or.inl ∘ Exists.intro i ∘ Or.inl
      grind
    · apply Or.inl ∘ Exists.intro i ∘ Or.inl
      exact ⟨by grind, h2⟩
  · rcases h_insertUnit_fold (i, true) h1 with h_insertUnit_fold | h_insertUnit_fold
    · grind
    · apply Or.inl ∘ Exists.intro i ∘ Or.inr
      exact ⟨by grind, h2⟩
  · grind

theorem mem_of_insertRatUnits {n : Nat} (f : DefaultFormula n) (units : CNF.Clause (PosFin n))
    (c : DefaultClause n) :
    c ∈ toList (insertRatUnits f units).1 → c ∈ units.map Clause.unit ∨ c ∈ toList f := by
  simp only [toList, insertRatUnits, List.append_assoc, List.mem_append,
    List.mem_filterMap, id_eq, exists_eq_right, List.mem_map, Prod.exists, Bool.exists_bool]
  intro h
  have hb : ∀ l : Literal (PosFin n), l ∈ (f.ratUnits, f.assignments, false).1.toList → (l ∈ f.ratUnits.toList ∨ l ∈ units) :=
    fun _ => Or.inl
  have hl (acc : Array (Literal (PosFin n)) × Array Assignment × Bool)
    (ih : ∀ l : Literal (PosFin n), l ∈ acc.1.toList → l ∈ f.ratUnits.toList ∨ l ∈ units)
    (unit : Literal (PosFin n)) (unit_in_units : unit ∈ units) :
    ∀ l : Literal (PosFin n), l ∈ (insertUnit acc unit).1.toList → (l ∈ f.ratUnits.toList ∨ l ∈ units) := by
    grind [insertUnit]
  have h_insertUnit_fold := List.foldlRecOn units insertUnit hb hl
  rcases h with h | h | ⟨i, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
  · grind
  · grind
  · rcases h_insertUnit_fold (i, false) h1 with h_insertUnit_fold | h_insertUnit_fold
    · grind
    · apply Or.inl ∘ Exists.intro i ∘ Or.inl
      exact ⟨h_insertUnit_fold, h2⟩
  · rcases h_insertUnit_fold (i, true) h1 with h_insertUnit_fold | h_insertUnit_fold
    · grind
    · apply Or.inl ∘ Exists.intro i ∘ Or.inr
      exact ⟨h_insertUnit_fold, h2⟩

theorem deleteOne_preserves_rupUnits {n : Nat} (f : DefaultFormula n) (id : Nat) :
    (deleteOne f id).rupUnits = f.rupUnits := by
  simp only [deleteOne]
  grind

theorem deleteOne_preserves_assignments_size {n : Nat} (f : DefaultFormula n) (id : Nat) :
    (deleteOne f id).assignments.size = f.assignments.size := by
  simp only [deleteOne]
  grind

theorem deleteOne_preserves_strongAssignmentsInvariant {n : Nat} (f : DefaultFormula n) (id : Nat) :
    StrongAssignmentsInvariant f → StrongAssignmentsInvariant (deleteOne f id) := by
  intro hf
  rcases hf with ⟨hsize, hf⟩
  have hsize' : (deleteOne f id).assignments.size = n := by
    simp only [← hsize]
    exact deleteOne_preserves_assignments_size f id
  apply Exists.intro hsize'
  intro i b hb
  have i_in_bounds : i.1 < f.assignments.size := by rw [hsize]; exact i.2.2
  simp only [deleteOne]
  match heq : f.clauses[id]! with
  | none =>
    simp only
    simp only [deleteOne, heq] at hb
    exact hf i b hb
  | some c =>
    by_cases hl : ∃ l : Literal (PosFin n), c = unit l
    · rcases hl with ⟨l, hl⟩
      simp only [unit] at hl
      simp only [hl]
      simp only [deleteOne, heq, hl] at hb
      by_cases l.1.1 = i.1
      · next l_eq_i =>
        simp only [l_eq_i, Array.getElem_modify_self] at hb
        have l_ne_b : l.2 ≠ b := by grind [not_has_remove]
        replace l_ne_b := Bool.eq_not_of_ne l_ne_b
        simp only [l_ne_b] at hb
        have hb := has_remove_irrelevant f.assignments[i.1] b hb
        specialize hf i b hb
        simp only [toList, List.append_assoc, List.mem_append, List.mem_filterMap, id_eq,
          exists_eq_right, List.mem_map, Prod.exists, Bool.exists_bool] at hf
        simp only [toList, List.append_assoc, List.mem_append, List.mem_filterMap, id_eq,
          exists_eq_right, List.mem_map, Prod.exists, Bool.exists_bool]
        rcases hf with hf | hf
        · apply Or.inl
          simp only [Array.set!, Array.setIfInBounds]
          split
          · rcases List.getElem_of_mem hf with ⟨idx, hbound, hidx⟩
            have idx_in_bounds : idx < List.length (List.set f.clauses.toList id none) := by grind
            rw [List.mem_iff_get]
            apply Exists.intro ⟨idx, idx_in_bounds⟩
            grind [unit]
          · exact hf
        · exact Or.inr hf
      · next l_ne_i =>
        simp only [Array.getElem_modify_of_ne l_ne_i] at hb
        specialize hf i b hb
        simp only [toList, List.append_assoc, List.mem_append, List.mem_filterMap, id_eq,
          exists_eq_right, List.mem_map, Prod.exists, Bool.exists_bool] at hf
        simp only [toList, List.append_assoc, List.mem_append, List.mem_filterMap, id_eq,
          exists_eq_right, List.mem_map, Prod.exists, Bool.exists_bool]
        rcases hf with hf | hf
        · apply Or.inl
          simp only [Array.set!, Array.setIfInBounds]
          split
          · rcases List.getElem_of_mem hf with ⟨idx, hbound, hidx⟩
            rw [List.mem_iff_get]
            have idx_in_bounds : idx < List.length (List.set f.clauses.toList id none) := by grind
            apply Exists.intro ⟨idx, idx_in_bounds⟩
            grind [unit]
          · exact hf
        · exact Or.inr hf
    · simp only [Prod.exists, Bool.exists_bool, not_exists, not_or, unit] at hl
      split
      · next some_eq_none => grind
      · next l _ _ heq => grind [cases Bool]
      · have deleteOne_f_rw : deleteOne f id = ⟨Array.set! f.clauses id none, f.rupUnits, f.ratUnits, f.assignments⟩ := by
          simp only [deleteOne]
          grind
        simp only [deleteOne_f_rw] at hb
        specialize hf i b hb
        simp only [toList, List.append_assoc, List.mem_append, List.mem_filterMap, id_eq,
          exists_eq_right, List.mem_map, Prod.exists, Bool.exists_bool] at hf
        simp only [toList, List.append_assoc, List.mem_append, List.mem_filterMap, id_eq,
          exists_eq_right, List.mem_map, Prod.exists, Bool.exists_bool]
        rcases hf with hf | hf
        · apply Or.inl
          simp only [Array.set!, Array.setIfInBounds]
          split
          · rcases List.getElem_of_mem hf with ⟨idx, hbound, hidx⟩
            rw [List.mem_iff_get]
            have idx_in_bounds : idx < List.length (List.set f.clauses.toList id none) := by
              grind
            apply Exists.intro ⟨idx, idx_in_bounds⟩
            grind [unit]
          · exact hf
        · exact Or.inr hf

theorem readyForRupAdd_delete {n : Nat} (f : DefaultFormula n) (arr : Array Nat) :
    ReadyForRupAdd f → ReadyForRupAdd (delete f arr) := by
  intro h
  rw [delete, ← Array.foldl_toList]
  constructor
  · have hb : f.rupUnits = #[] := h.1
    have hl (acc : DefaultFormula n) (ih : acc.rupUnits = #[]) (id : Nat) (_id_in_arr : id ∈ arr.toList) :
      (deleteOne acc id).rupUnits = #[] := by rw [deleteOne_preserves_rupUnits, ih]
    exact List.foldlRecOn arr.toList deleteOne hb hl
  · have hl (acc : DefaultFormula n) (ih : StrongAssignmentsInvariant acc) (id : Nat) (_id_in_arr : id ∈ arr.toList) :
      StrongAssignmentsInvariant (deleteOne acc id) := deleteOne_preserves_strongAssignmentsInvariant acc id ih
    exact List.foldlRecOn arr.toList deleteOne h.2 hl

theorem deleteOne_preserves_ratUnits {n : Nat} (f : DefaultFormula n) (id : Nat) :
    (deleteOne f id).ratUnits = f.ratUnits := by
  simp only [deleteOne]
  grind

theorem readyForRatAdd_delete {n : Nat} (f : DefaultFormula n) (arr : Array Nat) :
    ReadyForRatAdd f → ReadyForRatAdd (delete f arr) := by
  intro h
  constructor
  · rw [delete, ← Array.foldl_toList]
    have hl (acc : DefaultFormula n) (ih : acc.ratUnits = #[]) (id : Nat) (_id_in_arr : id ∈ arr.toList) :
      (deleteOne acc id).ratUnits = #[] := by grind [deleteOne_preserves_ratUnits]
    exact List.foldlRecOn arr.toList deleteOne h.1 hl
  · exact readyForRupAdd_delete f arr h.2

theorem deleteOne_subset (f : DefaultFormula n) (id : Nat) (c : DefaultClause n) :
    c ∈ toList (deleteOne f id) → c ∈ toList f := by
  simp only [deleteOne]
  intro h1
  rw [toList] at h1 ⊢
  split at h1 <;> grind

theorem delete_subset (f : DefaultFormula n) (arr : Array Nat) (c : DefaultClause n) :
    c ∈ toList (delete f arr) → c ∈ toList f := by
  simp only [delete, ← Array.foldl_toList]
  have hl (f' : DefaultFormula n) (ih : c ∈ toList f' → c ∈ toList f) (id : Nat) (_ : id ∈ arr.toList) :
    c ∈ toList (deleteOne f' id) → c ∈ toList f := by grind [deleteOne_subset]
  exact List.foldlRecOn arr.toList deleteOne id hl

end DefaultFormula

end Internal
end LRAT
end Std.Tactic.BVDecide
