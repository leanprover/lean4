/-
Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Clune
-/
prelude
import Std.Tactic.BVDecide.LRAT.Internal.Formula.Lemmas

/-!
This module contains the implementation of RUP-based clause adding for the default LRAT checker
implementation.
-/

namespace Std.Tactic.BVDecide
namespace LRAT
namespace Internal

namespace DefaultFormula

open Std.Sat
open DefaultClause DefaultFormula Assignment

theorem size_insertUnit {n : Nat} (units : Array (Literal (PosFin n)))
    (assignments : Array Assignment) (b : Bool) (l : Literal (PosFin n)) :
    (insertUnit (units, assignments, b) l).2.1.size = assignments.size := by
  simp only [insertUnit]
  split <;> simp

theorem size_insertUnit_fold :
    ∀ unitsAcc : Array (Literal (PosFin n)), ∀ assignments : Array Assignment, ∀ b : Bool,
      Array.size (List.foldl insertUnit (unitsAcc, assignments, b) units).2.1 = assignments.size := by
  induction units
  · simp only [List.foldl, forall_const]
  · next hd tl ih =>
    intro unitsAcc assignments b
    simp only [List.foldl]
    let hd_res := insertUnit (unitsAcc, assignments, b) hd
    specialize ih hd_res.1 hd_res.2.1 hd_res.2.2
    rw [ih, size_insertUnit]

theorem size_assignments_insertRupUnits {n : Nat} (f : DefaultFormula n)
    (units : CNF.Clause (PosFin n)) :
    (f.insertRupUnits units).1.assignments.size = f.assignments.size := by
  simp only [insertRupUnits]
  exact size_insertUnit_fold f.rupUnits f.assignments false

theorem clauses_insertRupUnits {n : Nat} (f : DefaultFormula n)
    (units : CNF.Clause (PosFin n)) :
    (f.insertRupUnits units).1.clauses = f.clauses := by
  rw [insertRupUnits]

theorem ratUnits_insertRupUnits {n : Nat} (f : DefaultFormula n)
    (units : CNF.Clause (PosFin n)) :
    (f.insertRupUnits units).1.ratUnits = f.ratUnits := by
  rw [insertRupUnits]

def InsertUnitInvariant {n : Nat} (original_assignments : Array Assignment)
    (original_assignments_size : original_assignments.size = n) (units : Array (Literal (PosFin n)))
    (assignments : Array Assignment) (assignments_size : assignments.size = n) :
    Prop := ∀ i : Fin n,
  let assignments_i := assignments[i.1]'(by rw [assignments_size]; exact i.2)
  let original_assignments_i := original_assignments[i.1]'(by rw [original_assignments_size] ; exact i.2)
  -- Case 1: i doesn't appear in units, so assignments_i and fassignments_i are equal
  (assignments_i = original_assignments_i ∧ ∀ j : Fin units.size, units[j].1.1 ≠ i.1) ∨
  -- Case 2: (i, b) appears but (i, ¬b) doesn't so assignments_i = addAssignment b fassignments_i
  (∃ j : Fin units.size, ∃ b : Bool, ∃ i_gt_zero : i.1 > 0,
    units[j] = ⟨⟨i.1, ⟨i_gt_zero, i.2⟩⟩, b⟩ ∧ assignments_i = addAssignment b original_assignments_i ∧
    ¬(hasAssignment b original_assignments_i) ∧ ∀ k : Fin units.size, k ≠ j → units[k].1.1 ≠ i.1) ∨
  -- Case 3: (i, true) and (i, false) both appear so assignments_i = both and fassignments_i = unassigned
  (∃ j1 : Fin units.size, ∃ j2 : Fin units.size, ∃ i_gt_zero : i.1 > 0,
    units[j1] = ⟨⟨i.1, ⟨i_gt_zero, i.2⟩⟩, true⟩ ∧ units[j2] = ⟨⟨i.1, ⟨i_gt_zero, i.2⟩⟩, false⟩ ∧
    assignments_i = both ∧ original_assignments_i = unassigned ∧ ∀ k : Fin units.size, k ≠ j1 → k ≠ j2 → units[k].1.1 ≠ i.1)

theorem insertUnitInvariant_insertUnit {n : Nat} (assignments0 : Array Assignment)
    (assignments0_size : assignments0.size = n) (units : Array (Literal (PosFin n)))
    (assignments : Array Assignment) (assignments_size : assignments.size = n)
    (foundContradiction : Bool) (l : Literal (PosFin n)) :
    InsertUnitInvariant assignments0 assignments0_size units assignments assignments_size →
    let update_res := insertUnit (units, assignments, foundContradiction) l
    have update_res_size : update_res.snd.fst.size = n := by rw [size_insertUnit]; exact assignments_size
    InsertUnitInvariant assignments0 assignments0_size update_res.1 update_res.2.1 update_res_size := by
  intro h
  simp only [InsertUnitInvariant, Fin.getElem_fin, ne_eq, Bool.not_eq_true] at h
  simp only [InsertUnitInvariant, Fin.getElem_fin, ne_eq, Bool.not_eq_true]
  intro i
  specialize h i
  have i_in_bounds : i.1 < assignments.size := by omega
  have l_in_bounds : l.1.1 < assignments.size := by rw [assignments_size]; exact l.1.2.2
  rcases h with ⟨h1, h2⟩ | ⟨j, b, i_gt_zero, h1, h2, h3, h4⟩ | ⟨j1, j2, i_gt_zero, h1, h2, h3, h4, h5⟩
  · by_cases hasAssignment l.2 assignments[l.1.1]!
    · next h3 =>
      apply Or.inl
      simp only [insertUnit, h3, ite_true]
      constructor
      · exact h1
      · intro j
        have hsize : (insertUnit (units, assignments, foundContradiction) l).1.size = units.size := by
          simp [insertUnit, h3]
        let j' : Fin (Array.size units) := ⟨j.1, by rw [← hsize]; exact j.2⟩
        exact h2 j'
    · next h3 =>
      by_cases i.1 = l.1.1
      · next i_eq_l =>
        apply Or.inr ∘ Or.inl
        have units_size_lt_updatedUnits_size : units.size < (insertUnit (units, assignments, foundContradiction) l).1.size := by
          simp only [insertUnit]
          split
          · contradiction
          · simp only [Array.size_push, Nat.lt_succ_self]
        let mostRecentUnitIdx : Fin (insertUnit (units, assignments, foundContradiction) l).1.size :=
          ⟨units.size, units_size_lt_updatedUnits_size⟩
        have i_gt_zero : i.1 > 0 := by rw [i_eq_l]; exact l.1.2.1
        refine ⟨mostRecentUnitIdx, l.2, i_gt_zero, ?_⟩
        simp +zetaDelta only [insertUnit, h3, ite_false, Array.getElem_push_eq, i_eq_l, reduceCtorEq]
        constructor
        · rfl
        · constructor
          · rw [Array.getElem_modify_self]
            simp only [← i_eq_l, h1]
          · constructor
            · simp only [getElem!_def, l_in_bounds, Array.getElem?_eq_getElem,
                Bool.not_eq_true] at h3
              simp only [← i_eq_l, ← h1]
              simp only [i_eq_l, h3]
            · intro k hk
              have k_in_bounds : k.1 < units.size := by
                apply Nat.lt_of_le_of_ne
                · apply Nat.le_of_lt_succ
                  have k_property := k.2
                  simp only [insertUnit, h3, ite_false, Array.size_push, reduceCtorEq] at k_property
                  exact k_property
                · intro h
                  simp only [← h, not_true, mostRecentUnitIdx] at hk
              rw [Array.getElem_push_lt _ _ _ k_in_bounds]
              rw [i_eq_l] at h2
              exact h2 ⟨k.1, k_in_bounds⟩
      · next i_ne_l =>
        apply Or.inl
        simp only [insertUnit, h3, ite_false, reduceCtorEq]
        rw [Array.getElem_modify_of_ne (Ne.symm i_ne_l)]
        constructor
        · exact h1
        · intro j
          rw [Array.getElem_push]
          by_cases h : j.val < Array.size units
          · simp only [h, dite_true]
            exact h2 ⟨j.1, h⟩
          · simp only [h, dite_false]
            exact Ne.symm i_ne_l
  · by_cases hasAssignment l.2 assignments[l.1.1]!
    · next h5 =>
      apply Or.inr ∘ Or.inl
      have j_lt_updatedUnits_size : j.1 < (insertUnit (units, assignments, foundContradiction) l).1.size := by
        simp only [insertUnit, h5, ite_true]
        exact j.2
      refine ⟨⟨j.1, j_lt_updatedUnits_size⟩, b,i_gt_zero, ?_⟩
      simp only [insertUnit, h5, ite_true]
      refine ⟨h1,h2,h3,?_⟩
      intro k k_ne_j
      have k_size : k.1 < units.size := by
        have k_property := k.2
        simp only [insertUnit, h5, ite_true] at k_property
        exact k_property
      have k_ne_j : { val := k.val, isLt := k_size } ≠ j := by
        intro k_eq_j
        simp only [← Fin.val_eq_of_eq k_eq_j, not_true] at k_ne_j
      exact h4 ⟨k.1, k_size⟩ k_ne_j
    · next h5 =>
      by_cases i.1 = l.1.1
      · next i_eq_l =>
        apply Or.inr ∘ Or.inr
        have units_size_lt_updatedUnits_size : units.size < (insertUnit (units, assignments, foundContradiction) l).1.size := by
          simp only [insertUnit]
          split
          · contradiction
          · simp only [Array.size_push, Nat.lt_succ_self]
        let mostRecentUnitIdx : Fin (insertUnit (units, assignments, foundContradiction) l).1.size :=
          ⟨units.size, units_size_lt_updatedUnits_size⟩
        have j_lt_updatedUnits_size : j.1 < (insertUnit (units, assignments, foundContradiction) l).1.size := by
          simp [insertUnit, h5, ite_false, Array.size_push]
          exact Nat.lt_trans j.2 (Nat.lt_succ_self units.size)
        match hb : b, hl : l.2 with
        | true, true =>
          exfalso
          have assignments_i_rw : assignments[i.1]! = assignments[i.1] := by
            simp only [getElem!_def, i_in_bounds, Array.getElem?_eq_getElem]
          rw [hl, ← i_eq_l, assignments_i_rw, h2] at h5
          exact h5 (has_add _ true)
        | true, false =>
          refine ⟨⟨j.1, j_lt_updatedUnits_size⟩, mostRecentUnitIdx, i_gt_zero, ?_⟩
          simp only [insertUnit, h5, ite_false, Array.getElem_push_eq, ne_eq, reduceCtorEq]
          constructor
          · rw [Array.getElem_push_lt units l j.1 j.2, h1]
          · constructor
            · simp +zetaDelta [i_eq_l, ← hl]
              rfl
            · constructor
              · simp only [i_eq_l]
                rw [Array.getElem_modify_self]
                simp only [addAssignment, hl, ← i_eq_l, h2, ite_true, ite_false]
                apply addNeg_addPos_eq_both
              · constructor
                · match h : assignments0[i.val]'_ with
                  | unassigned => rfl
                  | pos => simp +decide [h] at h3
                  | neg =>
                    simp only [addAssignment, addPosAssignment, h, ite_true] at h2
                    simp only [i_eq_l] at h2
                    simp [hasAssignment, hl, getElem!_def, l_in_bounds, h2, hasNegAssignment] at h5
                  | both => simp +decide only [h] at h3
                · intro k k_ne_j k_ne_l
                  rw [Array.getElem_push]
                  by_cases h : k.1 < units.size
                  · simp only [h, dite_true]
                    have k_ne_j : ⟨k.1, h⟩ ≠ j := by
                      intro k_eq_j
                      simp only [← k_eq_j, not_true] at k_ne_j
                    exact h4 ⟨k.1, h⟩ k_ne_j
                  · exfalso
                    have k_property := k.2
                    simp only [insertUnit, h5, ite_false, Array.size_push, reduceCtorEq] at k_property
                    rcases Nat.lt_or_eq_of_le <| Nat.le_of_lt_succ k_property with k_lt_units_size | k_eq_units_size
                    · exact h k_lt_units_size
                    · simp only [← k_eq_units_size, not_true, mostRecentUnitIdx] at k_ne_l
                      exact k_ne_l rfl
        | false, true =>
          refine ⟨mostRecentUnitIdx, ⟨j.1, j_lt_updatedUnits_size⟩, i_gt_zero, ?_⟩
          simp [insertUnit, h5, ite_false, Array.getElem_push_eq, ne_eq]
          constructor
          · simp +zetaDelta [i_eq_l, ← hl]
            rfl
          · constructor
            · rw [Array.getElem_push_lt units l j.1 j.2, h1]
            · constructor
              · simp only [i_eq_l]
                rw [Array.getElem_modify_self]
                simp only [addAssignment, hl, ← i_eq_l, h2, ite_true, ite_false]
                apply addPos_addNeg_eq_both
              · constructor
                · match h : assignments0[i.val]'_ with
                  | unassigned => rfl
                  | pos =>
                    simp only [addAssignment, h, ite_false, addNegAssignment, reduceCtorEq] at h2
                    simp only [i_eq_l] at h2
                    simp [hasAssignment, hl, getElem!_def, l_in_bounds, h2, hasPosAssignment] at h5
                  | neg  => simp +decide only [h] at h3
                  | both => simp +decide only [h] at h3
                · intro k k_ne_l k_ne_j
                  rw [Array.getElem_push]
                  by_cases h : k.1 < units.size
                  · simp only [h, dite_true]
                    have k_ne_j : ⟨k.1, h⟩ ≠ j := by
                      intro k_eq_j
                      simp only [← k_eq_j, not_true] at k_ne_j
                    exact h4 ⟨k.1, h⟩ k_ne_j
                  · exfalso
                    have k_property := k.2
                    simp only [insertUnit, h5, ite_false, Array.size_push, reduceCtorEq] at k_property
                    rcases Nat.lt_or_eq_of_le <| Nat.le_of_lt_succ k_property with k_lt_units_size | k_eq_units_size
                    · exact h k_lt_units_size
                    · simp only [← k_eq_units_size, not_true, mostRecentUnitIdx] at k_ne_l
                      exact k_ne_l rfl
        | false, false =>
          exfalso
          have assignments_i_rw : assignments[i.1]! = assignments[i.1] := by
            simp [getElem!_def, i_in_bounds]
          rw [hl, ← i_eq_l, assignments_i_rw, h2] at h5
          exact h5 (has_add _ false)
      · next i_ne_l =>
        apply Or.inr ∘ Or.inl
        have j_lt_updatedUnits_size : j.1 < (insertUnit (units, assignments, foundContradiction) l).1.size := by
          simp only [insertUnit, h5, ite_false, Array.size_push, reduceCtorEq]
          exact Nat.lt_trans j.2 (Nat.lt_succ_self units.size)
        refine ⟨⟨j.1, j_lt_updatedUnits_size⟩, b,i_gt_zero, ?_⟩
        simp only [insertUnit, h5, ite_false, reduceCtorEq]
        constructor
        · rw [Array.getElem_push_lt units l j.1 j.2, h1]
        · constructor
          · rw [Array.getElem_modify_of_ne (Ne.symm i_ne_l), h2]
          · constructor
            · exact h3
            · intro k k_ne_j
              rw [Array.getElem_push]
              by_cases h : k.val < units.size
              · simp only [h, dite_true]
                have k_ne_j : ⟨k.1, h⟩ ≠ j := by
                  intro k_eq_j
                  simp only [← Fin.val_eq_of_eq k_eq_j, not_true] at k_ne_j
                exact h4 ⟨k.1, h⟩ k_ne_j
              · simp only [h, dite_false]
                exact Ne.symm i_ne_l
  · have j1_lt_updatedUnits_size : j1.1 < (insertUnit (units, assignments, foundContradiction) l).1.size := by
      simp only [insertUnit]
      split
      · exact j1.2
      · simp only [Array.size_push]
        exact Nat.lt_trans j1.2 (Nat.lt_succ_self units.size)
    have j2_lt_updatedUnits_size : j2.1 < (insertUnit (units, assignments, foundContradiction) l).1.size := by
      simp only [insertUnit]
      split
      · exact j2.2
      · simp only [Array.size_push]
        exact Nat.lt_trans j2.2 (Nat.lt_succ_self units.size)
    refine Or.inr <| Or.inr <| ⟨⟨j1.1, j1_lt_updatedUnits_size⟩, ⟨j2.1, j2_lt_updatedUnits_size⟩, i_gt_zero, ?_⟩
    simp only [insertUnit]
    constructor
    · split
      · exact h1
      · simp only [Array.getElem_push_lt units l j1.1 j1.2, h1]
    · constructor
      · split
        · exact h2
        · simp only [Array.getElem_push_lt units l j2.1 j2.2, h2]
      · constructor
        · split
          · exact h3
          · simp only
            by_cases i.1 = l.1.1
            · next i_eq_l =>
              simp only [i_eq_l]
              rw [Array.getElem_modify_self]
              simp only [← i_eq_l, h3, add_both_eq_both]
            · next i_ne_l => rw [Array.getElem_modify_of_ne (Ne.symm i_ne_l), h3]
        · constructor
          · exact h4
          · intro k k_ne_j1 k_ne_j2
            by_cases k.1 < units.size
            · next k_in_bounds =>
              have k_ne_j1 : ⟨k.1, k_in_bounds⟩ ≠ j1 := by
                intro k_eq_j1
                simp only [← k_eq_j1, not_true] at k_ne_j1
              have k_ne_j2 : ⟨k.1, k_in_bounds⟩ ≠ j2 := by
                intro k_eq_j2
                simp only [← k_eq_j2, not_true] at k_ne_j2
              split
              · exact h5 ⟨k.1, k_in_bounds⟩ k_ne_j1 k_ne_j2
              · simp only [ne_eq]
                rw [Array.getElem_push]
                simp only [k_in_bounds, dite_true]
                exact h5 ⟨k.1, k_in_bounds⟩ k_ne_j1 k_ne_j2
            · next k_not_lt_units_size =>
              split
              · next h =>
                exfalso
                have k_property := k.2
                simp only [insertUnit, h, ite_true] at k_property
                exact k_not_lt_units_size k_property
              · next h =>
                simp only
                have k_eq_units_size : k.1 = units.size := by
                  have k_property := k.2
                  simp only [insertUnit, h, ite_false, Array.size_push, reduceCtorEq] at k_property
                  rcases Nat.lt_or_eq_of_le <| Nat.le_of_lt_succ k_property with k_lt_units_size | k_eq_units_size
                  · exfalso; exact k_not_lt_units_size k_lt_units_size
                  · exact k_eq_units_size
                simp only [k_eq_units_size, Array.getElem_push_eq, ne_eq]
                intro l_eq_i
                simp [getElem!_def, l_eq_i, i_in_bounds, h3, has_both] at h

theorem insertUnitInvariant_insertUnit_fold {n : Nat} (assignments0 : Array Assignment)
    (assignments0_size : assignments0.size = n) (rupUnits : Array (Literal (PosFin n)))
    (assignments : Array Assignment) (assignments_size : assignments.size = n) (b : Bool)
    (units : CNF.Clause (PosFin n)) :
    InsertUnitInvariant assignments0 assignments0_size rupUnits assignments assignments_size →
    let update_res := List.foldl insertUnit (rupUnits, assignments, b) units
    have update_res_size : update_res.snd.fst.size = n := by
      rw [size_insertUnit_fold]
      exact assignments_size
    InsertUnitInvariant assignments0 assignments0_size update_res.1 update_res.2.1 update_res_size := by
  induction units generalizing rupUnits assignments assignments_size b
  · simp only [List.foldl, imp_self]
  · next hd tl ih =>
    simp only [List.foldl]
    intro h0
    let update_res := insertUnit (rupUnits, assignments, b) hd
    have update_res_size : update_res.2.1.size = n := by rw [size_insertUnit]; exact assignments_size
    have h := insertUnitInvariant_insertUnit assignments0 assignments0_size rupUnits assignments assignments_size b hd h0
    exact ih update_res.1 update_res.2.1 update_res_size update_res.2.2 h

theorem insertUnitInvariant_insertRupUnits {n : Nat} (f : DefaultFormula n) (f_readyForRupAdd : ReadyForRupAdd f)
    (units : CNF.Clause (PosFin n)) :
    let assignments := (insertRupUnits f units).fst.assignments
    have hsize : assignments.size = n := by
      rw [← f_readyForRupAdd.2.1]
      exact size_assignments_insertRupUnits f units
    let rupUnits := (insertRupUnits f units).1.rupUnits
    InsertUnitInvariant f.assignments f_readyForRupAdd.2.1 rupUnits assignments hsize := by
  simp only [insertRupUnits]
  have hsize : f.assignments.size = n := by rw [f_readyForRupAdd.2.1]
  have h0 : InsertUnitInvariant f.assignments hsize f.rupUnits f.assignments hsize := by
    intro i
    simp only [Fin.getElem_fin, ne_eq, true_and, Bool.not_eq_true, exists_and_right]
    apply Or.inl
    intro j
    simp only [f_readyForRupAdd.1, Array.size_toArray, List.length_nil] at j
    exact Fin.elim0 j
  exact insertUnitInvariant_insertUnit_fold f.assignments hsize f.rupUnits f.assignments hsize false units h0

theorem nodup_insertRupUnits {n : Nat} (f : DefaultFormula n) (f_readyForRupAdd : ReadyForRupAdd f)
    (units : CNF.Clause (PosFin n)) :
      ∀ i : Fin (f.insertRupUnits units).1.rupUnits.size, ∀ j : Fin (f.insertRupUnits units).1.rupUnits.size,
      i ≠ j → (f.insertRupUnits units).1.rupUnits[i] ≠ (f.insertRupUnits units).1.rupUnits[j] := by
  intro i j i_ne_j
  rcases hi : (insertRupUnits f units).fst.rupUnits[i] with ⟨li, bi⟩
  rcases hj : (insertRupUnits f units).fst.rupUnits[j] with ⟨lj, bj⟩
  intro heq
  simp only [Prod.mk.injEq] at heq
  rcases heq with ⟨li_eq_lj, bi_eq_bj⟩
  have h := insertUnitInvariant_insertRupUnits f f_readyForRupAdd units ⟨li.1, li.2.2⟩
  simp only [ne_eq, Bool.not_eq_true, exists_and_right] at h
  rcases h with ⟨_, h2⟩ | ⟨k, b, _, _, _, h4⟩ | ⟨k1, k2, li_gt_zero, h1, h2, h3, h4, h5⟩
  · specialize h2 j
    rw [hj, li_eq_lj] at h2
    simp only [not_true] at h2
  · by_cases i = k
    · next i_eq_k =>
      have j_ne_k : j ≠ k := by rw [← i_eq_k]; exact i_ne_j.symm
      specialize h4 j j_ne_k
      rw [hj, li_eq_lj] at h4
      simp +decide only at h4
    · next i_ne_k =>
      specialize h4 i i_ne_k
      rw [hi] at h4
      simp only [not_true] at h4
  · by_cases bi
    · next bi_eq_true =>
      by_cases i = k1
      · next i_eq_k1 =>
        have j_ne_k1 : j ≠ k1 := by rw [← i_eq_k1]; exact i_ne_j.symm
        by_cases j = k2
        · next j_eq_k2 =>
          rw [← j_eq_k2, hj, ← bi_eq_bj, bi_eq_true] at h2
          simp at h2
        · next j_ne_k2 =>
          specialize h5 j j_ne_k1 j_ne_k2
          rw [hj, li_eq_lj] at h5
          simp +decide only at h5
      · next i_ne_k1 =>
        by_cases i = k2
        · next i_eq_k2 =>
          rw [← i_eq_k2, hi, bi_eq_true] at h2
          simp at h2
        · next i_ne_k2 =>
          specialize h5 i i_ne_k1 i_ne_k2
          rw [hi] at h5
          simp only [not_true] at h5
    · next bi_eq_false =>
      simp only [Bool.not_eq_true] at bi_eq_false
      by_cases i = k2
      · next i_eq_k2 =>
        have j_ne_k2 : j ≠ k2 := by rw [← i_eq_k2]; exact i_ne_j.symm
        by_cases j = k1
        · next j_eq_k1 =>
          rw [← j_eq_k1, hj, ← bi_eq_bj, bi_eq_false] at h1
          simp at h1
        · next j_ne_k1 =>
          specialize h5 j j_ne_k1 j_ne_k2
          rw [hj, li_eq_lj] at h5
          simp +decide only at h5
      · next i_ne_k2 =>
        by_cases i = k1
        · next i_eq_k1 =>
          rw [← i_eq_k1, hi, bi_eq_false] at h1
          simp at h1
        · next i_ne_k1 =>
          specialize h5 i i_ne_k1 i_ne_k2
          rw [hi] at h5
          simp only [not_true] at h5

theorem size_clearUnit (assignments : Array Assignment) (l : Literal (PosFin n)) :
    (clearUnit assignments l).size = assignments.size := by
  simp [clearUnit]

theorem size_clearUnit_foldl {α : Type u} (assignments : Array Assignment)
    (f : Array Assignment → α → Array Assignment) (f_preserves_size :
    ∀ arr : Array Assignment, ∀ a : α, (f arr a).size = arr.size) (l : List α) :
  Array.size (List.foldl f assignments l) = Array.size assignments := by
  have hb : assignments.size = assignments.size := rfl
  have hl (assignments' : Array Assignment) (hsize : assignments'.size = assignments.size) (a : α) (_ : a ∈ l) :
    (f assignments' a).size = assignments.size := by rw [f_preserves_size assignments' a, hsize]
  exact List.foldlRecOn l f assignments hb hl

def ClearInsertInductionMotive {n : Nat} (f : DefaultFormula n) (assignments_size : f.assignments.size = n)
    (units : Array (Literal (PosFin n))) :
    Nat → Array Assignment → Prop :=
  fun idx assignments => ∃ hsize : assignments.size = n, ∀ i : Fin n,
    have i_lt_assignments_size : i.1 < assignments.size := hsize ▸ i.2
    have i_lt_f_assignments_size : i.1 < f.assignments.size := by
      rw [assignments_size]
      exact i.2
    let assignments_i := assignments[i.1]'i_lt_assignments_size
    let fassignments_i := f.assignments[i.1]'i_lt_f_assignments_size
    -- Case 1: i doesn't appear in units, so assignments_i and fassignments_i are equal
    (assignments_i = fassignments_i ∧ ∀ j : Fin units.size, j ≥ idx → units[j].1.1 ≠ i.1) ∨
    -- Case 2: (i, b) appears but (i, ¬b) doesn't so assignments_i = addAssignment b fassignments_i
    (∃ j : Fin units.size, ∃ b : Bool, ∃ i_gt_zero : i.1 > 0,
      j ≥ idx ∧ units[j] = ⟨⟨i.1, ⟨i_gt_zero, i.2⟩⟩, b⟩ ∧ assignments_i = addAssignment b fassignments_i ∧
      ¬(hasAssignment b fassignments_i) ∧ ∀ k : Fin units.size, k ≥ idx → k ≠ j → units[k].1.1 ≠ i.1) ∨
    -- Case 3: (i, true) and (i, false) both appear so assignments_i = both and fassignments_i = unassigned
    (∃ j1 : Fin units.size, ∃ j2 : Fin units.size, ∃ i_gt_zero : i.1 > 0,
      j1 ≥ idx ∧ j2 ≥ idx ∧ units[j1] = ⟨⟨i.1, ⟨i_gt_zero, i.2⟩⟩, true⟩ ∧ units[j2] = ⟨⟨i.1, ⟨i_gt_zero, i.2⟩⟩, false⟩ ∧
      assignments_i = both ∧ fassignments_i = unassigned ∧ ∀ k : Fin units.size, k ≥ idx → k ≠ j1 → k ≠ j2 → units[k].1.1 ≠ i.1)

theorem clear_insertRup_base_case {n : Nat} (f : DefaultFormula n) (f_readyForRupAdd : ReadyForRupAdd f)
  (units : CNF.Clause (PosFin n)) :
  ClearInsertInductionMotive f f_readyForRupAdd.2.1 (insertRupUnits f units).1.rupUnits 0 (insertRupUnits f units).1.assignments := by
  have insertRupUnits_assignments_size := size_assignments_insertRupUnits f units
  rw [f_readyForRupAdd.2.1] at insertRupUnits_assignments_size
  apply Exists.intro insertRupUnits_assignments_size
  intro i
  simp only [Nat.zero_le, Fin.getElem_fin, ne_eq, forall_const, true_and]
  exact insertUnitInvariant_insertRupUnits f f_readyForRupAdd units i

theorem clear_insert_inductive_case {n : Nat} (f : DefaultFormula n) (f_assignments_size : f.assignments.size = n)
    (units : Array (Literal (PosFin n))) (units_nodup : ∀ i : Fin units.size, ∀ j : Fin units.size, i ≠ j → units[i] ≠ units[j])
    (idx : Fin units.size) (assignments : Array Assignment)
    (ih : ClearInsertInductionMotive f f_assignments_size units idx.1 assignments) :
    ClearInsertInductionMotive f f_assignments_size units (idx.1 + 1) (clearUnit assignments units[idx]) := by
  rcases ih with ⟨hsize, ih⟩
  have hsize' : Array.size (clearUnit assignments units[idx]) = n := by
    rw [← size_clearUnit assignments units[idx]] at hsize
    exact hsize
  apply Exists.intro hsize'
  intro i
  specialize ih i
  simp only [Fin.getElem_fin, ne_eq, exists_and_left, exists_and_right] at ih
  rcases ih with
    ⟨ih1, ih2⟩ | ⟨j, j_ge_idx, ⟨b, ⟨i_gt_zero, ih1⟩, ih2, ih3, ih4⟩⟩ |
    ⟨j1, j1_ge_idx, j2, j2_ge_idx, i_gt_zero, ih1, ih2, ih3, ih4, ih5⟩
  · apply Or.inl
    constructor
    · simp only [clearUnit, Fin.getElem_fin, Array.get_eq_getElem]
      specialize ih2 idx (Nat.le_refl idx.val)
      have i_in_bounds : i.1 < assignments.size := by
        rw [hsize]
        exact i.2
      have h := Array.getElem_modify_of_ne ih2 (removeAssignment units[idx.val].2) (by simpa using i_in_bounds)
      simp only [Fin.getElem_fin] at h
      rw [h]
      exact ih1
    · intro j j_ge_idx_add_one
      exact ih2 j (Nat.le_of_succ_le j_ge_idx_add_one)
  · by_cases idx = j
    · next idx_eq_j =>
      apply Or.inl
      constructor
      · simp only [clearUnit, idx_eq_j, Array.get_eq_getElem, ih1]
        rw [Array.getElem_modify_self, ih2, remove_add_cancel]
        exact ih3
      · intro k k_ge_idx_add_one
        have k_ge_idx : k.val ≥ idx.val := Nat.le_of_succ_le k_ge_idx_add_one
        have k_ne_j : k ≠ j := by
          intro k_eq_j
          rw [k_eq_j, idx_eq_j] at k_ge_idx_add_one
          exact Nat.not_succ_le_self j.val k_ge_idx_add_one
        exact ih4 k k_ge_idx k_ne_j
    · next idx_ne_j =>
      refine Or.inr <| Or.inl <| ⟨j,b,i_gt_zero,?_⟩
      constructor
      · rw [← Nat.succ_eq_add_one]
        apply Nat.succ_le_of_lt ∘ Nat.lt_of_le_of_ne j_ge_idx
        intro idx_eq_j
        exact idx_ne_j (Fin.eq_of_val_eq idx_eq_j)
      · constructor
        · exact ih1
        · constructor
          · simp only [clearUnit, Array.get_eq_getElem]
            specialize ih4 idx (Nat.le_refl idx.1) idx_ne_j
            rw [Array.getElem_modify_of_ne ih4]
            exact ih2
          · constructor
            · exact ih3
            · intro k k_ge_idx_add_one k_ne_j
              exact ih4 k (Nat.le_of_succ_le k_ge_idx_add_one) k_ne_j
  · by_cases idx = j1
    · next idx_eq_j1 =>
      have idx_ne_j2 : idx ≠ j2 := by
        rw [idx_eq_j1]
        intro j1_eq_j2
        simp [j1_eq_j2, ih2] at ih1
      refine Or.inr <| Or.inl <| ⟨j2, false, i_gt_zero, ?_⟩
      constructor
      · apply Nat.le_of_lt_succ
        rw [← Nat.succ_eq_add_one]
        apply Nat.succ_lt_succ ∘ Nat.lt_of_le_of_ne j2_ge_idx
        intro idx_eq_j2
        exact idx_ne_j2 (Fin.eq_of_val_eq idx_eq_j2)
      · constructor
        · simp only [Fin.getElem_fin]
          exact ih2
        · constructor
          · simp only [clearUnit, idx_eq_j1, Array.get_eq_getElem, ih1]
            rw [Array.getElem_modify_self, ih3, ih4]
            decide
          · constructor
            · simp [hasAssignment, hasNegAssignment, ih4]
            · intro k k_ge_idx_add_one k_ne_j2
              intro h1
              by_cases units[k.1].2
              · next h2 =>
                have k_ne_j1 : k ≠ j1 := by
                  rw [← idx_eq_j1]
                  intro k_eq_idx
                  rw [k_eq_idx] at k_ge_idx_add_one
                  exact Nat.lt_irrefl idx.1 <| Nat.lt_of_succ_le k_ge_idx_add_one
                have h3 := units_nodup k j1 k_ne_j1
                simp only [Fin.getElem_fin, ih1, ← h1, ← h2, ne_eq] at h3
                exact h3 rfl
              · next h2 =>
                have h3 := units_nodup k j2 k_ne_j2
                simp only [Bool.not_eq_true] at h2
                simp only [Fin.getElem_fin, ih2, ← h1, ← h2, ne_eq] at h3
                exact h3 rfl
    · next idx_ne_j1 =>
      by_cases idx = j2
      · next idx_eq_j2 =>
        refine Or.inr <| Or.inl <| ⟨j1, true, i_gt_zero, ?_⟩
        constructor
        · apply Nat.le_of_lt_succ
          rw [← Nat.succ_eq_add_one]
          apply Nat.succ_lt_succ ∘ Nat.lt_of_le_of_ne j1_ge_idx
          intro idx_eq_j1
          exact idx_ne_j1 (Fin.eq_of_val_eq idx_eq_j1)
        · constructor
          · simp only [Fin.getElem_fin]
            exact ih1
          · constructor
            · simp only [clearUnit, idx_eq_j2, Array.get_eq_getElem, ih2]
              rw [Array.getElem_modify_self, ih3, ih4]
              decide
            · constructor
              · simp only [hasAssignment, hasNegAssignment, ih4, ite_false, not_false_eq_true]
                decide
              · intro k k_ge_idx_add_one k_ne_j1
                intro h1
                by_cases units[k.1].2
                · next h2 =>
                  have h3 := units_nodup k j1 k_ne_j1
                  simp only [Fin.getElem_fin, ih1, ← h1, ← h2, ne_eq] at h3
                  exact h3 rfl
                · next h2 =>
                  have k_ne_j2 : k ≠ j2 := by
                    rw [← idx_eq_j2]
                    intro k_eq_idx
                    rw [k_eq_idx] at k_ge_idx_add_one
                    exact Nat.lt_irrefl idx.1 <| Nat.lt_of_succ_le k_ge_idx_add_one
                  have h3 := units_nodup k j2 k_ne_j2
                  simp only [Bool.not_eq_true] at h2
                  simp only [Fin.getElem_fin, ih2, ← h1, ← h2, ne_eq] at h3
                  exact h3 rfl
      · next idx_ne_j2 =>
        refine Or.inr <| Or.inr <| ⟨j1, j2,i_gt_zero, ?_⟩
        constructor
        · apply Nat.le_of_lt_succ
          rw [← Nat.succ_eq_add_one]
          apply Nat.succ_lt_succ ∘ Nat.lt_of_le_of_ne j1_ge_idx
          intro idx_eq_j1
          exact idx_ne_j1 (Fin.eq_of_val_eq idx_eq_j1)
        · constructor
          · apply Nat.le_of_lt_succ
            rw [← Nat.succ_eq_add_one]
            apply Nat.succ_lt_succ ∘ Nat.lt_of_le_of_ne j2_ge_idx
            intro idx_eq_j2
            exact idx_ne_j2 (Fin.eq_of_val_eq idx_eq_j2)
          · constructor
            · simp only [Fin.getElem_fin]
              exact ih1
            · constructor
              · simp only [Fin.getElem_fin]
                exact ih2
              · constructor
                · simp only [clearUnit, Array.get_eq_getElem]
                  have idx_res_ne_i : units[idx.1].1.1 ≠ i.1 := by
                    intro h1
                    by_cases units[idx.1].2
                    · next h2 =>
                      have h3 := units_nodup idx j1 idx_ne_j1
                      simp only [Fin.getElem_fin, ih1, ← h1, ← h2, ne_eq] at h3
                      exact h3 rfl
                    · next h2 =>
                      have h3 := units_nodup idx j2 idx_ne_j2
                      simp only [Bool.not_eq_true] at h2
                      simp only [Fin.getElem_fin, ih2, ← h1, ← h2, ne_eq] at h3
                      exact h3 rfl
                  rw [Array.getElem_modify_of_ne idx_res_ne_i]
                  exact ih3
                · constructor
                  · exact ih4
                  · intro k k_ge_idx_add_one
                    exact ih5 k <| Nat.le_of_succ_le k_ge_idx_add_one

theorem clear_insertRup {n : Nat} (f : DefaultFormula n) (f_readyForRupAdd : ReadyForRupAdd f)
    (units : CNF.Clause (PosFin n)) :
    clearRupUnits (f.insertRupUnits units).1 = f := by
  simp only [clearRupUnits]
  ext : 1
  · simp only [insertRupUnits]
  · rw [f_readyForRupAdd.1]
  · simp only [insertRupUnits]
  · simp only
    let motive := ClearInsertInductionMotive f f_readyForRupAdd.2.1 (insertRupUnits f units).1.rupUnits
    have h_base : motive 0 (insertRupUnits f units).1.assignments := clear_insertRup_base_case f f_readyForRupAdd units
    have h_inductive (idx : Fin (insertRupUnits f units).1.rupUnits.size) (assignments : Array Assignment)
      (ih : motive idx.val assignments) : motive (idx.val + 1) (clearUnit assignments (insertRupUnits f units).1.rupUnits[idx]) :=
      clear_insert_inductive_case f f_readyForRupAdd.2.1 (insertRupUnits f units).1.rupUnits
        (nodup_insertRupUnits f f_readyForRupAdd units) idx assignments ih
    rcases Array.foldl_induction motive h_base h_inductive with ⟨h_size, h⟩
    apply Array.ext
    · rw [h_size, f_readyForRupAdd.2.1]
    · intro i hi1 hi2
      have i_lt_n : i < n := by rw [← f_readyForRupAdd.2.1]; exact hi2
      specialize h ⟨i, i_lt_n⟩
      rcases h with ⟨h,_⟩
      · exact h
      · omega

theorem clauses_performRupCheck {n : Nat} (f : DefaultFormula n) (rupHints : Array Nat) :
    (performRupCheck f rupHints).1.clauses = f.clauses := by
  simp only [performRupCheck]

theorem rupUnits_performRupCheck {n : Nat} (f : DefaultFormula n) (rupHints : Array Nat) :
    (performRupCheck f rupHints).1.rupUnits = f.rupUnits := by
  simp only [performRupCheck]

theorem ratUnits_performRupCheck {n : Nat} (f : DefaultFormula n) (rupHints : Array Nat) :
    (performRupCheck f rupHints).1.ratUnits = f.ratUnits := by
  simp only [performRupCheck]

theorem size_assignemnts_confirmRupHint {n : Nat} (clauses : Array (Option (DefaultClause n)))
    (assignments : Array Assignment) (derivedLits : CNF.Clause (PosFin n)) (b1 b2 : Bool) (id : Nat) :
    (confirmRupHint clauses (assignments, derivedLits, b1, b2) id).1.size = assignments.size := by
  simp only [confirmRupHint]
  repeat first
    | rfl
    | simp only [Array.size_modify]
    | split

theorem size_assignments_performRupCheck {n : Nat} (f : DefaultFormula n) (rupHints : Array Nat) :
    (performRupCheck f rupHints).1.assignments.size = f.assignments.size := by
  simp only [performRupCheck]
  rw [← Array.foldl_toList]
  have hb : (f.assignments, ([] : CNF.Clause (PosFin n)), false, false).1.size = f.assignments.size := rfl
  have hl (acc : Array Assignment × CNF.Clause (PosFin n) × Bool × Bool) (hsize : acc.1.size = f.assignments.size)
    (id : Nat) (_ : id ∈ rupHints.toList) : (confirmRupHint f.clauses acc id).1.size = f.assignments.size := by
    have h := size_assignemnts_confirmRupHint f.clauses acc.1 acc.2.1 acc.2.2.1 acc.2.2.2 id
    rw [h, hsize]
  exact List.foldlRecOn rupHints.toList (confirmRupHint f.clauses) (f.assignments, [], false, false) hb hl

def DerivedLitsInvariant {n : Nat} (f : DefaultFormula n)
    (fassignments_size : f.assignments.size = n) (assignments : Array Assignment)
    (assignments_size : assignments.size = n) (derivedLits : CNF.Clause (PosFin n)) :
    Prop :=
  ∀ i : Fin n,
    have i_lt_assignments_size : i.1 < assignments.size := assignments_size ▸ i.2
    have i_lt_f_assignments_size : i.1 < f.assignments.size := by
      rw [fassignments_size]
      exact i.2
    let assignments_i := assignments[i.1]'i_lt_assignments_size
    let fassignments_i := f.assignments[i.1]'i_lt_f_assignments_size
    -- Case 1: i doesn't appear in derivedLits, so assignments_i and f_assignments_i are equal
    (assignments_i = fassignments_i ∧ ∀ l ∈ derivedLits, l.1.1 ≠ i.1) ∨
    -- Case 2: (i, b) appears but (i, ¬b) doesn't so assignments_i = addAssignment
    (∃ j : Fin derivedLits.length,
      (derivedLits.get j).1.1 = i.1 ∧ assignments_i = addAssignment (derivedLits.get j).2 fassignments_i ∧
      ¬(hasAssignment (derivedLits.get j).2 fassignments_i) ∧ ∀ k : Fin derivedLits.length, k ≠ j → (derivedLits.get k).1.1 ≠ i.1) ∨
    -- Case 3: (i, true) and (i, false) both appear so assignments_i = both and fassignments_i = unassigned
    (∃ j1 : Fin derivedLits.length, ∃ j2 : Fin derivedLits.length,
      (derivedLits.get j1).1.1 = i.1 ∧ (derivedLits.get j2).1.1 = i.1 ∧ (derivedLits.get j1).2 = true ∧ (derivedLits.get j2).2 = false ∧
      assignments_i = both ∧ fassignments_i = unassigned ∧ ∀ k : Fin derivedLits.length, k ≠ j1 → k ≠ j2 → (derivedLits.get k).1.1 ≠ i.1)

theorem confirmRupHint_preserves_invariant_helper {n : Nat} (f : DefaultFormula n)
    (f_assignments_size : f.assignments.size = n)
    (acc : Array Assignment × CNF.Clause (PosFin n) × Bool × Bool) (hsize : acc.1.size = n)
    (l : Literal (PosFin n)) (ih : DerivedLitsInvariant f f_assignments_size acc.1 hsize acc.2.1)
    (h : ¬hasAssignment l.snd acc.fst[l.fst.val]! = true) :
    have hsize' : (Array.modify acc.1 l.1.1 (addAssignment l.snd)).size = n := by rw [Array.size_modify]; exact hsize
    DerivedLitsInvariant f f_assignments_size (Array.modify acc.fst l.1.1 (addAssignment l.snd)) hsize' (l :: acc.2.fst) := by
  intro _ i
  have i_in_bounds : i.1 < acc.1.size := by rw [hsize]; exact i.2
  have l_in_bounds : l.1.1 < acc.1.size := by rw [hsize]; exact l.1.2.2
  rcases ih i with ⟨h1, h2⟩ | ⟨j, j_eq_i, h1, h2, h3⟩ | ⟨j1, j2, j1_eq_i, j2_eq_i, j1_eq_true, j2_eq_false, h1, h2, h3⟩
  · by_cases l.1.1 = i.1
    · next l_eq_i =>
      have zero_lt_length_list : 0 < (l :: acc.snd.fst).length := by
        simp only [List.length_cons]
        exact Nat.zero_lt_succ (List.length acc.snd.fst)
      apply Or.inr ∘ Or.inl ∘ Exists.intro ⟨0, zero_lt_length_list⟩
      constructor
      · simp only [List.get, l_eq_i]
      · constructor
        · simp only [l_eq_i, Array.getElem_modify_self, List.get, h1]
        · constructor
          · simp only [List.get, Bool.not_eq_true]
            simp only [getElem!_def, l_in_bounds, Array.getElem?_eq_getElem, Bool.not_eq_true] at h
            simp only [l_eq_i, h1] at h
            exact h
          · intro k k_ne_zero
            have k_eq_succ : ∃ k' : Nat, ∃ k'_succ_in_bounds : k' + 1 < (l :: acc.2.1).length, k = ⟨k' + 1, k'_succ_in_bounds⟩ := by
              have k_val_ne_zero : k.1 ≠ 0 := by
                intro k_eq_zero
                simp only [List.length_cons, Nat.succ_eq_add_one, Fin.zero_eta, ne_eq] at k_ne_zero
                apply k_ne_zero
                apply Fin.eq_of_val_eq
                simp [k_eq_zero]
              rcases Nat.exists_eq_succ_of_ne_zero k_val_ne_zero with ⟨k', k_eq_k'_succ⟩
              rw [Nat.succ_eq_add_one] at k_eq_k'_succ
              have k'_succ_in_bounds : k' + 1 < (l :: acc.2.1).length := by rw [← k_eq_k'_succ]; exact k.2
              apply Exists.intro k' ∘ Exists.intro k'_succ_in_bounds
              apply Fin.eq_of_val_eq
              exact k_eq_k'_succ
            rcases k_eq_succ with ⟨k', k'_succ_in_bounds, k_eq_succ⟩
            rw [k_eq_succ, List.get_cons_succ]
            have k'_in_bounds : k' < acc.2.1.length := by
              simp only [List.length_cons, Nat.succ_eq_add_one] at k'_succ_in_bounds
              exact Nat.lt_of_succ_lt_succ k'_succ_in_bounds
            exact h2 (acc.2.1.get ⟨k', k'_in_bounds⟩) <| List.get_mem acc.snd.fst ⟨k', k'_in_bounds⟩
    · next l_ne_i =>
      apply Or.inl
      constructor
      · rw [Array.getElem_modify_of_ne l_ne_i]
        exact h1
      · intro l' l'_in_list
        simp only [List.find?, List.mem_cons] at l'_in_list
        rcases l'_in_list with l'_eq_l | l'_in_acc
        · rw [l'_eq_l]
          exact l_ne_i
        · exact h2 l' l'_in_acc
  · let l' := acc.2.1.get j
    have zero_in_bounds : 0 < (l :: acc.2.1).length := by
      simp only [List.length_cons]
      exact Nat.zero_lt_succ (List.length acc.snd.fst)
    have j_succ_in_bounds : j.1 + 1 < (l :: acc.2.1).length := by
      simp only [List.length_cons, Nat.succ_eq_add_one]
      exact Nat.succ_lt_succ j.2
    by_cases l.1.1 = i.1
    · next l_eq_i =>
      apply Or.inr ∘ Or.inr
      have l_ne_l' : l.2 ≠ l'.2 := by
        intro l_eq_l'
        rw [l_eq_i] at h
        simp only [l'] at l_eq_l'
        simp [getElem!_def, i_in_bounds, h1, l_eq_l', has_add] at h
      by_cases l.2
      · next l_eq_true =>
        rw [l_eq_true] at l_ne_l'
        have l'_eq_false : l'.2 = false := by rw [← Bool.not_eq_true]; exact Ne.symm l_ne_l'
        apply Exists.intro ⟨0, zero_in_bounds⟩
        apply Exists.intro ⟨j.1 + 1, j_succ_in_bounds⟩
        constructor
        · simp only [List.get]
          exact l_eq_i
        · constructor
          · simp only [List.get, Nat.add_eq, Nat.add_zero]
            exact j_eq_i
          · simp only [List.get, Nat.add_eq, Nat.add_zero, List.length_cons, ne_eq]
            apply And.intro l_eq_true ∘ And.intro l'_eq_false
            constructor
            · simp only [l'] at l'_eq_false
              simp only [l_eq_i, addAssignment, l_eq_true, ite_true, Array.getElem_modify_self, h1,
                l'_eq_false, ite_false]
              apply addPos_addNeg_eq_both
            · constructor
              · simp only [l'] at l'_eq_false
                simp only [l'_eq_false, hasAssignment, ite_false] at h2
                simp only [hasAssignment, l_eq_true, ↓reduceIte, l_eq_i, getElem!_def, i_in_bounds,
                  Array.getElem?_eq_getElem, h1, addAssignment, l'_eq_false, reduceCtorEq,
                  hasPos_addNeg, l'] at h
                exact unassigned_of_has_neither _ h h2
              · intro k k_ne_zero k_ne_j_succ
                have k_eq_succ : ∃ k' : Nat, ∃ k'_succ_in_bounds : k' + 1 < (l :: acc.2.1).length, k = ⟨k' + 1, k'_succ_in_bounds⟩ := by
                  have k_val_ne_zero : k.1 ≠ 0 := by
                    intro k_eq_zero
                    simp only [List.length_cons, ← k_eq_zero, ne_eq, not_true] at k_ne_zero
                  rcases Nat.exists_eq_succ_of_ne_zero k_val_ne_zero with ⟨k', k_eq_k'_succ⟩
                  rw [Nat.succ_eq_add_one k'] at k_eq_k'_succ
                  have k'_succ_in_bounds : k' + 1 < (l :: acc.2.1).length := by rw [← k_eq_k'_succ]; exact k.2
                  apply Exists.intro k' ∘ Exists.intro k'_succ_in_bounds
                  apply Fin.eq_of_val_eq
                  exact k_eq_k'_succ
                rcases k_eq_succ with ⟨k', k'_succ_in_bounds, k_eq_succ⟩
                rw [k_eq_succ]
                simp only [List.get, Nat.add_eq, Nat.add_zero, ne_eq]
                have k'_in_bounds : k' < acc.2.1.length := by
                  simp only [List.length_cons, Nat.succ_eq_add_one] at k'_succ_in_bounds
                  exact Nat.lt_of_succ_lt_succ k'_succ_in_bounds
                have k'_ne_j : ⟨k', k'_in_bounds⟩ ≠ j := by
                  simp only [k_eq_succ, List.length_cons, Fin.mk.injEq, Nat.succ.injEq] at k_ne_j_succ
                  exact Fin.ne_of_val_ne k_ne_j_succ
                exact h3 ⟨k', k'_in_bounds⟩ k'_ne_j
      · next l_eq_false =>
        simp only [Bool.not_eq_true] at l_eq_false
        rw [l_eq_false] at l_ne_l'
        have l'_eq_true : l'.2 = true := by
          have l'_ne_false : l'.2 ≠ false := Ne.symm l_ne_l'
          simp only [ne_eq, Bool.not_eq_false] at l'_ne_false
          exact l'_ne_false
        refine ⟨⟨j.1 + 1, j_succ_in_bounds⟩, ⟨0, zero_in_bounds⟩, ?_⟩
        constructor
        · simp only [List.get, Nat.add_eq, Nat.add_zero]
          exact j_eq_i
        · constructor
          · simp only [List.get]
            exact l_eq_i
          · simp only [List.get, Nat.add_eq, Nat.add_zero, List.length_cons, ne_eq]
            apply And.intro l'_eq_true ∘ And.intro l_eq_false
            constructor
            · simp only [l'] at l'_eq_true
              simp only [l_eq_i, addAssignment, l'_eq_true, ite_true, Array.getElem_modify_self, h1,
                l_eq_false, ite_false]
              apply addNeg_addPos_eq_both
            · constructor
              · simp only [l'] at l'_eq_true
                simp only [hasAssignment, l'_eq_true, ite_true] at h2
                simp only [hasAssignment, l_eq_false, reduceCtorEq, ↓reduceIte, l_eq_i,
                  getElem!_def, i_in_bounds, Array.getElem?_eq_getElem, h1, addAssignment,
                  l'_eq_true, hasNeg_addPos, l'] at h
                exact unassigned_of_has_neither _ h2 h
              · intro k k_ne_j_succ k_ne_zero
                have k_eq_succ : ∃ k' : Nat, ∃ k'_succ_in_bounds : k' + 1 < (l :: acc.2.1).length, k = ⟨k' + 1, k'_succ_in_bounds⟩ := by
                  have k_val_ne_zero : k.1 ≠ 0 := by
                    intro k_eq_zero
                    simp only [List.length_cons, ← k_eq_zero, ne_eq, not_true] at k_ne_zero
                  rcases Nat.exists_eq_succ_of_ne_zero k_val_ne_zero with ⟨k', k_eq_k'_succ⟩
                  rw [Nat.succ_eq_add_one k'] at k_eq_k'_succ
                  have k'_succ_in_bounds : k' + 1 < (l :: acc.2.1).length := by rw [← k_eq_k'_succ]; exact k.2
                  apply Exists.intro k' ∘ Exists.intro k'_succ_in_bounds
                  apply Fin.eq_of_val_eq
                  exact k_eq_k'_succ
                rcases k_eq_succ with ⟨k', k'_succ_in_bounds, k_eq_succ⟩
                rw [k_eq_succ]
                simp only [List.get, Nat.add_eq, Nat.add_zero, ne_eq]
                have k'_in_bounds : k' < acc.2.1.length := by
                  simp only [List.length_cons, Nat.succ_eq_add_one] at k'_succ_in_bounds
                  exact Nat.lt_of_succ_lt_succ k'_succ_in_bounds
                have k'_ne_j : ⟨k', k'_in_bounds⟩ ≠ j := by
                  simp only [k_eq_succ, List.length_cons, Fin.mk.injEq, Nat.succ.injEq] at k_ne_j_succ
                  exact Fin.ne_of_val_ne k_ne_j_succ
                exact h3 ⟨k', k'_in_bounds⟩ k'_ne_j
    · next l_ne_i =>
      apply Or.inr ∘ Or.inl ∘ Exists.intro ⟨j.1 + 1, j_succ_in_bounds⟩
      simp only [List.get, Nat.add_eq, Nat.add_zero]
      constructor
      · exact j_eq_i
      · constructor
        · rw [Array.getElem_modify_of_ne l_ne_i]
          exact h1
        · apply And.intro h2
          intro k k_ne_j_succ
          by_cases k.1 = 0
          · next k_eq_zero =>
            have k_eq_zero : k = ⟨0, zero_in_bounds⟩ := by
              apply Fin.eq_of_val_eq
              simp only [List.length_cons]
              exact k_eq_zero
            simp only [k_eq_zero, List.length_cons, List.get, ne_eq]
            exact l_ne_i
          · next k_ne_zero =>
            have k_eq_succ : ∃ k' : Nat, ∃ k'_succ_in_bounds : k' + 1 < (l :: acc.2.1).length, k = ⟨k' + 1, k'_succ_in_bounds⟩ := by
              have k_val_ne_zero : k.1 ≠ 0 := by
                intro k_eq_zero
                simp only [List.length_cons, ← k_eq_zero, ne_eq, not_true] at k_ne_zero
              rcases Nat.exists_eq_succ_of_ne_zero k_val_ne_zero with ⟨k', k_eq_k'_succ⟩
              rw [Nat.succ_eq_add_one] at k_eq_k'_succ
              have k'_succ_in_bounds : k' + 1 < (l :: acc.2.1).length := by rw [← k_eq_k'_succ]; exact k.2
              apply Exists.intro k' ∘ Exists.intro k'_succ_in_bounds
              apply Fin.eq_of_val_eq
              exact k_eq_k'_succ
            rcases k_eq_succ with ⟨k', k'_succ_in_bounds, k_eq_succ⟩
            rw [k_eq_succ]
            simp only [List.get, Nat.add_eq, Nat.add_zero, ne_eq]
            have k'_in_bounds : k' < acc.2.1.length := by
              simp only [List.length_cons, Nat.succ_eq_add_one] at k'_succ_in_bounds
              exact Nat.lt_of_succ_lt_succ k'_succ_in_bounds
            have k'_ne_j : ⟨k', k'_in_bounds⟩ ≠ j := by
              simp only [List.length_cons] at k_eq_succ
              simp only [List.length_cons, k_eq_succ, ne_eq, Fin.mk.injEq, Nat.succ.injEq] at k_ne_j_succ
              exact Fin.ne_of_val_ne k_ne_j_succ
            exact h3 ⟨k', k'_in_bounds⟩ k'_ne_j
  · have j1_succ_in_bounds : j1.1 + 1 < (l :: acc.2.1).length := by
      simp only [List.length_cons, Nat.succ_eq_add_one]
      exact Nat.succ_lt_succ j1.2
    have j2_succ_in_bounds : j2.1 + 1 < (l :: acc.2.1).length := by
      simp only [List.length_cons, Nat.succ_eq_add_one]
      exact Nat.succ_lt_succ j2.2
    let j1_succ : Fin (l :: acc.2.1).length := ⟨j1.1 + 1, j1_succ_in_bounds⟩
    let j2_succ : Fin (l :: acc.2.1).length := ⟨j2.1 + 1, j2_succ_in_bounds⟩
    apply Or.inr ∘ Or.inr ∘ Exists.intro j1_succ ∘ Exists.intro j2_succ
    simp only [List.get, Nat.add_eq, Nat.add_zero, List.length_cons, ne_eq]
    apply And.intro j1_eq_i ∘ And.intro j2_eq_i ∘ And.intro j1_eq_true ∘ And.intro j2_eq_false
    have l_ne_i : l.1.1 ≠ i.1 := by
      intro l_eq_i
      simp only [hasAssignment, Bool.not_eq_true] at h
      split at h
      all_goals
        simp +decide [getElem!_def, l_eq_i, i_in_bounds, h1] at h
    constructor
    · rw [Array.getElem_modify_of_ne l_ne_i]
      exact h1
    · constructor
      · exact h2
      · intro k k_ne_j1_succ k_ne_j2_succ
        have zero_in_bounds : 0 < (l :: acc.2.1).length := by
          simp only [List.length_cons]
          exact Nat.zero_lt_succ (List.length acc.snd.fst)
        by_cases k = ⟨0, zero_in_bounds⟩
        · next k_eq_zero =>
          simp only [k_eq_zero, List.length_cons, List.get, ne_eq]
          exact l_ne_i
        · next k_ne_zero =>
          have k_eq_succ : ∃ k' : Nat, ∃ k'_succ_in_bounds : k' + 1 < (l :: acc.2.1).length, k = ⟨k' + 1, k'_succ_in_bounds⟩ := by
            have k_val_ne_zero : k.1 ≠ 0 := by
              intro k_eq_zero
              simp only [List.length_cons, ← k_eq_zero, ne_eq, not_true] at k_ne_zero
            rcases Nat.exists_eq_succ_of_ne_zero k_val_ne_zero with ⟨k', k_eq_k'_succ⟩
            rw [Nat.succ_eq_add_one k'] at k_eq_k'_succ
            have k'_succ_in_bounds : k' + 1 < (l :: acc.2.1).length := by rw [← k_eq_k'_succ]; exact k.2
            apply Exists.intro k' ∘ Exists.intro k'_succ_in_bounds
            apply Fin.eq_of_val_eq
            exact k_eq_k'_succ
          rcases k_eq_succ with ⟨k', k'_succ_in_bounds, k_eq_succ⟩
          rw [k_eq_succ]
          simp only [List.get, Nat.add_eq, Nat.add_zero, ne_eq]
          have k'_in_bounds : k' < acc.2.1.length := by
            simp only [List.length_cons, Nat.succ_eq_add_one] at k'_succ_in_bounds
            exact Nat.lt_of_succ_lt_succ k'_succ_in_bounds
          have k'_ne_j1 : ⟨k', k'_in_bounds⟩ ≠ j1 := by
            simp only [List.length_cons, k_eq_succ, ne_eq, Fin.mk.injEq, Nat.succ.injEq, j1_succ] at k_ne_j1_succ
            exact Fin.ne_of_val_ne k_ne_j1_succ
          have k'_ne_j2 : ⟨k', k'_in_bounds⟩ ≠ j2 := by
            simp only [List.length_cons, k_eq_succ, ne_eq, Fin.mk.injEq, Nat.succ.injEq, j2_succ] at k_ne_j2_succ
            exact Fin.ne_of_val_ne k_ne_j2_succ
          exact h3 ⟨k', k'_in_bounds⟩ k'_ne_j1 k'_ne_j2

theorem derivedLitsInvariant_confirmRupHint {n : Nat} (f : DefaultFormula n) (f_assignments_size : f.assignments.size = n)
    (rupHints : Array Nat) (i : Fin rupHints.size)
    (acc : Array Assignment × CNF.Clause (PosFin n) × Bool × Bool)
    (ih : ∃ hsize : acc.1.size = n, DerivedLitsInvariant f f_assignments_size acc.1 hsize acc.2.1) :
    let rupHint_res := (confirmRupHint f.clauses) acc rupHints[i]
    ∃ hsize : rupHint_res.1.size = n, DerivedLitsInvariant f f_assignments_size rupHint_res.1 hsize rupHint_res.2.1 := by
  rcases ih with ⟨hsize, ih⟩
  have hsize' : Array.size ((confirmRupHint f.clauses) acc rupHints[i]).1 = n := by
    rw [size_assignemnts_confirmRupHint]
    exact hsize
  apply Exists.intro hsize'
  simp only [confirmRupHint, Fin.getElem_fin]
  split
  · exact ih
  · have rupHint_clause_options :
      f.clauses[rupHints[i.1]]? = none ∨ f.clauses[rupHints[i.1]]? = some none ∨ ∃ c, f.clauses[rupHints[i.val]]? = some (some c) := by
      match f.clauses[rupHints[i.val]]? with
      | none => exact Or.inl rfl
      | some none => exact Or.inr <| Or.inl rfl
      | some (some c) => exact (Or.inr ∘ Or.inr ∘ Exists.intro c) rfl
    rcases rupHint_clause_options with rupHint_clause_eq_none | rupHint_clause_eq_some_none | ⟨c, rupHint_clause_eq_c⟩
    · simp only [rupHint_clause_eq_none]
      exact ih
    · simp only [rupHint_clause_eq_some_none]
      exact ih
    · simp only [rupHint_clause_eq_c]
      have reduce_c_options : reduce c acc.1 = ReduceResult.encounteredBoth ∨ reduce c acc.1 = ReduceResult.reducedToEmpty ∨
        (∃ l : Literal (PosFin n), reduce c acc.1 = ReduceResult.reducedToUnit l) ∨ reduce c acc.1 = ReduceResult.reducedToNonunit := by
        match reduce c acc.fst with
        | ReduceResult.encounteredBoth => exact Or.inl rfl
        | ReduceResult.reducedToEmpty => exact (Or.inr ∘ Or.inl) rfl
        | ReduceResult.reducedToUnit l => exact (Or.inr ∘ Or.inr ∘ Or.inl ∘ Exists.intro l) rfl
        | ReduceResult.reducedToNonunit => exact (Or.inr ∘ Or.inr ∘ Or.inr) rfl
      rcases reduce_c_options with hencounteredBoth | hreducedToEmpty | ⟨l, hreducedToUnit⟩ | hreducedToNonunit
      · simp only [hencounteredBoth]
        exact ih
      · simp only [hreducedToEmpty]
        exact ih
      · simp only [hreducedToUnit]
        by_cases h : hasAssignment l.snd acc.fst[l.fst.val]!
        · simp only [h, ite_true]
          exact ih
        · simp only [h, ite_false]
          exact confirmRupHint_preserves_invariant_helper f f_assignments_size acc hsize l ih h
      · simp only [hreducedToNonunit]
        exact ih

theorem derivedLitsInvariant_performRupCheck {n : Nat} (f : DefaultFormula n) (f_assignments_size : f.assignments.size = n)
    (rupHints : Array Nat)
    (f'_assignments_size : (performRupCheck f rupHints).1.assignments.size = n) :
    let rupCheckRes := performRupCheck f rupHints
    DerivedLitsInvariant f f_assignments_size rupCheckRes.1.assignments f'_assignments_size rupCheckRes.2.1 := by
  let motive := fun (_ : Nat) (acc : Array Assignment × CNF.Clause (PosFin n) × Bool × Bool) =>
    ∃ hsize : acc.1.size = n, DerivedLitsInvariant f f_assignments_size acc.1 hsize acc.2.1
  have h_base : motive 0 (f.assignments, [], false, false) := by
    apply Exists.intro f_assignments_size
    intro i
    apply Or.inl
    constructor
    · rfl
    · intro l l_in_nil
      simp only [List.find?, List.not_mem_nil] at l_in_nil
  have h_inductive (i : Fin rupHints.size) (acc : Array Assignment × CNF.Clause (PosFin n) × Bool × Bool)
    (ih : motive i.1 acc) := derivedLitsInvariant_confirmRupHint f f_assignments_size rupHints i acc ih
  rcases Array.foldl_induction motive h_base h_inductive with ⟨_, h⟩
  exact h

theorem nodup_derivedLits {n : Nat} (f : DefaultFormula n)
    (f_assignments_size : f.assignments.size = n) (rupHints : Array Nat)
    (f'_assignments_size : (performRupCheck f rupHints).1.assignments.size = n)
    (derivedLits : CNF.Clause (PosFin n))
    (derivedLits_satisfies_invariant:
      DerivedLitsInvariant f f_assignments_size (performRupCheck f rupHints).fst.assignments f'_assignments_size derivedLits)
    (derivedLits_arr : Array (Literal (PosFin n))) (derivedLits_arr_def : derivedLits_arr = { toList := derivedLits })
    (i j : Fin (Array.size derivedLits_arr)) (i_ne_j : i ≠ j) :
    derivedLits_arr[i] ≠ derivedLits_arr[j] := by
  intro li_eq_lj
  let li := derivedLits_arr[i]
  have li_in_derivedLits : li ∈ derivedLits := by
    rw [Array.mem_toList, ← derivedLits_arr_def]
    simp [li, Array.getElem_mem]
  have i_in_bounds : i.1 < derivedLits.length := by
    have i_property := i.2
    simp only [derivedLits_arr_def, Array.size_toArray] at i_property
    exact i_property
  have j_in_bounds : j.1 < derivedLits.length := by
    have j_property := j.2
    simp only [derivedLits_arr_def, Array.size_toArray] at j_property
    exact j_property
  rcases derivedLits_satisfies_invariant ⟨li.1.1, li.1.2.2⟩ with ⟨_, h2⟩ | ⟨k, _, _, _, h3⟩ |
    ⟨k1, k2, _, _, k1_eq_true, k2_eq_false, _, _, h3⟩
  · exact h2 li li_in_derivedLits rfl
  · by_cases k.1 = i.1
    · next k_eq_i =>
      have j_ne_k : ⟨j.1, j_in_bounds⟩ ≠ k := by
        intro j_eq_k
        simp only [← j_eq_k] at k_eq_i
        exact i_ne_j <| Fin.eq_of_val_eq (Eq.symm k_eq_i)
      specialize h3 ⟨j.1, j_in_bounds⟩ j_ne_k
      simp only [derivedLits_arr_def, Fin.getElem_fin] at li_eq_lj
      simp only [Fin.getElem_fin, derivedLits_arr_def, ne_eq, li, li_eq_lj] at h3
      simp only [List.get_eq_getElem, ← Array.getElem_toList, not_true_eq_false] at h3
    · next k_ne_i =>
      have i_ne_k : ⟨i.1, i_in_bounds⟩ ≠ k := by intro i_eq_k; simp only [← i_eq_k, not_true] at k_ne_i
      specialize h3 ⟨i.1, i_in_bounds⟩ i_ne_k
      simp +decide [Fin.getElem_fin, derivedLits_arr_def, ne_eq, li] at h3
  · by_cases li.2 = true
    · next li_eq_true =>
      have i_ne_k2 : ⟨i.1, i_in_bounds⟩ ≠ k2 := by
        intro i_eq_k2
        rw [← i_eq_k2] at k2_eq_false
        simp only [List.get_eq_getElem] at k2_eq_false
        simp [derivedLits_arr_def, k2_eq_false, li] at li_eq_true
      have j_ne_k2 : ⟨j.1, j_in_bounds⟩ ≠ k2 := by
        intro j_eq_k2
        rw [← j_eq_k2] at k2_eq_false
        simp only [List.get_eq_getElem] at k2_eq_false
        simp only [derivedLits_arr_def, Fin.getElem_fin] at li_eq_lj
        simp [derivedLits_arr_def, k2_eq_false, li_eq_lj, li] at li_eq_true
      by_cases ⟨i.1, i_in_bounds⟩ = k1
      · next i_eq_k1 =>
        have j_ne_k1 : ⟨j.1, j_in_bounds⟩ ≠ k1 := by
          intro j_eq_k1
          rw [← j_eq_k1] at i_eq_k1
          simp only [Fin.mk.injEq] at i_eq_k1
          exact i_ne_j (Fin.eq_of_val_eq i_eq_k1)
        specialize h3 ⟨j.1, j_in_bounds⟩ j_ne_k1 j_ne_k2
        simp [li, li_eq_lj, derivedLits_arr_def] at h3
      · next i_ne_k1 =>
        specialize h3 ⟨i.1, i_in_bounds⟩ i_ne_k1 i_ne_k2
        apply h3
        simp +decide only [Fin.getElem_fin, ne_eq, derivedLits_arr_def, li]
        rfl
    · next li_eq_false =>
      simp only [Bool.not_eq_true] at li_eq_false
      have i_ne_k1 : ⟨i.1, i_in_bounds⟩ ≠ k1 := by
        intro i_eq_k1
        rw [← i_eq_k1] at k1_eq_true
        simp only [List.get_eq_getElem] at k1_eq_true
        simp [derivedLits_arr_def, k1_eq_true, li] at li_eq_false
      have j_ne_k1 : ⟨j.1, j_in_bounds⟩ ≠ k1 := by
        intro j_eq_k1
        rw [← j_eq_k1] at k1_eq_true
        simp only [List.get_eq_getElem] at k1_eq_true
        simp only [derivedLits_arr_def, Fin.getElem_fin] at li_eq_lj
        simp [derivedLits_arr_def, k1_eq_true, li_eq_lj, li] at li_eq_false
      by_cases ⟨i.1, i_in_bounds⟩ = k2
      · next i_eq_k2 =>
        have j_ne_k2 : ⟨j.1, j_in_bounds⟩ ≠ k2 := by
          intro j_eq_k2
          rw [← j_eq_k2] at i_eq_k2
          simp only [Fin.mk.injEq] at i_eq_k2
          exact i_ne_j (Fin.eq_of_val_eq i_eq_k2)
        specialize h3 ⟨j.1, j_in_bounds⟩ j_ne_k1 j_ne_k2
        simp [li, li_eq_lj, derivedLits_arr_def] at h3
      · next i_ne_k2 =>
        specialize h3 ⟨i.1, i_in_bounds⟩ i_ne_k1 i_ne_k2
        simp +decide [derivedLits_arr_def, li] at h3

theorem restoreAssignments_performRupCheck_base_case {n : Nat} (f : DefaultFormula n)
    (f_assignments_size : f.assignments.size = n)
    (f' : DefaultFormula n) (_f'_def : f' = (performRupCheck f rupHints).1)
    (f'_assignments_size : f'.assignments.size = n) (derivedLits : CNF.Clause (PosFin n))
    (derivedLits_arr : Array (Literal (PosFin n)))
    (derivedLits_arr_def : derivedLits_arr = {toList := derivedLits})
    (derivedLits_satisfies_invariant :
      DerivedLitsInvariant f f_assignments_size f'.assignments f'_assignments_size derivedLits)
    (_derivedLits_arr_nodup : ∀ (i j : Fin (Array.size derivedLits_arr)), i ≠ j → derivedLits_arr[i] ≠ derivedLits_arr[j]) :
    ClearInsertInductionMotive f f_assignments_size derivedLits_arr 0 f'.assignments := by
  apply Exists.intro f'_assignments_size
  intro i
  specialize derivedLits_satisfies_invariant i
  rcases derivedLits_satisfies_invariant with ⟨h1, h2⟩ | ⟨j, j_eq_i, h1, h2, h3⟩ |
    ⟨j1, j2, j1_eq_i, j2_eq_i, j1_eq_true, j2_eq_false, h1, h2, h3⟩
  · apply Or.inl
    constructor
    · exact h1
    · intro j _
      have idx_in_list : derivedLits_arr[j] ∈ derivedLits := by
        simp only [derivedLits_arr_def, Fin.getElem_fin]
        apply Array.getElem_mem_toList
      exact h2 derivedLits_arr[j] idx_in_list
  · apply Or.inr ∘ Or.inl
    have j_lt_derivedLits_arr_size : j.1 < derivedLits_arr.size := by
      simp only [derivedLits_arr_def, Array.size_toArray]
      exact j.2
    have i_gt_zero : i.1 > 0 := by rw [← j_eq_i]; exact (List.get derivedLits j).1.2.1
    refine ⟨⟨j.1, j_lt_derivedLits_arr_size⟩, List.get derivedLits j |>.2, i_gt_zero, ?_⟩
    constructor
    · apply Nat.zero_le
    · constructor
      · simp only [derivedLits_arr_def, Fin.getElem_fin, ← j_eq_i]
        rfl
      · apply And.intro h1 ∘ And.intro h2
        intro k _ k_ne_j
        have k_in_bounds : k < derivedLits.length := by
          have k_property := k.2
          simp only [derivedLits_arr_def, Array.size_toArray] at k_property
          exact k_property
        have k_ne_j : ⟨k.1, k_in_bounds⟩ ≠ j := by
          apply Fin.ne_of_val_ne
          simp only
          exact Fin.val_ne_of_ne k_ne_j
        simp only [Fin.getElem_fin, ne_eq, derivedLits_arr_def]
        exact h3 ⟨k.1, k_in_bounds⟩ k_ne_j
  · apply Or.inr ∘ Or.inr
    have j1_lt_derivedLits_arr_size : j1.1 < derivedLits_arr.size := by
      simp only [derivedLits_arr_def, Array.size_toArray]
      exact j1.2
    have j2_lt_derivedLits_arr_size : j2.1 < derivedLits_arr.size := by
      simp only [derivedLits_arr_def, Array.size_toArray]
      exact j2.2
    have i_gt_zero : i.1 > 0 := by rw [← j1_eq_i]; exact (List.get derivedLits j1).1.2.1
    refine ⟨⟨j1.1, j1_lt_derivedLits_arr_size⟩,
            ⟨j2.1, j2_lt_derivedLits_arr_size⟩,
            i_gt_zero, Nat.zero_le j1.1, Nat.zero_le j2.1, ?_⟩
    constructor
    · simp only [derivedLits_arr_def, Fin.getElem_fin, ← j1_eq_i]
      rw [← j1_eq_true]
      rfl
    · constructor
      · simp only [derivedLits_arr_def, Fin.getElem_fin, ← j2_eq_i]
        rw [← j2_eq_false]
        rfl
      · apply And.intro h1 ∘ And.intro h2
        intro k _ k_ne_j1 k_ne_j2
        have k_in_bounds : k < derivedLits.length := by
          have k_property := k.2
          simp only [derivedLits_arr_def, Array.size_toArray] at k_property
          exact k_property
        have k_ne_j1 : ⟨k.1, k_in_bounds⟩ ≠ j1 := by
          apply Fin.ne_of_val_ne
          simp only
          exact Fin.val_ne_of_ne k_ne_j1
        have k_ne_j2 : ⟨k.1, k_in_bounds⟩ ≠ j2 := by
          apply Fin.ne_of_val_ne
          simp only
          exact Fin.val_ne_of_ne k_ne_j2
        simp only [Fin.getElem_fin, ne_eq, derivedLits_arr_def]
        exact h3 ⟨k.1, k_in_bounds⟩ k_ne_j1 k_ne_j2

theorem restoreAssignments_performRupCheck {n : Nat} (f : DefaultFormula n) (f_assignments_size : f.assignments.size = n)
    (rupHints : Array Nat) :
    restoreAssignments (performRupCheck f rupHints).1.assignments (performRupCheck f rupHints).2.1
      =
    f.assignments := by
  rw [restoreAssignments]
  let f' := (performRupCheck f rupHints).1
  have f'_def : f' = (performRupCheck f rupHints).1 := rfl
  have f'_assignments_size : f'.assignments.size = n :=
    by rw [size_assignments_performRupCheck f rupHints, f_assignments_size]
  have derivedLits_satisfies_invariant := derivedLitsInvariant_performRupCheck f f_assignments_size rupHints f'_assignments_size
  simp only at derivedLits_satisfies_invariant
  generalize (performRupCheck f rupHints).2.1 = derivedLits at *
  rw [← f'_def, Array.foldl_toList]
  let derivedLits_arr : Array (Literal (PosFin n)) := {toList := derivedLits}
  have derivedLits_arr_def : derivedLits_arr = {toList := derivedLits} := rfl
  have derivedLits_arr_nodup := nodup_derivedLits f f_assignments_size rupHints f'_assignments_size derivedLits
    derivedLits_satisfies_invariant derivedLits_arr derivedLits_arr_def
  let motive := ClearInsertInductionMotive f f_assignments_size derivedLits_arr
  have h_base :=
    restoreAssignments_performRupCheck_base_case f f_assignments_size f' f'_def f'_assignments_size derivedLits
      derivedLits_arr derivedLits_arr_def derivedLits_satisfies_invariant derivedLits_arr_nodup
  have h_inductive (idx : Fin derivedLits_arr.size) (assignments : Array Assignment) (ih : motive idx.val assignments) :=
    clear_insert_inductive_case f f_assignments_size derivedLits_arr derivedLits_arr_nodup idx assignments ih
  rcases Array.foldl_induction motive h_base h_inductive with ⟨h_size, h⟩
  apply Array.ext
  · rw [← Array.foldl_toList, size_clearUnit_foldl f'.assignments clearUnit size_clearUnit derivedLits,
      f'_assignments_size, f_assignments_size]
  · intro i hi1 hi2
    rw [f_assignments_size] at hi2
    specialize h ⟨i, hi2⟩
    rcases h with ⟨h1, _⟩ | ⟨j, b, i_gt_zero, j_ge_derivedLits_size, _⟩ | ⟨j1, j2, i_gt_zero, j1_ge_derivedLits_size, _⟩
    · simp only [← derivedLits_arr_def]
      exact h1
    · exfalso
      exact (Nat.not_lt_of_le j_ge_derivedLits_size) j.2
    · exfalso
      exact (Nat.not_lt_of_le j1_ge_derivedLits_size) j1.2

theorem rupAdd_result {n : Nat} (f : DefaultFormula n) (c : DefaultClause n) (rupHints : Array Nat) (f' : DefaultFormula n)
    (f_readyForRupAdd : ReadyForRupAdd f) (rupAddSuccess : performRupAdd f c rupHints = (f', true)) :
    f' = insert f c := by
  rw [performRupAdd] at rupAddSuccess
  simp only [Bool.not_eq_true'] at rupAddSuccess
  split at rupAddSuccess
  · simp only [clear_insertRup f f_readyForRupAdd (negate c), Prod.mk.injEq, and_true] at rupAddSuccess
    exact rupAddSuccess.symm
  · split at rupAddSuccess
    · simp at rupAddSuccess
    · split at rupAddSuccess
      · simp at rupAddSuccess
      · let fc := (insertRupUnits f (negate c)).1
        have fc_assignments_size : (insertRupUnits f (negate c)).1.assignments.size = n := by
          rw [size_assignments_insertRupUnits f (negate c)]
          exact f_readyForRupAdd.2.1
        simp +zetaDelta only [clauses_performRupCheck, rupUnits_performRupCheck, ratUnits_performRupCheck,
          restoreAssignments_performRupCheck fc fc_assignments_size, Prod.mk.injEq, and_true] at rupAddSuccess
        have rupAddSuccess : DefaultFormula.insert (clearRupUnits (insertRupUnits f (negate c)).fst) c = f' := by
          rw [rupAddSuccess]
        rw [clear_insertRup f f_readyForRupAdd (negate c)] at rupAddSuccess
        exact rupAddSuccess.symm

end DefaultFormula

end Internal
end LRAT
end Std.Tactic.BVDecide
