/-
Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Clune
-/
prelude
import Std.Tactic.BVDecide.LRAT.Internal.Formula.RatAddResult

/-!
This module contains the verification of RAT-based clause adding for the default LRAT checker
implementation.
-/

namespace Std.Tactic.BVDecide
namespace LRAT
namespace Internal

namespace DefaultFormula

open Std.Sat
open DefaultClause DefaultFormula Assignment ReduceResult

theorem mem_of_necessary_assignment {n : Nat} {p : (PosFin n) → Bool} {c : DefaultClause n}
    {l : Literal (PosFin n)} (p_entails_c : p ⊨ c)
    (p'_not_entails_c : (fun v => if v = l.1 then l.2 else p v) ⊭ c) :
    Literal.negate l ∈ Clause.toList c := by
  simp only [(· ⊨ ·), Clause.eval, List.any_eq_true, decide_eq_true_eq, Prod.exists, Bool.exists_bool] at p_entails_c p'_not_entails_c
  simp only [not_exists, not_or, not_and] at p'_not_entails_c
  rcases p_entails_c with ⟨v, ⟨v_in_c, pv⟩ | ⟨v_in_c, pv⟩⟩
  · specialize p'_not_entails_c v
    have h := p'_not_entails_c.1 v_in_c
    simp only [Entails.eval, Bool.not_eq_false] at h
    split at h
    · next heq => simp [Literal.negate, ← heq, h, v_in_c]
    · next hne =>
      exfalso
      simp [(· ⊨ ·), h] at pv
  · specialize p'_not_entails_c v
    have h := p'_not_entails_c.2 v_in_c
    simp only [(· ⊨ ·), Bool.not_eq_false] at h
    split at h
    · next heq => simp [Literal.negate, ← heq, h, v_in_c]
    · next hne =>
      exfalso
      simp [(· ⊨ ·), h] at pv

theorem entails_of_irrelevant_assignment {n : Nat} {p : (PosFin n) → Bool} {c : DefaultClause n}
    {l : Literal (PosFin n)} (p_entails_cl : p ⊨ c.delete (Literal.negate l)) :
    (fun v => if v = l.1 then l.2 else p v) ⊨ c.delete (Literal.negate l) := by
  simp only [(· ⊨ ·), Clause.eval, List.any_eq_true, decide_eq_true_eq, Prod.exists, Bool.exists_bool,
    Clause.toList, delete_iff] at p_entails_cl
  simp only [(· ⊨ ·), Clause.eval, List.any_eq_true, decide_eq_true_eq, Prod.exists, Bool.exists_bool]
  rcases p_entails_cl with ⟨v, ⟨⟨negl_ne_v, v_in_c_del_l⟩, pv⟩ | ⟨⟨negl_ne_v, v_in_c_del_l⟩, pv⟩⟩
  · exists v
    left
    constructor
    · simp [Clause.toList, delete_iff, negl_ne_v, v_in_c_del_l]
    · split
      · next heq =>
        simp only [heq, Literal.negate, ne_eq, Prod.mk.injEq, true_and] at negl_ne_v
        simp_all
      · next hne =>
        exact pv
  · exists v
    right
    constructor
    · simp [Clause.toList, delete_iff, negl_ne_v, v_in_c_del_l]
    · split
      · next heq =>
        simp only [heq, Literal.negate, ne_eq, Prod.mk.injEq, true_and] at negl_ne_v
        simp_all
      · next hne =>
        exact pv

theorem assignmentsInvariant_insertRatUnits {n : Nat} (f : DefaultFormula n)
    (hf : f.ratUnits = #[] ∧ AssignmentsInvariant f) (units : CNF.Clause (PosFin n)) :
    AssignmentsInvariant (insertRatUnits f units).1 := by
  have h := insertRatUnits_postcondition f ⟨hf.1, hf.2.1⟩ units
  have hsize : (insertRatUnits f units).1.assignments.size = n := by rw [size_assignments_insertRatUnits, hf.2.1]
  apply Exists.intro hsize
  intro i b hb p hp
  simp only [(· ⊨ ·), Clause.eval] at hp
  simp only [toList, List.append_assoc,
    Entails.eval, List.any_eq_true, Prod.exists, Bool.exists_bool, Bool.decide_coe,
    List.all_eq_true, List.mem_append, List.mem_filterMap, id_eq, exists_eq_right, List.mem_map] at hp
  have pf : p ⊨ f := by
    simp only [(· ⊨ ·), Clause.eval]
    simp only [toList, List.append_assoc,
      Entails.eval, List.any_eq_true, Prod.exists, Bool.exists_bool,
      Bool.decide_coe, List.all_eq_true, List.mem_append, List.mem_filterMap, id_eq, exists_eq_right, List.mem_map]
    intro c cf
    rcases cf with cf | cf | cf
    · specialize hp c (Or.inl cf)
      exact hp
    · specialize hp c <| (Or.inr ∘ Or.inl) cf
      exact hp
    · simp [hf.1] at cf
  rcases h ⟨i.1, i.2.2⟩ with ⟨h1, h2⟩ | ⟨j, b', i_gt_zero, h1, h2, h3, h4⟩ | ⟨j1, j2, i_gt_zero, h1, h2, _, _, _⟩
  · rw [h1] at hb
    exact hf.2.2 i b hb p pf
  · rw [h2] at hb
    by_cases b = b'
    · next b_eq_b' =>
      let j_unit := unit (insertRatUnits f units).1.ratUnits[j]
      have j_unit_def : j_unit = unit (insertRatUnits f units).1.ratUnits[j] := rfl
      have j_unit_in_insertRatUnits_res :
        ∃ i : PosFin n,
          (i, false) ∈ (insertRatUnits f units).1.ratUnits.toList ∧ unit (i, false) = j_unit ∨
          (i, true) ∈ (insertRatUnits f units).1.ratUnits.toList ∧ unit (i, true) = j_unit := by
        apply Exists.intro i
        rw [j_unit_def, h1]
        by_cases hb' : b'
        · rw [hb']
          apply Or.inr
          constructor
          · have h1 : (insertRatUnits f units).fst.ratUnits[j] = (i, true) := by
              rw [hb'] at h1
              simp only [h1, Prod.mk.injEq, and_true]
              rfl
            rw [← h1]
            apply Array.getElem_mem_toList
          · rfl
        · simp only [Bool.not_eq_true] at hb'
          rw [hb']
          apply Or.inl
          constructor
          · have h1 : (insertRatUnits f units).fst.ratUnits[j] = (i, false) := by
              rw [hb'] at h1
              simp only [h1, Prod.mk.injEq, and_true]
              rfl
            rw [← h1]
            apply Array.getElem_mem_toList
          · rfl
      specialize hp j_unit ((Or.inr ∘ Or.inr) j_unit_in_insertRatUnits_res)
      simp only [List.any_eq_true, Prod.exists, Bool.exists_bool, Bool.decide_coe, Fin.getElem_fin, List.find?, j_unit] at hp
      simp only [Fin.getElem_fin] at h1
      rcases hp with ⟨i', hp⟩
      simp only [h1, Clause.toList, unit_eq, List.mem_singleton, Prod.mk.injEq] at hp
      rcases hp with ⟨hp1, hp2⟩ | ⟨hp1, hp2⟩
      · simp only [b_eq_b', ← hp1.2, (· ⊨ ·)]
        rw [hp1.1] at hp2
        exact of_decide_eq_true hp2
      · simp only [b_eq_b', ← hp1.2, (· ⊨ ·)]
        rw [hp1.1] at hp2
        exact hp2
    · next b_ne_b' =>
      apply hf.2.2 i b _ p pf
      have b'_def : b' = (decide ¬b = true) := by cases b <;> cases b' <;> simp at *
      rw [has_iff_has_add_complement, ← b'_def, hb]
  · let j1_unit := unit (insertRatUnits f units).1.ratUnits[j1]
    have j1_unit_def : j1_unit = unit (insertRatUnits f units).1.ratUnits[j1] := rfl
    have j1_unit_in_insertRatUnits_res :
      ∃ i : PosFin n,
        (i, false) ∈ (insertRatUnits f units).1.ratUnits.toList ∧ unit (i, false) = j1_unit ∨
        (i, true) ∈ (insertRatUnits f units).1.ratUnits.toList ∧ unit (i, true) = j1_unit := by
      apply Exists.intro i ∘ Or.inr
      rw [j1_unit_def, h1]
      constructor
      · have h1 : (insertRatUnits f units).fst.ratUnits[j1] = (i, true) := by
          rw [h1]
          simp only [Prod.mk.injEq, and_true]
          rfl
        rw [← h1]
        apply Array.getElem_mem_toList
      · rfl
    let j2_unit := unit (insertRatUnits f units).1.ratUnits[j2]
    have j2_unit_def : j2_unit = unit (insertRatUnits f units).1.ratUnits[j2] := rfl
    have j2_unit_in_insertRatUnits_res :
      ∃ i : PosFin n,
        (i, false) ∈ (insertRatUnits f units).1.ratUnits.toList ∧ unit (i, false) = j2_unit ∨
        (i, true) ∈ (insertRatUnits f units).1.ratUnits.toList ∧ unit (i, true) = j2_unit := by
      apply Exists.intro i ∘ Or.inl
      rw [j2_unit_def, h2]
      constructor
      · have h2 : (insertRatUnits f units).fst.ratUnits[j2] = (i, false) := by
          rw [h2]
          simp only [Prod.mk.injEq, and_true]
          rfl
        rw [← h2]
        apply Array.getElem_mem_toList
      · rfl
    have hp1 := hp j1_unit ((Or.inr ∘ Or.inr) j1_unit_in_insertRatUnits_res)
    have hp2 := hp j2_unit ((Or.inr ∘ Or.inr) j2_unit_in_insertRatUnits_res)
    simp only [List.any_eq_true, Prod.exists, Bool.exists_bool, Bool.decide_coe, Fin.getElem_fin, List.find?] at hp1 hp2
    rcases hp1 with ⟨i1, hp1⟩
    rcases hp2 with ⟨i2, hp2⟩
    simp only [Fin.getElem_fin] at h1 h2
    simp only [(· ⊨ ·), h1, Clause.toList, unit_eq, List.mem_singleton, Prod.mk.injEq,
      and_false, false_and, and_true, false_or, h2, or_false, j1_unit, j2_unit] at hp1 hp2
    simp_all
    simp [hp2.1, ← hp1.1, hp1.2] at hp2

theorem sat_of_confirmRupHint_of_insertRat_fold {n : Nat} (f : DefaultFormula n)
    (hf : f.ratUnits = #[] ∧ AssignmentsInvariant f) (c : DefaultClause n) (rupHints : Array Nat)
    (p : PosFin n → Bool) (pf : p ⊨ f) :
    let fc := insertRatUnits f (negate c)
    let confirmRupHint_fold_res := rupHints.foldl (confirmRupHint fc.1.clauses) (fc.1.assignments, [], false, false) 0 rupHints.size
    confirmRupHint_fold_res.2.2.1 = true → p ⊨ c := by
  intro fc confirmRupHint_fold_res confirmRupHint_success
  let motive := ConfirmRupHintFoldEntailsMotive fc.1
  have h_base : motive 0 (fc.fst.assignments, [], false, false) := by
    simp [ConfirmRupHintFoldEntailsMotive, size_assignments_insertRatUnits, hf.2.1, fc, motive]
    have fc_satisfies_AssignmentsInvariant : AssignmentsInvariant fc.1 :=
      assignmentsInvariant_insertRatUnits f hf (negate c)
    exact limplies_of_assignmentsInvariant fc.1 fc_satisfies_AssignmentsInvariant
  have h_inductive (idx : Fin rupHints.size) (acc : Array Assignment × CNF.Clause (PosFin n) × Bool × Bool) (ih : motive idx.1 acc) :=
    confirmRupHint_preserves_motive fc.1 rupHints idx acc ih
  rcases Array.foldl_induction motive h_base h_inductive with ⟨_, h1, h2⟩
  have fc_incompatible_confirmRupHint_fold_res := (h2 confirmRupHint_success)
  rw [Incompatible.symm] at fc_incompatible_confirmRupHint_fold_res
  have fc_unsat :=
    unsat_of_limplies_and_incompatible (PosFin n) fc.1 confirmRupHint_fold_res.1 h1 fc_incompatible_confirmRupHint_fold_res p
  by_cases pc : p ⊨ c
  · exact pc
  · exfalso -- Derive contradiction from pc, pf, and fc_unsat
    simp only [(· ⊨ ·), Clause.eval, List.any_eq_true, Prod.exists, Bool.exists_bool, not_exists,
      not_or, not_and, Bool.not_eq_true] at pc
    simp only [formulaEntails_def, List.all_eq_true, decide_eq_true_eq, Classical.not_forall,
      not_imp] at fc_unsat
    rcases fc_unsat with ⟨unsat_c, unsat_c_in_fc, p_unsat_c⟩
    have unsat_c_in_fc := mem_of_insertRatUnits f (negate c) unsat_c unsat_c_in_fc
    simp only [List.mem_map, Prod.exists, Bool.exists_bool] at unsat_c_in_fc
    rcases unsat_c_in_fc with ⟨v, ⟨v_in_neg_c, unsat_c_eq⟩ | ⟨v_in_neg_c, unsat_c_eq⟩⟩ | unsat_c_in_f
    · simp only [negate_eq, List.mem_map, Prod.exists, Bool.exists_bool] at v_in_neg_c
      rcases v_in_neg_c with ⟨v', ⟨_, v'_eq_v⟩ | ⟨v'_in_c, v'_eq_v⟩⟩
      · simp [Literal.negate] at v'_eq_v
      · simp only [Literal.negate, Bool.not_true, Prod.mk.injEq, and_true] at v'_eq_v
        simp only [(· ⊨ ·), Clause.eval, List.any_eq_true, decide_eq_true_eq, Prod.exists,
          Bool.exists_bool, ← unsat_c_eq, not_exists, not_or, not_and] at p_unsat_c
        specialize p_unsat_c v
        rw [Clause.unit_eq] at p_unsat_c
        simp only [List.mem_singleton, forall_const, Prod.mk.injEq, and_false, false_implies, and_true] at p_unsat_c
        simp only [(· ⊨ ·), Bool.not_eq_false] at p_unsat_c
        specialize pc v
        rw [v'_eq_v] at v'_in_c
        have pv := pc.2 v'_in_c
        simp only [(· ⊨ ·), Bool.not_eq_true] at pv
        simp only [p_unsat_c] at pv
        cases pv
    · simp only [negate_eq, List.mem_map, Prod.exists, Bool.exists_bool] at v_in_neg_c
      rcases v_in_neg_c with ⟨v', ⟨v'_in_c, v'_eq_v⟩ | ⟨_, v'_eq_v⟩⟩
      · simp only [Literal.negate, Bool.not_false, Prod.mk.injEq, and_true] at v'_eq_v
        simp only [(· ⊨ ·), Clause.eval, List.any_eq_true, decide_eq_true_eq, Prod.exists,
          Bool.exists_bool, ← unsat_c_eq, not_exists, not_or, not_and] at p_unsat_c
        specialize p_unsat_c v
        rw [Clause.unit_eq] at p_unsat_c
        simp only [List.mem_singleton, forall_const, Prod.mk.injEq, and_false, false_implies, and_true] at p_unsat_c
        specialize pc v
        rw [v'_eq_v] at v'_in_c
        have pv := pc.1 v'_in_c
        simp only [(· ⊨ ·), Bool.not_eq_true] at pv
        simp only [p_unsat_c] at pv
        cases pv
      · simp [Literal.negate] at v'_eq_v
    · simp only [formulaEntails_def, List.all_eq_true, decide_eq_true_eq] at pf
      exact p_unsat_c <| pf unsat_c unsat_c_in_f

theorem sat_of_insertRat {n : Nat} (f : DefaultFormula n)
    (hf : f.ratUnits = #[] ∧ AssignmentsInvariant f) (c : DefaultClause n) (p : PosFin n → Bool)
    (pf : p ⊨ f) :
    (insertRatUnits f (negate c)).2 = true → p ⊨ c := by
  simp only [insertRatUnits]
  intro insertUnit_fold_success
  rcases contradiction_of_insertUnit_fold_success f.assignments hf.2.1 f.ratUnits false (negate c) (by intro; contradiction)
    insertUnit_fold_success with ⟨i, hboth⟩
  have i_in_bounds : i.1 < f.assignments.size := by rw [hf.2.1]; exact i.2.2
  have h0 : InsertUnitInvariant f.assignments hf.2.1 f.ratUnits f.assignments hf.2.1 := by
    intro i
    simp only [Fin.getElem_fin, ne_eq, true_and, Bool.not_eq_true, exists_and_right]
    apply Or.inl
    intro j
    rw [hf.1] at j
    exact Fin.elim0 j
  have insertUnit_fold_satisfies_invariant := insertUnitInvariant_insertUnit_fold f.assignments hf.2.1 f.ratUnits
    f.assignments hf.2.1 false (negate c) h0
  rcases insertUnit_fold_satisfies_invariant ⟨i.1, i.2.2⟩ with ⟨h1, h2⟩ | ⟨j, b, i_gt_zero, h1, h2, h3, h4⟩ |
    ⟨j1, j2, i_gt_zero, h1, h2, _, _, _⟩
  · rw [h1] at hboth
    simp only at hboth
    have hpos : hasAssignment true (f.assignments[i.1]'i_in_bounds) = true := by simp only [hboth]; decide
    have hneg : hasAssignment false (f.assignments[i.1]'i_in_bounds) = true := by simp only [hboth]; decide
    have p_entails_i_true := hf.2.2 i true hpos p pf
    have p_entails_i_false := hf.2.2 i false hneg p pf
    simp only [Entails.eval] at p_entails_i_true p_entails_i_false
    simp [p_entails_i_true] at p_entails_i_false
  · simp only [(· ⊨ ·), Clause.eval, List.any_eq_true, Prod.exists, Bool.exists_bool, Bool.decide_coe]
    apply Exists.intro i
    have ib_in_insertUnit_fold : (i, b) ∈ (List.foldl insertUnit (f.ratUnits, f.assignments, false) (negate c)).1.toList := by
      have i_rw : i = ⟨i.1, i.2⟩ := rfl
      rw [i_rw, ← h1]
      apply List.get_mem
    have ib_in_insertUnit_fold := mem_insertUnit_fold_units f.ratUnits f.assignments false (negate c) (i, b) ib_in_insertUnit_fold
    simp only [negate, Literal.negate, List.mem_map, Prod.mk.injEq, Prod.exists, Bool.exists_bool,
      Bool.not_false, Bool.not_true, hf.1, Array.toList_toArray, List.find?, List.not_mem_nil, or_false]
      at ib_in_insertUnit_fold
    rw [hboth] at h2
    rcases ib_in_insertUnit_fold with ⟨i', ⟨i_false_in_c, i'_eq_i, b_eq_true⟩ | ⟨i_true_in_c, i'_eq_i, b_eq_false⟩⟩
    · apply Or.inl
      rw [i'_eq_i] at i_false_in_c
      apply And.intro i_false_in_c
      simp only [addAssignment, ← b_eq_true, addPosAssignment, ite_true] at h2
      split at h2
      · simp at h2
      · next heq =>
        have hasNegAssignment_fi : hasAssignment false (f.assignments[i.1]'i_in_bounds) := by
          simp +decide only [hasAssignment, hasPosAssignment, heq]
        have p_entails_i := hf.2.2 i false hasNegAssignment_fi p pf
        simp only [(· ⊨ ·)] at p_entails_i
        simp only [p_entails_i, decide_true]
      · next heq =>
        exfalso
        rw [heq] at h3
        exact h3 (has_both b)
      · simp at h2
    · apply Or.inr
      rw [i'_eq_i] at i_true_in_c
      apply And.intro i_true_in_c
      simp only [addAssignment, ← b_eq_false, addNegAssignment, ite_false, reduceCtorEq] at h2
      split at h2
      · next heq =>
        have hasPosAssignment_fi : hasAssignment true (f.assignments[i.1]'i_in_bounds) := by
          simp only [hasAssignment, hasPosAssignment, ite_true, heq]
        have p_entails_i := hf.2.2 i true hasPosAssignment_fi p pf
        simp only [(· ⊨ ·)] at p_entails_i
        exact p_entails_i
      · simp at h2
      · next heq =>
        exfalso
        rw [heq] at h3
        exact h3 (has_both b)
      · simp at h2
  · exfalso
    have i_true_in_insertUnit_fold : (i, true) ∈ (List.foldl insertUnit (f.ratUnits, f.assignments, false) (negate c)).1.toList := by
      have i_rw : i = ⟨i.1, i.2⟩ := rfl
      rw [i_rw, ← h1]
      apply List.get_mem
    have i_false_in_insertUnit_fold : (i, false) ∈ (List.foldl insertUnit (f.ratUnits, f.assignments, false) (negate c)).1.toList := by
      have i_rw : i = ⟨i.1, i.2⟩ := rfl
      rw [i_rw, ← h2]
      apply List.get_mem
    simp only [hf.1, negate, Literal.negate] at i_true_in_insertUnit_fold i_false_in_insertUnit_fold
    have i_true_in_insertUnit_fold :=
      mem_insertUnit_fold_units #[] f.assignments false (c.clause.map Literal.negate) (i, true) i_true_in_insertUnit_fold
    have i_false_in_insertUnit_fold :=
      mem_insertUnit_fold_units #[] f.assignments false (c.clause.map Literal.negate) (i, false) i_false_in_insertUnit_fold
    simp only [Literal.negate, List.mem_map, Prod.mk.injEq, Bool.not_eq_true', Prod.exists,
      exists_eq_right_right, exists_eq_right, Array.toList_toArray, List.find?, List.not_mem_nil, or_false,
      Bool.not_eq_false'] at i_true_in_insertUnit_fold i_false_in_insertUnit_fold
    have c_not_tautology := Clause.not_tautology c (i, true)
    simp only [Clause.toList] at c_not_tautology
    rcases c_not_tautology with i_true_not_in_c | i_false_not_in_c
    · exact i_true_not_in_c i_false_in_insertUnit_fold
    · exact i_false_not_in_c i_true_in_insertUnit_fold

theorem safe_insert_of_performRupCheck_insertRat {n : Nat} (f : DefaultFormula n)
    (hf : f.ratUnits = #[] ∧ AssignmentsInvariant f) (c : DefaultClause n) (rupHints : Array Nat) :
    (performRupCheck (insertRatUnits f (negate c)).1 rupHints).2.2.1 = true
      →
    Limplies (PosFin n) f (f.insert c) := by
  intro performRupCheck_success p pf
  simp only [performRupCheck] at performRupCheck_success
  simp only [formulaEntails_def, List.all_eq_true, decide_eq_true_eq]
  intro c' c'_in_fc
  rw [insert_iff] at c'_in_fc
  rcases c'_in_fc with c'_eq_c | c'_in_f
  · rw [c'_eq_c]
    exact sat_of_confirmRupHint_of_insertRat_fold f hf c rupHints p pf performRupCheck_success
  · simp only [formulaEntails_def, List.all_eq_true, decide_eq_true_eq] at pf
    exact pf c' c'_in_f

theorem assignmentsInvariant_performRupCheck_of_assignmentsInvariant {n : Nat} (f : DefaultFormula n)
    (f_AssignmentsInvariant : AssignmentsInvariant f) (rupHints : Array Nat) :
    AssignmentsInvariant (performRupCheck f rupHints).1 := by
  simp only [performRupCheck]
  let motive := ConfirmRupHintFoldEntailsMotive f
  have h_base : motive 0 (f.assignments, [], false, false) := by
    simp [ConfirmRupHintFoldEntailsMotive, f_AssignmentsInvariant.1,
      limplies_of_assignmentsInvariant f f_AssignmentsInvariant, motive]
  have h_inductive (idx : Fin rupHints.size) (acc : Array Assignment × CNF.Clause (PosFin n) × Bool × Bool) (ih : motive idx.1 acc) :=
    confirmRupHint_preserves_motive f rupHints idx acc ih
  rcases Array.foldl_induction motive h_base h_inductive with ⟨hsize, h1, _⟩
  apply Exists.intro hsize
  intro i b h p pf
  simp only at h
  specialize h1 p pf
  simp only [( · ⊨ ·), Bool.not_eq_true] at h1
  specialize h1 i
  have i_in_bounds :
    i.1 < (rupHints.foldl (fun b => confirmRupHint f.clauses b) (f.assignments, [], false, false) 0 rupHints.size).1.size := by
    let in_bounds_motive (_idx : Nat) (acc : Array Assignment × CNF.Clause (PosFin n) × Bool × Bool) := acc.1.size = n
    have in_bounds_base : in_bounds_motive 0 (f.assignments, [], false, false) := by
      simp only [f_AssignmentsInvariant.1, in_bounds_motive]
    have in_bounds_inductive (idx : Fin rupHints.size) (acc : Array Assignment × CNF.Clause (PosFin n) × Bool × Bool)
      (ih : in_bounds_motive idx.1 acc) : in_bounds_motive (idx.1 + 1) (confirmRupHint f.clauses acc rupHints[idx]) := by
      have h := size_assignemnts_confirmRupHint f.clauses acc.1 acc.2.1 acc.2.2.1 acc.2.2.2 rupHints[idx]
      have : (acc.fst, acc.snd.fst, acc.snd.snd.fst, acc.snd.snd.snd) = acc := rfl
      simp [this] at *
      omega
    rw [Array.foldl_induction in_bounds_motive in_bounds_base in_bounds_inductive]
    exact i.2.2
  simp only [getElem!, i_in_bounds, dite_true, Array.get_eq_getElem, decidableGetElem?] at h1
  simp only [( · ⊨ ·), Entails.eval.eq_1]
  by_cases hb : b
  · rw [hb]
    rw [hb] at h
    by_cases pi : p i
    · exact pi
    · simp only at pi
      simp [pi, h] at h1
  · simp only [Bool.not_eq_true] at hb
    rw [hb]
    rw [hb] at h
    by_cases pi : p i
    · simp [pi, h] at h1
    · simp at pi
      exact pi

theorem c_without_negPivot_of_performRatCheck_success {n : Nat} (f : DefaultFormula n)
    (hf : f.ratUnits = #[] ∧ AssignmentsInvariant f) (negPivot : Literal (PosFin n))
    (ratHint : Nat × Array Nat) (performRatCheck_success : (performRatCheck f negPivot ratHint).2)
    (c : DefaultClause n) :
    f.clauses[ratHint.1]! = some c → Limplies (PosFin n) f (c.delete negPivot) := by
  intro hc p pf
  simp only [performRatCheck, hc, Bool.or_eq_true, Bool.not_eq_true'] at performRatCheck_success
  split at performRatCheck_success
  · next h =>
    exact sat_of_insertRat f hf (c.delete negPivot) p pf h
  · split at performRatCheck_success
    · simp at performRatCheck_success
    · next h =>
      simp only [not_or, Bool.not_eq_true, Bool.not_eq_false] at h
      have pfc : p ⊨ f.insert (c.delete negPivot) :=
        safe_insert_of_performRupCheck_insertRat f hf (c.delete negPivot) ratHint.2 h.2 p pf
      rw [DefaultFormula.formulaEntails_def, List.all_eq_true] at pfc
      exact of_decide_eq_true (pfc (c.delete negPivot) (by simp [insert_iff]))

theorem existsRatHint_of_ratHintsExhaustive {n : Nat} (f : DefaultFormula n)
    (f_readyForRatAdd : ReadyForRatAdd f) (pivot : Literal (PosFin n))
    (ratHints : Array (Nat × Array Nat))
    (ratHintsExhaustive_eq_true : ratHintsExhaustive f pivot ratHints = true) (c' : DefaultClause n)
    (c'_in_f : c' ∈ toList f) (negPivot_in_c' : Literal.negate pivot ∈ Clause.toList c') :
    ∃ i : Fin ratHints.size, f.clauses[ratHints[i].1]! = some c' := by
  simp only [toList, f_readyForRatAdd.2.1, Array.toList_toArray, List.map, List.append_nil, f_readyForRatAdd.1,
    List.mem_filterMap, id_eq, exists_eq_right] at c'_in_f
  rw [List.mem_iff_getElem] at c'_in_f
  rcases c'_in_f with ⟨i, hi, c'_in_f⟩
  simp only [ratHintsExhaustive, getRatClauseIndices] at ratHintsExhaustive_eq_true
  have i_in_bounds : i < Array.size (Array.range (Array.size f.clauses)) := by
    rw [Array.size_range]
    simpa using hi
  have i_lt_f_clauses_size : i < f.clauses.size := by
    rw [Array.size_range] at i_in_bounds
    exact i_in_bounds
  have h : i ∈ (ratHints.map (fun x => x.1)).toList := by
    rw [← of_decide_eq_true ratHintsExhaustive_eq_true]
    have i_eq_range_i : i = (Array.range f.clauses.size)[i]'i_in_bounds := by
      rw [Array.getElem_range]
    rw [i_eq_range_i]
    rw [Array.mem_toList]
    rw [Array.mem_filter]
    constructor
    · rw [← Array.mem_toList]
      apply Array.getElem_mem_toList
    · rw [← Array.getElem_eq_getElem_toList] at c'_in_f
      simp only [getElem!, Array.getElem_range, i_lt_f_clauses_size, dite_true,
        c'_in_f, DefaultClause.contains_iff, Array.get_eq_getElem, decidableGetElem?]
      simpa [Clause.toList] using negPivot_in_c'
  rcases List.get_of_mem h with ⟨j, h'⟩
  have j_in_bounds : j < ratHints.size := by
    have j_property := j.2
    simp only [Array.toList_map, List.length_map] at j_property
    dsimp at *
    omega
  simp only [List.get_eq_getElem, Array.toList_map, Array.length_toList, List.getElem_map] at h'
  rw [← Array.getElem_eq_getElem_toList] at h'
  rw [← Array.getElem_eq_getElem_toList] at c'_in_f
  exists ⟨j.1, j_in_bounds⟩
  simp [getElem!, h', i_lt_f_clauses_size, dite_true, c'_in_f, decidableGetElem?]

theorem performRatCheck_success_of_performRatCheck_fold_success {n : Nat} (f : DefaultFormula n)
    (hf : f.ratUnits = #[] ∧ f.assignments.size = n) (p : Literal (PosFin n))
    (ratHints : Array (Nat × Array Nat)) (i : Fin ratHints.size)
    (performRatCheck_fold_success :
    (ratHints.foldl
      (fun acc ratHint => if acc.2 = true then performRatCheck acc.1 p ratHint else (acc.1, false))
      (f, true) 0 ratHints.size).2 = true) : (performRatCheck f p ratHints[i]).2 = true := by
  let motive (idx : Nat) (acc : DefaultFormula n × Bool) : Prop :=
    acc.1 = f ∧ (acc.2 = true → ∀ i : Fin idx, (performRatCheck f p ratHints[i]!).2)
  have h_base : motive 0 (f, true) := by
    constructor
    · rfl
    · intro _ i
      exact Fin.elim0 i
  let fold_fn (acc : DefaultFormula n × Bool) (ratHint : Nat × Array Nat) :=
    if acc.2 = true then performRatCheck acc.1 p ratHint else (acc.1, false)
  have fold_fn_def (acc : DefaultFormula n × Bool) (ratHint : Nat × Array Nat) :
    fold_fn acc ratHint = if acc.2 = true then performRatCheck acc.1 p ratHint else (acc.1, false) := rfl
  have h_inductive (idx : Fin ratHints.size) (acc : DefaultFormula n × Bool) (ih : motive idx.1 acc) :
    motive (idx.1 + 1) (fold_fn acc ratHints[idx]) := by
    constructor
    · simp only [Fin.getElem_fin, fold_fn_def, ih.1]
      split
      · rw [formula_performRatCheck]
        exact hf
      · rfl
    · intro h i
      rw [fold_fn_def] at h
      split at h
      · next acc_eq_true =>
        have i_lt_or_eq_idx : i.1 < idx.1 ∨ i.1 = idx.1 := by
          omega
        rcases i_lt_or_eq_idx with i_lt_idx | i_eq_idx
        · exact ih.2 acc_eq_true ⟨i.1, i_lt_idx⟩
        · simp only [getElem!, i_eq_idx, idx.2, Fin.getElem_fin, dite_true, decidableGetElem?]
          simp only [Fin.getElem_fin, ih.1] at h
          exact h
      · simp at h
  have h := (Array.foldl_induction motive h_base h_inductive).2 performRatCheck_fold_success i
  simpa [getElem!, i.2, dite_true, decidableGetElem?] using h

theorem safe_insert_of_performRatCheck_fold_success {n : Nat} (f : DefaultFormula n)
    (f_readyForRatAdd : ReadyForRatAdd f) (c : DefaultClause n) (pivot : Literal (PosFin n))
    (rupHints : Array Nat) (ratHints : Array (Nat × Array Nat))
    (pivot_in_c : pivot ∈ Clause.toList c)
    (ratHintsExhaustive_eq_true : ratHintsExhaustive f pivot ratHints = true)
    (performRatCheck_fold_success :
      (Array.foldl
        (fun x ratHint => if x.2 = true then performRatCheck x.1 (Literal.negate pivot) ratHint else (x.1, false))
        ((performRupCheck (insertRupUnits f (negate c)).1 rupHints).1, true) ratHints 0 (Array.size ratHints)).2 = true) :
    Equisat (PosFin n) f (insert f c) := by
  constructor
  · intro h p pfc
    specialize h p
    simp only [(· ⊨ ·), List.all_eq_true, decide_eq_true_eq, Classical.not_forall,
      exists_prop, nonempty_prop] at h pfc
    rcases h with ⟨c', c'_in_f, pc'⟩
    have c'_in_fc : c' ∈ toList (insert f c) := by rw [insert_iff]; exact Or.inr c'_in_f
    exact pc' <| pfc c' c'_in_fc
  · intro fc_unsat p pf
    by_cases pc : p ⊨ c
    · specialize fc_unsat p
      simp only [(· ⊨ ·), List.any_eq_true, Prod.exists, Bool.exists_bool,
        Bool.decide_coe, List.all_eq_true, Classical.not_forall, not_exists, exists_prop] at fc_unsat
      rcases fc_unsat with ⟨c', c'_in_fc, pc'⟩
      rw [insert_iff] at c'_in_fc
      rcases c'_in_fc with c'_eq_c | c'_in_f
      · simp only [c'_eq_c, decide_eq_true_eq] at pc'
        exact pc' pc
      · simp only [(· ⊨ ·), List.any_eq_true, Prod.exists, Bool.exists_bool,
          Bool.decide_coe, List.all_eq_true] at pf
        exact pc' <| pf c' c'_in_f
    · rw [← Clause.limplies_iff_mem] at pivot_in_c
      let p' : (PosFin n) → Bool := fun a => if a = pivot.1 then pivot.2 else p a
      have p'_entails_c : p' ⊨ c := by
        specialize pivot_in_c p'
        simp only [(· ⊨ ·), ite_eq_left_iff, not_true, false_implies, forall_const, p'] at pivot_in_c
        exact pivot_in_c
      specialize fc_unsat p'
      simp only [formulaEntails_def, List.all_eq_true, decide_eq_true_eq, Classical.not_forall,
        not_imp] at fc_unsat
      rcases fc_unsat with ⟨c', c'_in_fc, p'_not_entails_c'⟩
      simp only [insert_iff, Array.toList_toArray, List.mem_singleton] at c'_in_fc
      rcases c'_in_fc with c'_eq_c | c'_in_f
      · rw [← c'_eq_c] at p'_entails_c
        exact p'_not_entails_c' p'_entails_c
      · have pc' : p ⊨ c' := by
          rw [DefaultFormula.formulaEntails_def, List.all_eq_true] at pf
          exact of_decide_eq_true <| pf c' c'_in_f
        have negPivot_in_c' : Literal.negate pivot ∈ Clause.toList c' := mem_of_necessary_assignment pc' p'_not_entails_c'
        have h : p ⊨ (c'.delete (Literal.negate pivot)) := by
          rcases existsRatHint_of_ratHintsExhaustive f f_readyForRatAdd pivot ratHints
            ratHintsExhaustive_eq_true c' c'_in_f negPivot_in_c' with ⟨i, hc'⟩
          have h_performRupCheck_res :
            (performRupCheck (insertRupUnits f (negate c)).fst rupHints).fst.ratUnits = #[] ∧
            (performRupCheck (insertRupUnits f (negate c)).fst rupHints).fst.assignments.size = n := by
            simp only [ratUnits_performRupCheck, ratUnits_insertRupUnits, f_readyForRatAdd.1,
              size_assignments_performRupCheck, size_assignments_insertRupUnits, f_readyForRatAdd.2.2.1, and_self]
          have performRatCheck_success :=
            performRatCheck_success_of_performRatCheck_fold_success (performRupCheck (insertRupUnits f (negate c)).1 rupHints).1
              h_performRupCheck_res (Literal.negate pivot) ratHints i performRatCheck_fold_success
          have performRupCheck_res_satisfies_AssignmentsInvariant :
            AssignmentsInvariant (performRupCheck (insertRupUnits f (negate c)).1 rupHints).1 := by
            apply assignmentsInvariant_performRupCheck_of_assignmentsInvariant (insertRupUnits f (negate c)).1
            apply assignmentsInvariant_insertRupUnits_of_assignmentsInvariant f f_readyForRatAdd.2
          have h :=
            c_without_negPivot_of_performRatCheck_success (performRupCheck (insertRupUnits f (negate c)).fst rupHints).1
              ⟨h_performRupCheck_res.1, performRupCheck_res_satisfies_AssignmentsInvariant⟩ (Literal.negate pivot) ratHints[i]
              performRatCheck_success
          simp only [clauses_performRupCheck, clauses_insertRupUnits, Fin.getElem_fin] at h
          apply h c' hc' p
          simp only [(· ⊨ ·), Clause.eval]
          simp only [List.any_eq_true, Prod.exists, Bool.exists_bool,
            Bool.decide_coe, List.all_eq_true, decide_eq_true_eq]
          intro c'' hc''
          simp only [toList, clauses_performRupCheck, rupUnits_performRupCheck,
            ratUnits_performRupCheck] at hc''
          rw [← toList] at hc''
          have hc'' := mem_of_insertRupUnits f (negate c) c'' hc''
          rcases hc'' with c''_in_negc | c''_in_f
          · simp only [(· ⊨ ·), Clause.eval] at pc
            simp only [List.any_eq_true, decide_eq_true_eq, Prod.exists, Bool.exists_bool, not_exists,
              not_or, not_and, Clause.toList, DefaultClause.toList] at pc
            simp only [negate, Literal.negate, List.map_map, List.mem_map, Function.comp_apply, Prod.exists,
              Bool.exists_bool, Bool.not_false, Bool.not_true] at c''_in_negc
            rcases c''_in_negc with ⟨l, ⟨l_in_negc, l_def⟩ | ⟨l_in_negc, l_def⟩⟩
            · apply Exists.intro l ∘ Or.inr
              simp only [← l_def, Clause.unit_eq, List.mem_singleton, decide_eq_true_eq, true_and, (· ⊨ ·)]
              have h := (pc l).1 l_in_negc
              simp only [(· ⊨ ·), Bool.not_eq_false] at h
              assumption
            · apply Exists.intro l ∘ Or.inl
              simp only [← l_def, Clause.unit_eq, List.mem_singleton, decide_eq_true_eq, true_and, (· ⊨ ·)]
              have h := (pc l).2 l_in_negc
              simp only [(· ⊨ ·), Bool.not_eq_true] at h
              assumption
          · simp only [(· ⊨ ·), Clause.eval] at pf
            simp only [List.any_eq_true, Prod.exists, Bool.exists_bool, Bool.decide_coe, List.all_eq_true] at pf
            simp only [Bool.decide_eq_false, Bool.not_eq_true'] at pf
            apply pf
            assumption
        have p'_entails_c'_del_negPivot : p' ⊨ c'.delete (Literal.negate pivot) := entails_of_irrelevant_assignment h
        exact p'_not_entails_c' <| Clause.entails_of_entails_delete p'_entails_c'_del_negPivot

theorem ratAdd_sound {n : Nat} (f : DefaultFormula n) (c : DefaultClause n)
    (pivot : Literal (PosFin n)) (rupHints : Array Nat) (ratHints : Array (Nat × Array Nat))
    (f' : DefaultFormula n) (f_readyForRatAdd : ReadyForRatAdd f) (pivot_in_c : pivot ∈ Clause.toList c)
    (ratAddSuccess : performRatAdd f c pivot rupHints ratHints = (f', true)) :
    Equisat (PosFin n) f f' := by
  have f'_def := ratAdd_result f c pivot rupHints ratHints f' f_readyForRatAdd pivot_in_c ratAddSuccess
  rw [performRatAdd] at ratAddSuccess
  simp only [Bool.not_eq_true'] at ratAddSuccess
  split at ratAddSuccess
  · next ratHintsExhaustive_eq_true =>
    split at ratAddSuccess
    · simp at ratAddSuccess
    · split at ratAddSuccess
      · simp at ratAddSuccess
      · split at ratAddSuccess
        · simp at ratAddSuccess
        · split at ratAddSuccess
          · simp at ratAddSuccess
          · next performRatCheck_fold_success =>
            simp only [Bool.not_eq_false] at performRatCheck_fold_success
            rw [f'_def]
            exact safe_insert_of_performRatCheck_fold_success f f_readyForRatAdd c pivot rupHints ratHints pivot_in_c
              ratHintsExhaustive_eq_true performRatCheck_fold_success
  · simp at ratAddSuccess

end DefaultFormula

end Internal
end LRAT
end Std.Tactic.BVDecide
