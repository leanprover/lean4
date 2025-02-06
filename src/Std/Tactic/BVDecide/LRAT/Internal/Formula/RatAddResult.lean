/-
Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Clune
-/
prelude
import Std.Tactic.BVDecide.LRAT.Internal.Formula.RupAddSound

/-!
This module contains the implementation of RAT-based clause adding for the default LRAT checker
implementation.
-/

namespace Std.Tactic.BVDecide
namespace LRAT
namespace Internal

namespace DefaultFormula

open Std.Sat
open DefaultClause DefaultFormula Assignment

theorem size_assignments_insertRatUnits {n : Nat} (f : DefaultFormula n)
    (units : CNF.Clause (PosFin n)) :
    (f.insertRatUnits units).1.assignments.size = f.assignments.size := by
  simp only [insertRatUnits]
  exact size_insertUnit_fold f.ratUnits f.assignments false

theorem insertRatUnits_postcondition {n : Nat} (f : DefaultFormula n)
    (hf : f.ratUnits = #[] ∧ f.assignments.size = n)
    (units : CNF.Clause (PosFin n)) :
    let assignments := (insertRatUnits f units).fst.assignments
    have hsize : assignments.size = n := by
      rw [← hf.2]
      exact size_assignments_insertRatUnits f units
    let ratUnits := (insertRatUnits f units).1.ratUnits
    InsertUnitInvariant f.assignments hf.2 ratUnits assignments hsize := by
  simp only [insertRatUnits]
  have hsize : f.assignments.size = n := by rw [hf.2]
  have h0 : InsertUnitInvariant f.assignments hf.2 f.ratUnits f.assignments hsize := by
    intro i
    apply Or.inl
    simp only [Fin.getElem_fin, ne_eq, true_and, Bool.not_eq_true, exists_and_right]
    intro j
    simp only [hf.1, Array.size_toArray, List.length_nil] at j
    exact Fin.elim0 j
  exact insertUnitInvariant_insertUnit_fold f.assignments hf.2 f.ratUnits f.assignments hsize false units h0

theorem nodup_insertRatUnits {n : Nat} (f : DefaultFormula n)
    (hf : f.ratUnits = #[] ∧ f.assignments.size = n) (units : CNF.Clause (PosFin n)) :
    ∀ i : Fin (f.insertRatUnits units).1.ratUnits.size, ∀ j : Fin (f.insertRatUnits units).1.ratUnits.size,
      i ≠ j → (f.insertRatUnits units).1.ratUnits[i] ≠ (f.insertRatUnits units).1.ratUnits[j] := by
  intro i j i_ne_j
  rcases hi : (insertRatUnits f units).fst.ratUnits[i] with ⟨li, bi⟩
  rcases hj : (insertRatUnits f units).fst.ratUnits[j] with ⟨lj, bj⟩
  intro heq
  cases heq
  have h := insertRatUnits_postcondition f hf units ⟨li.1, li.2.2⟩
  simp only [ne_eq, Bool.not_eq_true, exists_and_right] at h
  rcases h with ⟨_, h2⟩ | ⟨k, b, _, _, _, h4⟩ | ⟨k1, k2, li_gt_zero, h1, h2, h3, h4, h5⟩
  · specialize h2 j
    rw [hj] at h2
    contradiction
  · by_cases i = k
    · next i_eq_k =>
      have j_ne_k : j ≠ k := by rw [← i_eq_k]; exact i_ne_j.symm
      specialize h4 j j_ne_k
      simp +decide only [hj] at h4
    · next i_ne_k =>
      specialize h4 i i_ne_k
      simp +decide only [hi] at h4
  · by_cases bi
    · next bi_eq_true =>
      by_cases i = k1
      · next i_eq_k1 =>
        have j_ne_k1 : j ≠ k1 := by rw [← i_eq_k1]; exact i_ne_j.symm
        by_cases j = k2
        · next j_eq_k2 =>
          rw [← j_eq_k2, hj, bi_eq_true] at h2
          simp at h2
        · next j_ne_k2 =>
          specialize h5 j j_ne_k1 j_ne_k2
          simp +decide only [hj] at h5
      · next i_ne_k1 =>
        by_cases i = k2
        · next i_eq_k2 =>
          rw [← i_eq_k2, hi, bi_eq_true] at h2
          simp at h2
        · next i_ne_k2 =>
          specialize h5 i i_ne_k1 i_ne_k2
          simp only [hi, not_true] at h5
    · next bi_eq_false =>
      simp only [Bool.not_eq_true] at bi_eq_false
      by_cases i = k2
      · next i_eq_k2 =>
        have j_ne_k2 : j ≠ k2 := by rw [← i_eq_k2]; exact i_ne_j.symm
        by_cases j = k1
        · next j_eq_k1 =>
          rw [← j_eq_k1, hj, bi_eq_false] at h1
          simp at h1
        · next j_ne_k1 =>
          specialize h5 j j_ne_k1 j_ne_k2
          simp +decide only [hj] at h5
      · next i_ne_k2 =>
        by_cases i = k1
        · next i_eq_k1 =>
          rw [← i_eq_k1, hi, bi_eq_false] at h1
          simp at h1
        · next i_ne_k1 =>
          specialize h5 i i_ne_k1 i_ne_k2
          simp +decide only [hi] at h5

theorem clear_insertRat_base_case {n : Nat} (f : DefaultFormula n)
    (hf : f.ratUnits = #[] ∧ f.assignments.size = n) (units : CNF.Clause (PosFin n)) :
    let insertRat_res := insertRatUnits f units
    ClearInsertInductionMotive f hf.2 insertRat_res.1.ratUnits 0 insertRat_res.1.assignments := by
  have insertRatUnits_assignments_size := size_assignments_insertRatUnits f units
  rw [hf.2] at insertRatUnits_assignments_size
  apply Exists.intro insertRatUnits_assignments_size
  intro i
  simp only [Nat.zero_le, Fin.getElem_fin, ne_eq, forall_const, true_and]
  exact insertRatUnits_postcondition f hf units i

theorem clear_insertRat {n : Nat} (f : DefaultFormula n)
    (hf : f.ratUnits = #[] ∧ f.assignments.size = n) (units : CNF.Clause (PosFin n)) :
    clearRatUnits (f.insertRatUnits units).1 = f := by
  simp only [clearRatUnits]
  ext : 1
  · simp only [insertRatUnits]
  · simp only [insertRatUnits]
  · rw [hf.1]
  · simp only
    let motive := ClearInsertInductionMotive f hf.2 (insertRatUnits f units).1.ratUnits
    have h_base : motive 0 (insertRatUnits f units).1.assignments := clear_insertRat_base_case f hf units
    have h_inductive (idx : Fin (insertRatUnits f units).1.ratUnits.size) (assignments : Array Assignment)
      (ih : motive idx.val assignments) : motive (idx.val + 1) (clearUnit assignments (insertRatUnits f units).1.ratUnits[idx]) :=
      clear_insert_inductive_case f hf.2 (insertRatUnits f units).1.ratUnits
        (nodup_insertRatUnits f hf units) idx assignments ih
    rcases Array.foldl_induction motive h_base h_inductive with ⟨h_size, h⟩
    apply Array.ext
    · rw [h_size, hf.2]
    · intro i hi1 hi2
      have i_lt_n : i < n := by omega
      specialize h ⟨i, i_lt_n⟩
      rcases h with h | h | h
      · exact h.1
      · omega
      · omega

theorem formula_performRatCheck {n : Nat} (f : DefaultFormula n)
    (hf : f.ratUnits = #[] ∧ f.assignments.size = n) (p : Literal (PosFin n))
    (ratHint : Nat × Array Nat) :
    (performRatCheck f p ratHint).1 = f := by
  simp only [performRatCheck, Bool.or_eq_true, Bool.not_eq_true']
  split
  · next c _ =>
    split
    · rw [clear_insertRat f hf]
    · let fc := (insertRatUnits f (negate (DefaultClause.delete c p))).1
      have fc_assignments_size : fc.assignments.size = n := by rw [size_assignments_insertRatUnits, hf.2]
      have insertRatUnits_rw : (insertRatUnits f (negate (DefaultClause.delete c p))).1 =
        ⟨(insertRatUnits f (negate (DefaultClause.delete c p))).1.clauses,
         (insertRatUnits f (negate (DefaultClause.delete c p))).1.rupUnits,
         (insertRatUnits f (negate (DefaultClause.delete c p))).1.ratUnits,
         (insertRatUnits f (negate (DefaultClause.delete c p))).1.assignments⟩ := rfl
      simp only [clauses_performRupCheck, rupUnits_performRupCheck, ratUnits_performRupCheck]
      rw [restoreAssignments_performRupCheck fc fc_assignments_size ratHint.2, ← insertRatUnits_rw,
        clear_insertRat f hf (negate (DefaultClause.delete c p))]
      split <;> rfl
  · rfl

theorem performRatCheck_fold_formula_eq {n : Nat} (f : DefaultFormula n)
    (hf : f.ratUnits = #[] ∧ f.assignments.size = n) (p : Literal (PosFin n))
    (ratHints : Array (Nat × Array Nat)) :
    let performRatCheck_fold_res :=
      ratHints.foldl
        (fun x ratHint =>
          if x.2 = true then
            performRatCheck x.1 p ratHint
          else
            (x.1, false)) (f, true) 0 ratHints.size
    performRatCheck_fold_res.1 = f := by
  let motive (_idx : Nat) (acc : DefaultFormula n × Bool) := acc.1 = f
  have h_base : motive 0 (f, true) := rfl
  have h_inductive (idx : Fin ratHints.size) (acc : DefaultFormula n × Bool) :
    motive idx.1 acc → motive (idx.1 + 1) (if acc.2 then performRatCheck acc.1 p ratHints[idx] else (acc.1, false)) := by
    intro ih
    rw [ih]
    split
    · exact formula_performRatCheck f hf p ratHints[idx]
    · rfl
  exact Array.foldl_induction motive h_base h_inductive

theorem ratAdd_result {n : Nat} (f : DefaultFormula n) (c : DefaultClause n) (p : Literal (PosFin n))
  (rupHints : Array Nat) (ratHints : Array (Nat × Array Nat)) (f' : DefaultFormula n)
  (f_readyForRatAdd : ReadyForRatAdd f) (_pc : p ∈ Clause.toList c)
  (ratAddSuccess : performRatAdd f c p rupHints ratHints = (f', true)) : f' = insert f c := by
  rw [performRatAdd] at ratAddSuccess
  simp only [Bool.not_eq_true'] at ratAddSuccess
  split at ratAddSuccess
  · split at ratAddSuccess
    · simp at ratAddSuccess
    · split at ratAddSuccess
      · simp at ratAddSuccess
      · split at ratAddSuccess
        · simp at ratAddSuccess
        · split at ratAddSuccess
          · simp at ratAddSuccess
          · next performRatCheck_fold_success =>
            simp only [Bool.not_eq_false] at performRatCheck_fold_success
            let fc := (insertRupUnits f (negate c)).1
            have fc_assignments_size : (insertRupUnits f (negate c)).1.assignments.size = n := by
              rw [size_assignments_insertRupUnits f (negate c)]
              exact f_readyForRatAdd.2.2.1
            simp only [clauses_performRupCheck, rupUnits_performRupCheck, ratUnits_performRupCheck,
              restoreAssignments_performRupCheck fc fc_assignments_size, Prod.mk.injEq, and_true] at ratAddSuccess
            rw [← ratAddSuccess]
            clear f' ratAddSuccess
            let performRupCheck_res := (performRupCheck (insertRupUnits f (negate c)).1 rupHints).1
            have h_performRupCheck_res : performRupCheck_res.ratUnits = #[] ∧ performRupCheck_res.assignments.size = n := by
              have hsize : performRupCheck_res.assignments.size = n := by
                rw [size_assignments_performRupCheck, size_assignments_insertRupUnits, f_readyForRatAdd.2.2.1]
              exact And.intro f_readyForRatAdd.1 hsize
            have insertRupUnits_rw : (insertRupUnits f (negate c)).1 =
              ⟨(insertRupUnits f (negate c)).1.clauses, (insertRupUnits f (negate c)).1.rupUnits,
               (insertRupUnits f (negate c)).1.ratUnits, (insertRupUnits f (negate c)).1.assignments⟩ := rfl
            simp +zetaDelta only [performRatCheck_fold_formula_eq performRupCheck_res h_performRupCheck_res (Literal.negate p) ratHints,
              clauses_performRupCheck, rupUnits_performRupCheck, ratUnits_performRupCheck,
              restoreAssignments_performRupCheck fc fc_assignments_size, ← insertRupUnits_rw,
              clear_insertRup f f_readyForRatAdd.2 (negate c), fc, performRupCheck_res]
  · simp at ratAddSuccess

end DefaultFormula

end Internal
end LRAT
end Std.Tactic.BVDecide
