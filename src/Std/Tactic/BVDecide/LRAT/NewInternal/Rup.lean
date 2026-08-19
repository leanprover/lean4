/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Std.Tactic.BVDecide.LRAT.NewInternal.Basic
public import Std.Tactic.BVDecide.LRAT.NewInternal.Assignment
import Init.Omega
import Init.ByCases
import Std.Sat.CNF.SpecLemmas
import Std.Tactic.Do

namespace Std.Tactic.BVDecide.LRAT.NewInternal

open Std.Sat Std.Do

inductive PropagateResult where
  | conflict
  | extended (assign : Assignment)
  | error

namespace State

def propagateHints (s : State) (assign : Assignment) (hints : Array Nat) : PropagateResult := Id.run do
  let mut assign := assign
  for hintIdx in hints do
    let some hintClause := s.get? hintIdx | return .error
    let mut unit : Option (Literal Nat) := none
    for (atom, pol) in hintClause do
      match assign.get? atom with
      | some value =>
        if value == pol then
          return .error
        else
          continue
      | none =>
        match unit with
        | none => unit := some (atom, pol)
        | some u =>
          if u == (atom, pol) then
            continue
          else
            return .error
    match unit with
    | none => return .conflict
    | some (atom, pol) => assign := assign.insert atom pol
  return .extended assign

def checkPropagate (s : State) (assign : Assignment) (rupHints : Array Nat) : Bool :=
  propagateHints s assign rupHints matches .conflict

public def checkRup (s : State) (clause : CNF.Clause Nat) (rupHints : Array Nat) : Bool := Id.run do
  let some assignment := Assignment.ofClause clause | return true
  checkPropagate s assignment rupHints

set_option mvcgen.warning false

theorem propagateHints_spec (s : State) (assign : Assignment) (hints : Array Nat) :
    match propagateHints s assign hints with
    | .conflict => CNF.Unsat (s.toCNF ++ assign.toCNF)
    | .extended newAssign => CNF.Entails (s.toCNF ++ assign.toCNF) newAssign.toCNF
    | .error => True := by
  generalize h : propagateHints s assign hints = x
  unfold propagateHints at h
  apply Id.of_wp_run_eq h
  clear h
  mvcgen invariants
  · Invariant.withEarlyReturnNewDo
      (onReturn := fun ret curAssign => ⌜
        match ret with
        | .error => True
        | .conflict =>
          CNF.Entails (s.toCNF ++ assign.toCNF) (s.toCNF ++ curAssign.toCNF)
          ∧ CNF.Unsat (s.toCNF ++ curAssign.toCNF)
        | .extended _ => False⌝)
      (onContinue := fun xs curAssign =>
        ⌜CNF.Entails (s.toCNF ++ assign.toCNF) (s.toCNF ++ curAssign.toCNF)⌝)
  · by
    next pref cur suff hfor b curAssign hintClause hclause hprev =>
    exact Invariant.withEarlyReturnNewDo
      (onReturn := fun ret _ => ⌜ret = .error⌝)
      (onContinue := fun xs unit => ⌜
        match unit with
        | some u =>
            curAssign.get? u.1 = none
            ∧ ∀ lit ∈ xs.prefix, lit = u ∨ curAssign.get? lit.1 = some !lit.2
        | none => ∀ lit ∈ xs.prefix, curAssign.get? lit.1 = some !lit.2⌝)
  all_goals mleave
  · simp
  · next pref1 cur1 suff1 hfor1 b1 curAssign hintClause hclause hout pref cur suff hfor b unit
      value hget hbeq ih =>
    have h3 : curAssign.get? cur.fst = some !cur.snd := by
      by_cases cur.snd <;> simp_all
    simp only [unit, true_and, reduceCtorEq, false_and, and_false, exists_false, or_false,
      List.forall_mem_append, List.forall_mem_singleton, h3, or_true, and_true] at ih ⊢
    split <;> simp_all
  · next pref1 cur1 suff1 hfor1 b1 curAssign hintClause hclause hout pref cur suff hfor b unit
      hget hnone ih =>
    simp only [unit] at hnone
    simp only [hnone, reduceCtorEq, false_and, and_false, exists_false, or_false, hget,
      true_and, and_true, List.forall_mem_append, List.forall_mem_singleton] at ih ⊢
    exact fun lit hlit => .inr (ih.right lit hlit)
  · next pref1 cur1 suff1 hfor1 b1 curAssign hintClause hclause hout pref cur suff hfor b unit
      hget u hsome hbeq ih =>
    simp only [beq_iff_eq] at hbeq
    simp only [unit] at hsome
    simp only [hsome, hbeq, hget, true_and, and_true, reduceCtorEq, false_and, and_false,
      exists_false, or_false, List.forall_mem_append, List.forall_mem_singleton] at ⊢ ih
    exact ih.right
  · simp
  · simp
  · simp_all
  · next pref cur suff hfor b curAssign hintClause hclause hout r hr1 hr2 ih =>
    simp only [hr1, hr2, reduceCtorEq, false_and, and_false, exists_false, or_false, true_and,
      CNF.Clause.mem_literals_iff, Option.some.injEq, exists_eq_left', false_or] at ih hout ⊢
    refine ⟨hout.right, ?_⟩
    rw [CNF.unsat_iff_not_sat]
    intro a hsat
    rw [CNF.sat_append] at hsat
    have hsatc := CNF.sat_of_mem hsat.left (mem_toCNF_of_eq_some hclause)
    exact Assignment.not_sat_of_forall_falsified hsat.right ih hsatc
  · next pref cur suff hfor b curAssign hintClause hclause hout r hr1 atom pol hr2 ih =>
    simp only [hr1, hr2, reduceCtorEq, false_and, and_false, exists_false, or_false, true_and,
      CNF.Clause.mem_literals_iff] at ih hout ⊢
    apply CNF.entails_trans hout.right
    apply CNF.entails_append_of_entails
    · exact CNF.append_entails_left
    · apply CNF.entails_trans (h2 := Assignment.toCNF_add_entails_toCNF_insert)
      rw [CNF.entails_add_iff]
      constructor
      · exact CNF.append_entails_right
      · rw [CNF.entails_clause_def]
        intro a ha
        rw [CNF.sat_append] at ha
        rw [CNF.Clause.sat_unit_iff]
        have hsatc := CNF.sat_of_mem ha.left (mem_toCNF_of_eq_some hclause)
        exact Assignment.unit_propagation ha.right hsatc ih.right
  · simp
  · simp [CNF.entails_refl]
  · next state ret hstate ih =>
    split
    · simp only [hstate, reduceCtorEq, false_and, Option.some.injEq, true_and, exists_eq_left',
        false_or] at ih
      exact CNF.unsat_of_entails_unsat ih.right ih.left
    · simp_all
    · simp_all
  · next state h1 ih =>
    simp only [h1, true_and, reduceCtorEq, false_and, exists_false, or_false] at ih
    exact CNF.entails_trans ih CNF.append_entails_right

theorem unsat_of_propagateHints_eq_conflict (h : propagateHints s assign hints = .conflict) :
    CNF.Unsat (s.toCNF ++ assign.toCNF) := by
  have := propagateHints_spec s assign hints
  simpa [h] using this

theorem entails_of_propagateHints_eq_extended
    (h : propagateHints s assign hints = .extended newAssign) :
    CNF.Entails (s.toCNF ++ assign.toCNF) newAssign.toCNF := by
  have := propagateHints_spec s assign hints
  simpa [h] using this

theorem unsat_of_checkPropagate (h : checkPropagate s assign rupHints) :
    CNF.Unsat (s.toCNF ++ assign.toCNF) := by
  unfold checkPropagate at h
  split at h
  · exact unsat_of_propagateHints_eq_conflict (by assumption)
  · contradiction

public theorem entails_clause_of_checkRup {s : State} {clause : CNF.Clause Nat}
    {rupHints : Array Nat} (h : checkRup s clause rupHints = true) :
    CNF.EntailsClause s.toCNF clause := by
  unfold checkRup at h
  match h1 : Assignment.ofClause clause with
  | some assign =>
    simp only [h1, Id.run] at h
    exact Assignment.entails_clause_of_unsat_of_ofClause_eq_some h1 (unsat_of_checkPropagate h)
  | none =>
    apply CNF.entails_clause_of_forall_sat
    apply Assignment.sat_of_ofClause_eq_none
    exact h1

end State

end Std.Tactic.BVDecide.LRAT.NewInternal
