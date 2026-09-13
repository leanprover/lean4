/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Std.Tactic.BVDecide.LRAT.Internal.Basic
public import Std.Tactic.BVDecide.LRAT.Internal.Assignment
import Init.Omega
import Init.ByCases
import Std.Sat.CNF.SpecLemmas
import Std.Tactic.Do

namespace Std.Tactic.BVDecide.LRAT.Internal

set_option mvcgen.warning false

open Std.Sat Std.Do

public inductive PropagateResult where
  | conflict
  | extended (assign : Assignment)
  | error

namespace State

public def propagateHints (s : State) (assign : Assignment) (hints : Array Nat) :
    PropagateResult := Id.run do
  let mut assign := assign
  for hintIdx in hints do
    let some hintClause := s.get? hintIdx | return .error
    let mut unit : Option Nat := none
    for (atom, pol) in hintClause do
      if (assign.get? atom).all (· == pol) then
        match unit with
        | none =>
          unit := some atom
          assign := assign.insert atom pol
        | some u =>
          if atom = u then continue else return .error
      else
        match unit with
        | none => continue
        | some u =>
          if atom = u then return .error else continue
    match unit with
    | none => return .conflict
    | some _ => continue
  return .extended assign

public def checkPropagate (s : State) (assign : Assignment) (rupHints : Array Nat) : Bool :=
  propagateHints s assign rupHints matches .conflict

public def checkRup (s : State) (clause : CNF.Clause Nat) (rupHints : Array Nat) : Bool := Id.run do
  let some assignment := Assignment.ofClause clause | return true
  checkPropagate s assignment rupHints

set_option linter.deprecated.syntax false in
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
      (onContinue := fun xs state => ⌜
        match state.2 with
        | some atom => ∃ pol,
            (curAssign.get? atom).all (· == pol)
            ∧ state.1 = curAssign.insert atom pol
            ∧ ∀ lit ∈ xs.prefix, lit = (atom, pol) ∨ curAssign.get? lit.1 = some !lit.2
        | none =>
            state.1 = curAssign
            ∧ ∀ lit ∈ xs.prefix, curAssign.get? lit.1 = some !lit.2⌝)
  all_goals mleave
  · next pref1 cur1 suff1 hfor1 b1 curAssign hintClause hclause hout pref cur suff hfor b st
      assignNow unit hval hunit ih =>
    simp only [unit, st, assignNow] at hunit ih hval ⊢
    simp only [hunit, reduceCtorEq, false_and, and_false, exists_false, or_false] at ih
    simp only [ih, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hval ⊢
    refine Or.inl ⟨by trivial, cur.snd, hval, rfl, fun lit hlit => ?_⟩
    cases hlit
    next hlit => simp [hlit, ih]
    next hlit => simp [hlit]
  · next pref1 cur1 suff1 hfor1 b1 curAssign hintClause hclause hout pref cur suff hfor b st
      assignNow unit hval u hunit hcur ih =>
    simp only [unit, st, assignNow] at hunit ih hval ⊢
    simp only [hunit, reduceCtorEq, false_and, and_false, exists_false, or_false] at ih
    obtain ⟨_, pol, hunitVal, hinsert, ih⟩ := ih
    refine Or.inl ⟨by trivial, pol, hunitVal, hinsert, fun lit hlit => ?_⟩
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hlit
    cases hlit
    next hlit => simp [hlit, ih]
    next hlit =>
      simp only [hinsert, hcur, Assignment.get?_insert_of_eq, Option.all_some, beq_iff_eq] at hval
      simp [←hcur, hlit, hval]
  · simp
  · next pref1 cur1 suff1 hfor1 b1 curAssign hintClause hclause hout pref cur suff hfor b st
      assignNow unit hval hunit ih =>
    simp only [unit, st, assignNow] at hunit ih hval ⊢
    simp only [hunit, reduceCtorEq, false_and, and_false, exists_false, or_false] at ih
    simp only [ih, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hval ⊢
    refine Or.inl ⟨by trivial, by trivial, fun lit hlit => ?_⟩
    cases hlit
    next hlit => simp [hlit, ih]
    next hlit =>
      simp only [←hlit, Bool.not_eq_true, Option.all_eq_false] at hval
      obtain ⟨val, hget, hval⟩ := hval
      simp only [beq_eq_false_iff_ne, ne_eq] at hval
      simp [hget, Bool.eq_not, hval]
  · simp
  · next pref1 cur1 suff1 hfor1 b1 curAssign hintClause hclause hout pref cur suff hfor b st
      assignNow unit hval u hunit hcur ih =>
    simp only [unit, st, assignNow] at hunit ih hval ⊢
    simp only [hunit, reduceCtorEq, false_and, and_false, exists_false, or_false] at ih
    obtain ⟨_, pol, hunitVal, hinsert, ih⟩ := ih
    refine Or.inl ⟨by trivial, pol, hunitVal, hinsert, fun lit hlit => ?_⟩
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hlit
    cases hlit
    next hlit => simp [hlit, ih]
    next hlit =>
      simp only [hinsert, Bool.not_eq_true, Option.all_eq_false, Assignment.get?_insert_of_ne (Ne.symm hcur)] at hval
      obtain ⟨val, hget, hval⟩ := hval
      simp only [beq_eq_false_iff_ne, ne_eq] at hval
      simp [hlit, hget, Bool.eq_not, hval]
  · simp
  · simp_all
  · next pref cur suff hfor b curAssign hintClause hclause hout r st assignNow unit hr1 hr2 ih =>
    simp only [unit, st, assignNow] at hr2 ⊢
    simp only [hr1, hr2, reduceCtorEq, false_and, and_false, exists_false, or_false, true_and,
      CNF.Clause.mem_literals_iff, Option.some.injEq, exists_eq_left', false_or] at ih hout ⊢
    obtain ⟨hsame, ih⟩ := ih
    rw [hsame]
    refine ⟨hout.right, ?_⟩
    rw [CNF.unsat_iff_not_sat]
    intro a hsat
    rw [CNF.sat_append] at hsat
    have hsatc := CNF.sat_of_mem hsat.left (mem_toCNF_of_eq_some hclause)
    exact Assignment.not_sat_of_forall_falsified hsat.right ih hsatc
  · next pref cur suff hfor b curAssign hintClause hclause hout r st assignNow unit hr1 u hsome ih =>
    simp only [unit, st, assignNow] at hsome ⊢
    simp only [hr1, hsome, reduceCtorEq, false_and, and_false, exists_false, or_false, true_and,
      CNF.Clause.mem_literals_iff] at ih hout ⊢
    obtain ⟨pol, hnone, hins, hall⟩ := ih
    rw [hins]
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
        exact Assignment.unit_propagation ha.right hsatc hall
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

public theorem unsat_of_propagateHints_eq_conflict (h : propagateHints s assign hints = .conflict) :
    CNF.Unsat (s.toCNF ++ assign.toCNF) := by
  have := propagateHints_spec s assign hints
  simpa [h] using this

public theorem entails_of_propagateHints_eq_extended
    (h : propagateHints s assign hints = .extended newAssign) :
    CNF.Entails (s.toCNF ++ assign.toCNF) newAssign.toCNF := by
  have := propagateHints_spec s assign hints
  simpa [h] using this

public theorem unsat_of_checkPropagate (h : checkPropagate s assign rupHints) :
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

end Std.Tactic.BVDecide.LRAT.Internal
