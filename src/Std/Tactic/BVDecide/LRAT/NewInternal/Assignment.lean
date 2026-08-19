/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Std.Data.HashMap
public import Init.Data.Hashable
public import Std.Sat.CNF.Unit
import Std.Sat.CNF.Unit
import Std.Sat.CNF.SpecLemmas
import Std.Tactic.Do
public import Std.Sat.CNF.Entails

public section

namespace Std.Tactic.BVDecide.LRAT.NewInternal

open Std.Sat Std.Do

/--
The value of an atom under an `Assignment`.
-/
inductive AssignValue where
  | unassigned
  | true
  | false

namespace AssignValue

@[inline]
def ofBool : Bool → AssignValue
  | Bool.true => .true
  | Bool.false => .false

@[inline]
def toOption : AssignValue → Option Bool
  | .unassigned => none
  | .true => some Bool.true
  | .false => some Bool.false

@[simp]
theorem toOption_ofBool : (ofBool b).toOption = some b := by
  cases b <;> rfl

end AssignValue

structure Assignment where
  assign : Std.HashMap Nat AssignValue

namespace Assignment

def empty : Assignment := Assignment.mk {}

@[inline]
def get (a : Assignment) (atom : Nat) : AssignValue :=
  a.assign.getD atom .unassigned

@[inline]
def get? (a : Assignment) (atom : Nat) : Option Bool :=
  (a.get atom).toOption

private theorem get?_eq_bind {a : Assignment} :
    a.get? atom = a.assign[atom]?.bind AssignValue.toOption := by
  rw [get?, get, Std.HashMap.getD_eq_getD_getElem?]
  cases a.assign[atom]? <;> rfl

@[simp]
theorem get?_empty : Assignment.empty.get? atom = none := by
  simp [get?_eq_bind, empty]

@[inline]
def insert (a : Assignment) (atom : Nat) (b : Bool) : Assignment :=
  { a with assign := a.assign.insert atom (.ofBool b) }

@[simp]
theorem get?_insert_of_eq {a : Assignment} (h : atom = atom') :
    (a.insert atom b).get? atom' = some b := by
  simp [insert, get?_eq_bind, h]

@[simp]
theorem get?_insert_of_ne {a : Assignment} (h : atom ≠ atom') :
    (a.insert atom b).get? atom' = a.get? atom' := by
  simp [insert, get?_eq_bind, Std.HashMap.getElem?_insert, h]

@[simp]
theorem get_eq_unassigned_iff {a : Assignment} :
    a.get atom = .unassigned ↔ a.get? atom = none := by
  rw [get?]
  cases a.get atom <;> simp [AssignValue.toOption]

@[simp]
theorem get_eq_true_iff {a : Assignment} :
    a.get atom = .true ↔ a.get? atom = some true := by
  rw [get?]
  cases a.get atom <;> simp [AssignValue.toOption]

@[simp]
theorem get_eq_false_iff {a : Assignment} :
    a.get atom = .false ↔ a.get? atom = some false := by
  rw [get?]
  cases a.get atom <;> simp [AssignValue.toOption]

def toCNF (a : Assignment) : CNF Nat :=
  a.assign.toList.foldl (init := .empty) fun acc (atom, value) =>
    match value.toOption with
    | some pol => acc.add (.unit atom pol)
    | none => acc

private theorem sat_foldl_add_unit_iff {a : Nat → Bool} {l : List (Nat × AssignValue)}
    {init : CNF Nat} :
    (l.foldl (fun acc (atom, value) =>
        match value.toOption with
        | some pol => acc.add (.unit atom pol)
        | none => acc) init).Sat a
      ↔ (init.Sat a ∧ ∀ p ∈ l, ∀ pol, p.2.toOption = some pol → a p.1 = pol) := by
  induction l generalizing init with
  | nil => simp
  | cons x xs ih =>
    rcases x with ⟨atom, value⟩
    rw [List.foldl_cons, ih]
    cases value <;> simp_all [AssignValue.toOption, and_assoc, and_left_comm]

theorem sat_toCNF_iff {assign : Assignment} (a : Nat → Bool) :
    assign.toCNF.Sat a ↔ (∀ atom pol, assign.get? atom = some pol → a atom = pol) := by
  rw [toCNF, sat_foldl_add_unit_iff]
  simp only [CNF.sat_empty, true_and, Prod.forall]
  constructor
  · intro h atom pol hget
    rw [get?_eq_bind, Option.bind_eq_some_iff] at hget
    rcases hget with ⟨v, hv1, hv2⟩
    exact h atom v (Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr hv1) pol hv2
  · intro h atom v hmem pol hv
    apply h atom pol
    rw [get?_eq_bind, Std.HashMap.mem_toList_iff_getElem?_eq_some.mp hmem]
    exact hv

theorem not_sat_of_forall_falsified {assign : Assignment} {c : CNF.Clause Nat} {a : Nat → Bool}
    (h1 : assign.toCNF.Sat a) (h2 : ∀ lit ∈ c, assign.get? lit.1 = some !lit.2) :
    ¬c.Sat a := by
  rw [CNF.Clause.not_sat_iff_forall_mem_ne]
  intro lit hlit
  have := (sat_toCNF_iff a).mp h1 lit.1 (!lit.2) (h2 lit hlit)
  simp [this]

theorem unit_propagation {assign : Assignment} {c : CNF.Clause Nat} {unit : Literal Nat}
    {a : Nat → Bool} (h1 : assign.toCNF.Sat a) (h2 : c.Sat a)
    (h3 : ∀ lit ∈ c, lit = unit ∨ assign.get? lit.1 = some !lit.2) :
    a unit.1 = unit.2 := by
  rw [CNF.Clause.sat_iff_exists_mem_eq] at h2
  rcases h2 with ⟨lit, hlit1, hlit2⟩
  specialize h3 lit hlit1
  rcases h3 with h3 | h3
  · simpa [h3] using hlit2
  · rw [sat_toCNF_iff] at h1
    specialize h1 lit.1 (!lit.2) h3
    simp [h1] at hlit2

theorem toCNF_add_entails_toCNF_insert {assignment : Assignment} :
    CNF.Entails (assignment.toCNF.add (.unit atom pol)) (assignment.insert atom pol).toCNF := by
  rw [CNF.entails_def]
  simp only [CNF.sat_add, CNF.Clause.sat_unit_iff, sat_toCNF_iff, and_imp]
  intro a ha h1 atom' pol' h2
  by_cases h3 : atom = atom'
  · specialize h1 atom pol
    simp_all
  · simp [get?_insert_of_ne h3] at h2
    exact h1 atom' pol' h2

def ofClause (clause : CNF.Clause Nat) : Option Assignment := Id.run do
  let mut assign := .empty
  for lit in clause do
    if let some value := assign.get? lit.1 then
      if value == lit.2 then
        return none
    else
      assign := assign.insert lit.1 !lit.2
  return some assign

set_option mvcgen.warning false in
theorem ofClause_spec (clause : CNF.Clause Nat) :
    match ofClause clause with
    | none => ∃ atom pol, (atom, pol) ∈ clause ∧ (atom, !pol) ∈ clause
    | some assignment => ∀ lit, lit ∈ clause ↔ assignment.get? lit.1 = some !lit.2 := by
  generalize h : ofClause clause = x
  unfold ofClause at h
  apply Id.of_wp_run_eq h
  clear h
  mvcgen invariants
  · Invariant.withEarlyReturnNewDo
      (onReturn := fun ret assignment => ⌜ret = none ∧ ∃ atom pol, (atom, pol) ∈ clause ∧ (atom, !pol) ∈ clause⌝)
      (onContinue := fun xs assignment => ⌜(∀ lit, lit ∈ xs.prefix ↔ assignment.get? lit.1 = some !lit.2)⌝)
  all_goals mleave
  · next pref lit suff hfor state assignment value hvalue heq ih =>
    simp only [beq_iff_eq, Prod.forall, reduceCtorEq, false_and, and_false, exists_const, or_false,
      Option.some.injEq, true_and, exists_eq_left', false_or] at ⊢ ih hvalue heq
    exists lit.fst, lit.snd
    replace ih := ih.right lit.fst !lit.snd
    simp only [heq, assignment] at hvalue
    simp only [hvalue, Bool.not_not, iff_true] at ih
    simp [← CNF.Clause.mem_literals_iff, hfor, ih]
  · next pref lit suff hfor state assignment value hvalue heq ih =>
    simp only [Prod.forall, reduceCtorEq, false_and, and_false, exists_const, or_false,
      List.mem_append, List.mem_cons, List.not_mem_nil, true_and] at ⊢ ih
    intro atom pol
    have : (!lit.snd) = value := by
      cases value <;> simpa using heq
    subst this
    have ih1 := (ih.right lit.fst lit.snd).mpr hvalue
    have ih2 := ih.right atom pol
    rw [← ih2]
    simp +contextual [ih1]
  · next pref lit suff hfor state assignment value hvalue1 hvalue2 ih =>
    simp only [imp_false, Prod.forall, reduceCtorEq, false_and, and_false, exists_const, or_false,
      List.mem_append, List.mem_cons, List.not_mem_nil, true_and] at *
    intro atom pol
    rcases lit with ⟨atom', pol'⟩
    have hvalue : state.snd.get? atom' = none := by
      cases value
      · exact hvalue2
      · simp at hvalue1
    by_cases heq : atom = atom'
    · simp [heq, eq_comm (a := pol') (b := pol), ih.right, hvalue]
    · simp [heq, Ne.symm heq, ih.right, assignment]
  · simp
  · simp_all
  · next state hstate ih =>
    simp only [hstate, CNF.Clause.mem_literals_iff, Prod.forall, true_and, reduceCtorEq, false_and,
      exists_const, or_false] at ih
    simp [- Bool.forall_bool, ih]

theorem exists_lit_of_ofClause_eq_none (h : ofClause clause = none) :
    ∃ atom pol, (atom, pol) ∈ clause ∧ (atom, !pol) ∈ clause := by
  have := ofClause_spec clause
  simpa [h] using this

theorem sat_of_ofClause_eq_none (h : ofClause clause = none) :
    ∀ a, clause.Sat a := by
  rcases exists_lit_of_ofClause_eq_none h with ⟨atom, pol, h1, h2⟩
  exact CNF.Clause.sat_of_mem_of_mem_neg h1 h2

theorem get_eq_of_ofClause_eq_some (h : ofClause clause = some assignment) :
    ∀ lit, lit ∈ clause ↔ assignment.get? lit.1 = some !lit.2 := by
  have := ofClause_spec clause
  simpa [h] using this

theorem sat_toCNF_iff_not_sat_of_ofClause_eq_some (h1 : ofClause clause = some assignment) :
    ∀ a, assignment.toCNF.Sat a ↔ ¬clause.Sat a := by
  intro a
  have h2 := get_eq_of_ofClause_eq_some h1
  rw [sat_toCNF_iff]
  rw [CNF.Clause.not_sat_iff_forall_mem_ne]
  constructor
  · intro h3 lit hlit
    specialize h2 lit
    specialize h3 lit.fst !lit.snd
    simp_all
  · intro h3 atom pol h4
    specialize h2 (atom, !pol)
    specialize h3 (atom, !pol)
    simp_all

-- This is the AT property
theorem entails_clause_of_unsat_of_ofClause_eq_some (h1 : ofClause clause = some assignment)
    (h2 : CNF.Unsat (f ++ assignment.toCNF)) : CNF.EntailsClause f clause := by
  rw [CNF.entails_clause_def]
  rw [CNF.unsat_iff_not_sat] at h2
  intro a h3
  specialize h2 a
  rw [CNF.sat_append, sat_toCNF_iff_not_sat_of_ofClause_eq_some h1] at h2
  simpa [h3] using h2

end Assignment

end Std.Tactic.BVDecide.LRAT.NewInternal
