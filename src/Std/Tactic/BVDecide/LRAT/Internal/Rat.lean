/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Std.Tactic.BVDecide.LRAT.Internal.Rup
public import Std.Tactic.BVDecide.LRAT.Internal.Add
import Std.Tactic.Do
import Std.Data.HashSet

namespace Std.Tactic.BVDecide.LRAT.Internal

set_option mvcgen.warning false

open Std.Sat Std.Do

namespace State

def checkRatHintsExhaustive (s : State) (ratHints : Array (Nat × Array Nat))
    (negPivot : Literal Nat) : Bool :=
  let set : Std.HashSet Nat := .ofArray <| ratHints.map (·.1)
  s.all fun idx c => ¬negPivot ∈ c ∨ set.contains idx

public def checkRat (s : State) (clause : CNF.Clause Nat) (pivot : Literal Nat)
    (rupHints : Array Nat) (ratHints : Array (Nat × Array Nat)) : Bool := Id.run do
  if pivot ∉ clause then
    return false
  let some assign := Assignment.ofClause clause | return true
  match s.propagateHints assign rupHints with
  | .conflict => return true
  | .error => return false
  | .extended assign =>
    let negPivot := pivot.negate
    if !s.checkRatHintsExhaustive ratHints negPivot then
      return false
    return ratHints.all fun (idx, hints) =>
      match s.get? idx with
      | some clause =>
        /-
        This is a non-linear use of `assign`, in practice RAT clauses are currently rare and for large
        formulas should be dominated by repeatedly iterating the entire formula instead of this copy
        anyway. If we should realize this is an issue at some point we can start introducing
        backtracking `Assignment` approaches.
        -/
        match assign.extendOfClauseWithout clause negPivot with
        | some assign => s.checkPropagate assign hints
        | none => true
      | none => false

theorem checkRatHintsExhaustive_spec {s : State} {ratHints : Array (Nat × Array Nat)}
    {negPivot : Literal Nat} (h : checkRatHintsExhaustive s ratHints negPivot = true) :
    ∀ c ∈ s.toCNF, negPivot ∈ c → ∃ idx hints, s.get? idx = some c ∧ (idx, hints) ∈ ratHints := by
  intro c hc hmem
  simp only [checkRatHintsExhaustive, HashSet.ofArray_eq_ofList, Array.toList_map,
    HashSet.contains_ofList, List.contains_eq_mem, List.mem_map, Array.mem_toList_iff, Prod.exists,
    exists_and_right, exists_eq_right, decide_eq_true_eq, Bool.decide_or, decide_not,
    Bool.decide_eq_true] at h
  rcases forall_of_all_eq_true h c hc with ⟨idx, hidx1, hidx2⟩
  simp only [List.mem_map, Array.mem_toList_iff, Prod.exists, exists_and_right, exists_eq_right,
    Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not,
    decide_eq_true_eq] at hidx2
  rcases hidx2 with hidx2 | hidx2
  · contradiction
  · rcases hidx2 with ⟨hints, hmem⟩
    exists idx, hints

set_option linter.deprecated.syntax false in
theorem checkRat_spec {s : State} {clause : CNF.Clause Nat} {pivot : Literal Nat}
    {rupHints : Array Nat} {ratHints : Array (Nat × Array Nat)} :
    checkRat s clause pivot rupHints ratHints = true
      → pivot ∈ clause
        ∧ ∀ clause' ∈ s.toCNF,
          pivot.negate ∈ clause'
            → s.toCNF.EntailsClause (clause ++ (clause'.erase pivot.negate)) := by
  generalize h : checkRat s clause pivot rupHints ratHints = x
  unfold checkRat at h
  apply Id.of_wp_run_eq h
  clear h
  mvcgen
  all_goals mleave
  · simp
  · constructor
    · simp_all
    · intros
      apply CNF.entails_clause_append_left
      apply Assignment.entails_clause_of_unsat_of_ofClause_eq_some
      · assumption
      · apply unsat_of_propagateHints_eq_conflict
        assumption
  · simp
  · simp
  · next hmemp assign hassign newAssign hprop negPivot hex =>
    intro hloop
    constructor
    · simp_all
    · intro c' hmem hpmem
      rw [Array.all_eq_true'] at hloop
      rcases checkRatHintsExhaustive_spec (by simpa using hex) c' hmem hpmem with ⟨idx, hints, hidx1, hidx2⟩
      specialize hloop (idx, hints) hidx2
      simp only [hidx1] at hloop
      split at hloop
      · next finalAssign heq =>
        apply CNF.entails_clause_of_unsat_of_isNegationOf (f1 := (clause ++ c'.erase pivot.negate).negate)
        · apply CNF.isNegationOf_negate
        · rw [CNF.unsat_iff_not_sat]
          intro a
          rw [CNF.sat_append, CNF.Clause.negate_append, CNF.sat_append]
          rintro ⟨hsat1, hsat2, hsat3⟩
          have hsat4 : assign.toCNF.Sat a := by
            rw [CNF.Clause.sat_negate_iff_sat_of_isNegationOf assign.toCNF] at hsat2
            · assumption
            · exact Assignment.isNegationOf_of_ofClause_eq_some hassign
          have hsat5 : newAssign.toCNF.Sat a := by
            have := entails_of_propagateHints_eq_extended hprop
            rw [CNF.entails_def] at this
            apply this
            simp [hsat1, hsat4]
          have hsat6 : ∀ lit ∈ c'.erase pivot.negate, a lit.1 = !lit.2 := by
            apply CNF.forall_mem_eq_not_of_isNegationOf_of_sat
            · exact CNF.isNegationOf_negate _
            · exact hsat3
          have hsat7 : finalAssign.toCNF.Sat a := by
            rw [Assignment.sat_toCNF_iff]
            intro atom pol hatom
            have := (Assignment.mem_or_get?_eq_iff_of_extendOfClauseWithout_eq_some heq (atom, !pol))
            simp only [ne_eq, Bool.not_not, hatom, iff_true] at this
            rcases this with ⟨ht1, ht2⟩ | ht
            · specialize hsat6 (atom, !pol)
              rw [Bool.not_not] at hsat6
              apply hsat6
              rw [eq_comm] at ht2
              simp +zetaDelta [ht1, ht2]
            · rw [Assignment.sat_toCNF_iff] at hsat5
              apply hsat5
              exact ht
          have hsat8 : (s.toCNF ++ finalAssign.toCNF).Unsat := unsat_of_checkPropagate hloop
          rw [CNF.unsat_iff_not_sat] at hsat8
          specialize hsat8 a
          apply hsat8
          simp [hsat1, hsat7]
      · next heq =>
        have hspec1 := Assignment.entails_clause_of_extendOfClauseWithout_eq_none heq
        have hspec2 := entails_of_propagateHints_eq_extended hprop
        rw [CNF.entails_clause_append_iff]
        intro a hsat1
        by_cases hsat2 : assign.toCNF.Sat a
        · right
          rw [CNF.entails_clause_def] at hspec1
          specialize hspec1 a
          rw [CNF.entails_def] at hspec2
          specialize hspec2 a
          apply hspec1
          apply hspec2
          simp [hsat1, hsat2]
        · left
          have hspec1 := Assignment.isNegationOf_of_ofClause_eq_some hassign
          rw [CNF.isNegationOf_def] at hspec1
          simpa [hspec1] using hsat2
  · constructor
    · simp_all
    · intros
      apply CNF.entails_clause_append_left
      apply CNF.entails_clause_of_forall_sat
      apply Assignment.sat_of_ofClause_eq_none
      rw [Option.eq_none_iff_forall_ne_some]
      simp_all

public theorem unsat_of_unsat_of_checkRat {s : State} {clause : CNF.Clause Nat}
    {pivot : Literal Nat} {rupHints : Array Nat} {ratHints : Array (Nat × Array Nat)}
    (h1 : checkRat s clause pivot rupHints ratHints = true) (h2 : s.toCNF.Sat a) :
    ∃ a', (s.add clause).toCNF.Sat a' := by
  have hspec := checkRat_spec h1
  rcases CNF.exists_sat_add_of_rat hspec.1 hspec.2 a h2 with ⟨a', ha'⟩
  exists a'
  simp [ha']

end State

end Std.Tactic.BVDecide.LRAT.Internal
