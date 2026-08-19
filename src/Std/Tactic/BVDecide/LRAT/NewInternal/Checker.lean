/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
import Std.Tactic.BVDecide.LRAT.NewInternal.Add
import Std.Tactic.BVDecide.LRAT.NewInternal.Delete
import Std.Tactic.BVDecide.LRAT.NewInternal.Rup
import Std.Tactic.BVDecide.LRAT.NewInternal.Empty
public import Std.Tactic.BVDecide.LRAT.Actions
import Init.Omega

namespace Std.Tactic.BVDecide.LRAT.NewInternal

open Std.Sat

public def check (formula : CNF Nat) (proof : Array IntAction) : Bool :=
  let state := .ofCNF formula
  go state proof 0
where
  go (state : State) (proof : Array IntAction) (idx : Nat) : Bool :=
    if h : idx < proof.size then
      let step := proof[idx]
      match step with
      | .addEmpty id rupHints => state.checkEmpty rupHints
      | .addRup id clause rupHints =>
        let clause := convertClause clause
        if state.checkRup clause rupHints then
          go (state.add clause) proof (idx + 1)
        else
          false
      | .addRat .. => false -- TODO
      | .del ids => go (state.deleteMany ids) proof (idx + 1)
    else
      false

  convertClause (clause : Array Int) : CNF.Clause Nat :=
    ⟨clause.toList.filterMap fun int =>
      if int > 0 then
        some (int.natAbs - 1, true)
      else if int < 0 then
        some (int.natAbs - 1, false)
      else
        none
    ⟩

theorem unsat_of_go {state : State} {proof : Array IntAction} {idx : Nat}
    (h : check.go state proof idx) : CNF.Unsat state.toCNF := by
  fun_induction check.go state proof idx
  case case1 =>
    apply CNF.unsat_of_entails_clause_unsat (c := .empty) (h1 := by simp)
    apply State.entails_clause_empty_of_checkEmpty
    exact h
  case case2 h2 ih =>
    specialize ih h
    apply CNF.unsat_of_entails_unsat (h1 := ih)
    apply State.entails_add_of_entails_clause
    apply State.entails_clause_of_checkRup
    exact h2
  case case3 => contradiction
  case case4 => contradiction
  case case5 ih =>
    specialize ih h
    apply CNF.unsat_of_entails_unsat (h1 := ih)
    apply State.entails_deleteMany
  case case6 => contradiction

public theorem unsat_of_check {formula : CNF Nat} {proof : Array IntAction}
    (h : check formula proof) : CNF.Unsat formula := by
  simp only [check] at h
  replace h := unsat_of_go h
  simpa using h

end Std.Tactic.BVDecide.LRAT.NewInternal
