/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Lean.Elab.Tactic.Grind
import Lean.LibrarySuggestions.Basic

/-!
# Tests for grind_annotated command

This file tests that:
1. The `grind_annotated` command correctly validates date formats
2. The `filterGrindAnnotated` wrapper correctly filters suggestions based on the caller
-/

open Lean Meta Elab Tactic LibrarySuggestions

/-! ## Date format validation -/

/--
error: Invalid date format: offset 0: condition not satisfied
Expected format: YYYY-MM-DD (e.g., "2025-01-15")
-/
#guard_msgs in
grind_annotated "invalid-date"

/-- info: Init.Data.List.Lemmas is grind-annotated: true -/
#guard_msgs in
#eval do
  let env ← getEnv
  -- Use the public API to check if a module is grind-annotated
  -- First we need to get the module index for a theorem from Init.Data.List.Lemmas
  match env.getModuleIdxFor? `List.eq_nil_of_length_eq_zero with
  | none => logInfo "Could not find module"
  | some modIdx =>
    let isAnnotated := Lean.Elab.Tactic.Grind.isGrindAnnotatedModule env modIdx
    logInfo m!"Init.Data.List.Lemmas is grind-annotated: {isAnnotated}"

/-! ## Filtering logic -/

/--
Create a hardcoded selector that returns a suggestion from `List.eq_nil_of_length_eq_zero`
in the grind-annotated Init.Data.List.Lemmas module.
-/
def testSelector : Selector := fun _ _ => do
  return #[{
    name := `List.eq_nil_of_length_eq_zero
    score := 1.0
    flag := none
  }]

/-- info: All tests passed! -/
#guard_msgs in
example : True := by
  run_tac do
    let mvarId ← getMainGoal
    let env ← getEnv

    -- Debug: Check if List.eq_nil_of_length_eq_zero exists and get its module
    let theoremName := `List.eq_nil_of_length_eq_zero

    match env.getModuleIdxFor? theoremName with
    | none => logInfo "Theorem has no module index"
    | some modIdx =>
      let _moduleName := env.header.moduleNames[modIdx.toNat]!
      let _isAnnotated := Grind.isGrindAnnotatedModule env modIdx
      pure ()

    -- Test 1: Without filter, suggestion should be returned
    let suggestions1 ← testSelector mvarId {}
    unless suggestions1.size == 1 do
      throwError "Test 1 failed: Expected 1 suggestion without filter, got {suggestions1.size}"

    -- Test 2: With filterGrindAnnotated and caller := "grind", suggestion should be filtered out
    let filteredSelector := testSelector.filterGrindAnnotated
    let suggestions2 ← filteredSelector mvarId { caller := some "grind" }
    unless suggestions2.size == 0 do
      throwError "Test 2 failed: Expected 0 suggestions with grind caller, got {suggestions2.size}"

    -- Test 3: With filterGrindAnnotated and caller := "simp", suggestion should be returned
    let suggestions3 ← filteredSelector mvarId { caller := some "simp" }
    unless suggestions3.size == 1 do
      throwError "Test 3 failed: Expected 1 suggestion with simp caller, got {suggestions3.size}"

    -- Test 4: With filterGrindAnnotated and no caller, suggestion should be returned
    let suggestions4 ← filteredSelector mvarId { caller := none }
    unless suggestions4.size == 1 do
      throwError "Test 4 failed: Expected 1 suggestion with no caller, got {suggestions4.size}"

    logInfo "All tests passed!"
  trivial
