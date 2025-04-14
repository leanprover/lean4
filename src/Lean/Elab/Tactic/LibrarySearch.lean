/-
Copyright (c) 2021-2024 Gabriel Ebner and Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Joe Hendrix, Kim Morrison
-/
prelude
import Lean.Meta.Tactic.LibrarySearch
import Lean.Meta.Tactic.TryThis
import Lean.Elab.Tactic.ElabTerm

namespace Lean.Elab.LibrarySearch

open Lean Meta LibrarySearch
open Elab Tactic Term TryThis

/--
Implementation of the `exact?` tactic.

* `ref` contains the input syntax and is used for locations in error reporting.
* `required` contains an optional list of terms that should be used in closing the goal.
* `requireClose` indicates if the goal must be closed.
  It is `true` for `exact?` and `false` for `apply?`.
-/
def exact? (ref : Syntax) (required : Option (Array (TSyntax `term))) (requireClose : Bool) :
    TacticM Unit := do
  let mvar ← getMainGoal
  let initialState ← saveState
  let (_, goal) ← (← getMainGoal).intros
  goal.withContext do
    let required := (← (required.getD #[]).mapM getFVarId).toList.map .fvar
    let tactic := fun exfalso =>
      solveByElim required (exfalso := exfalso) (maxDepth := 6)
    let allowFailure := fun g => do
      let g ← g.withContext (instantiateMVars (.mvar g))
      return required.all fun e => e.occurs g
    match (← librarySearch goal tactic allowFailure) with
    -- Found goal that closed problem
    | none =>
      addExactSuggestion ref (← instantiateMVars (mkMVar mvar)).headBeta (checkState? := initialState)
    -- Found suggestions
    | some suggestions =>
      if requireClose then
        let hint := if suggestions.isEmpty then "" else " Try `apply?` to see partial suggestions."
        throwError "`exact?` could not close the goal.{hint}"
      reportOutOfHeartbeats `apply? ref
      for (_, suggestionMCtx) in suggestions do
        withMCtx suggestionMCtx do
          addExactSuggestion ref (← instantiateMVars (mkMVar mvar)).headBeta
            (checkState? := initialState) (addSubgoalsMsg := true) (tacticErrorAsInfo := true)
      if suggestions.isEmpty then logError "apply? didn't find any relevant lemmas"
      admitGoal goal

@[builtin_tactic Lean.Parser.Tactic.exact?]
def evalExact : Tactic := fun stx => do
  let `(tactic| exact? $[using $[$required],*]?) := stx
        | throwUnsupportedSyntax
  exact? (← getRef) required true


@[builtin_tactic Lean.Parser.Tactic.apply?]
def evalApply : Tactic := fun stx => do
  let `(tactic| apply? $[using $[$required],*]?) := stx
        | throwUnsupportedSyntax
  exact? (← getRef) required false

@[builtin_term_elab Lean.Parser.Syntax.exact?]
def elabExact?Term : TermElab := fun stx expectedType? => do
  let `(exact?%) := stx | throwUnsupportedSyntax
  withExpectedType expectedType? fun expectedType => do
    let goal ← mkFreshExprMVar expectedType
    let (_, introdGoal) ← goal.mvarId!.intros
    introdGoal.withContext do
      if let some suggestions ← librarySearch introdGoal then
        if suggestions.isEmpty then logError "`exact?%` didn't find any relevant lemmas"
        else logError "`exact?%` could not close the goal. Try `by apply?` to see partial suggestions."
        mkLabeledSorry expectedType (synthetic := true) (unique := true)
      else
        addTermSuggestion stx (← instantiateMVars goal).headBeta
        instantiateMVars goal

end Lean.Elab.LibrarySearch
