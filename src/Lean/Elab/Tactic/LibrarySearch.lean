/-
Copyright (c) 2021-2024 Gabriel Ebner and Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Joe Hendrix, Kim Morrison
-/
module

prelude
public import Lean.Meta.Tactic.LibrarySearch
public import Lean.Meta.Tactic.TryThis
public import Lean.Elab.Tactic.ElabTerm
public import Lean.Elab.Tactic.Config

public section

namespace Lean.Elab.LibrarySearch

open Lean Meta LibrarySearch
open Elab Tactic Term TryThis

declare_config_elab elabLibrarySearchConfig Parser.Tactic.LibrarySearchConfig

/--
Implementation of the `exact?` tactic.

* `ref` contains the input syntax and is used for locations in error reporting.
* `config` contains configuration options (e.g., `grind` for using grind as a discharger).
* `required` contains an optional list of terms that should be used in closing the goal.
* `requireClose` indicates if the goal must be closed.
  It is `true` for `exact?` and `false` for `apply?`.
-/
def exact? (ref : Syntax) (config : Parser.Tactic.LibrarySearchConfig)
    (required : Option (Array (TSyntax `term))) (requireClose : Bool) :
    TacticM Unit := do
  let mvar ← getMainGoal
  let initialState ← saveState
  let (_, goal) ← (← getMainGoal).intros
  goal.withContext do
    let required := (← (required.getD #[]).mapM getFVarId).toList.map .fvar
    let tactic := fun goals =>
      solveByElim required (exfalso := false) goals (maxDepth := 6) (grind := config.grind) (try? := config.try?)
    let allowFailure := fun g => do
      let g ← g.withContext (instantiateMVars (.mvar g))
      return required.all fun e => e.occurs g
    match (← librarySearch goal tactic allowFailure (includeStar := config.star)
        (collectAll := config.all)) with
    -- Found goal that closed problem (only when collectAll = false)
    | none =>
      addExactSuggestion ref (← instantiateMVars (mkMVar mvar)).headBeta (checkState? := initialState)
    -- Found suggestions (includes complete solutions when collectAll = true)
    | some suggestions =>
      -- Separate complete solutions (empty remaining goals) from incomplete ones
      let (complete, incomplete) := suggestions.partition (·.1.isEmpty)
      if requireClose && !config.all then
        let hint := if suggestions.isEmpty then "" else " Try `apply?` to see partial suggestions."
        throwError "`exact?` could not close the goal.{hint}"
      if requireClose && config.all && complete.isEmpty then
        let hint := if incomplete.isEmpty then "" else " Try `apply?` to see partial suggestions."
        throwError "`exact?` could not close the goal.{hint}"
      reportOutOfHeartbeats `apply? ref
      -- Collect complete solutions and show as a single "Try these:" message
      let completeExprs ← complete.mapM fun (_, suggestionMCtx) =>
        withMCtx suggestionMCtx do
          return (← instantiateMVars (mkMVar mvar)).headBeta
      if !completeExprs.isEmpty then
        addExactSuggestions ref completeExprs (checkState? := initialState)
      -- Show incomplete solutions only if not requireClose (i.e., for apply?)
      -- Note: we must call addExactSuggestion inside withMCtx because incomplete
      -- solutions have unassigned metavariables that are only valid in that context
      if !requireClose then
        for (_, suggestionMCtx) in incomplete do
          withMCtx suggestionMCtx do
            addExactSuggestion ref (← instantiateMVars (mkMVar mvar)).headBeta
              (checkState? := initialState) (addSubgoalsMsg := true) (tacticErrorAsInfo := true)
        if suggestions.isEmpty then logError "apply? didn't find any relevant lemmas"
      admitGoal goal (synthetic := false)

@[builtin_tactic Lean.Parser.Tactic.exact?]
def evalExact : Tactic := fun stx => do
  let `(tactic| exact? $cfg:optConfig $[using $[$required],*]?) := stx
        | throwUnsupportedSyntax
  let config ← elabLibrarySearchConfig cfg
  exact? (← getRef) config required true


@[builtin_tactic Lean.Parser.Tactic.apply?]
def evalApply : Tactic := fun stx => do
  let `(tactic| apply? $cfg:optConfig $[using $[$required],*]?) := stx
        | throwUnsupportedSyntax
  let config ← elabLibrarySearchConfig cfg
  exact? (← getRef) config required false

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
