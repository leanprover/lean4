/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
prelude
import Lean.Elab.Command
import Lean.Meta.Eval
import Init.Data.Random

/-!
# An API for premise selection algorithms.

This module provides a basic API for premise selection algorithms,
which are used to suggest identifiers that should be introduced in a proof.

The core interface is the `Selector` type, which is a function from a metavariable
and a configuration to a list of suggestions.

The `Selector` is registered as an environment extension, and the trivial (no suggestions) implementation
is `Lean.PremiseSelection.empty`.

Lean does not provide a default premise selector, so this module is intended to be used in conjunction
with a downstream package which registers a premise selector.
-/

namespace Lean.PremiseSelection

/--
A `Suggestion` is essentially just an identifier and a confidence score that the identifier is relevant.
If the premise selection request included information about the intended use (e.g. in the simplifier, in `grind`, etc.)
the score may be adjusted for that application.

A `Suggestion` may optionally include suggested syntactical modifiers for particular tactics,
e.g. indicating that if the identifier is used in `simp` it should be used with the `↓`, `↑`, or `←` modifiers,
or that if the identifier is used in `grind` it should be used with a particular pattern modifier.
To keep this extensible, these suggestions are represented as a `NameMap Syntax`,
where the key is the name of the tactic and the value is the suggested syntax decorating the identifier.
-/
structure Suggestion where
  name : Name
  /--
  The score of the suggestion, lower is better.
  Recommended to use the estimated negative log₂-likelihood that this suggestion is optimal.
  -/
  score : Nat
  /--
  Optional, suggested syntactical modifiers for particular tactics.
  e.g.
  ```
  (∅ : NameMap Syntax)
    |>.insert `grind (← `(grindMod| ←=))
    |>.insert `simp (← `(simpPre| ↓))
  ```
  -/
  tacticModifiers : NameMap Syntax := {}

structure Config where
  /--
  The maximum number of suggestions to return.
  -/
  maxSuggestions : Option Nat := none
  /--
  The tactic that is calling the premise selection, e.g. `simp`, `grind`, or `aesop`.
  This may be used to adjust the score of the suggestions,
  as well as to provide syntactical modifiers specific to the caller.
  -/
  caller : Option Name := none
  /--
  A filter on suggestions; only suggestions returning `true` should be returned.
  (It can be better to filter on the premise selection side, to ensure that enough suggestions are returned.)
  -/
  filter : Name → MetaM Bool := fun _ => pure true
  /--
  An optional arbitrary "hint" to the premise selection algorithm.
  There is no guarantee that the algorithm will make any use of the hint.

  Potential use cases include a natural language comment provided by the user
  (e.g. allowing use of the premise selector as a search engine)
  or including context from the current proof and/or file.

  We may later split these use cases into separate fields if necessary.
  -/
  hint : Option String := none

abbrev Selector : Type := MVarId → Config → MetaM (Array Suggestion)

/--
The trivial premise selector, which returns no suggestions.
-/
def empty : Selector := fun _ _ => pure #[]

/-- A random premise selection algorithm, provided solely for testing purposes. -/
def random (gen : StdGen := ⟨37, 59⟩) : Selector := fun _ cfg => do
  IO.stdGenRef.set gen
  let env := (← getEnv).checkedWithoutAsync
  let max := cfg.maxSuggestions.getD 10
  let n := env.const2ModIdx.size
  let mut suggestions := #[]
  for (c, _) in env.const2ModIdx do
    if suggestions.size ≥ max then
      break
    if (← IO.rand 0 (2*max)) = 0 then
      suggestions := suggestions.push { name := c, score := Nat.log2 n }
  return suggestions

initialize premiseSelectorExt : EnvExtension (Option Selector) ←
  registerEnvExtension (pure none)

/-- Generate premise suggestions for the given metavariable, using the currently registered premise selector. -/
def select (m : MVarId) (c : Config := {}) : MetaM (Array Suggestion) := do
  let some selector := premiseSelectorExt.getState (← getEnv) |
    throwError "No premise selector registered. \
      (Note the Lean does not provide a default premise selector, these must be installed by a downstream library.)"
  selector m c

/-- Set the current premise selector.-/
def registerPremiseSelector (selector : Selector) : CoreM Unit := do
  modifyEnv fun env => premiseSelectorExt.setState env (some selector)

open Lean Elab Command in
@[builtin_command_elab setPremiseSelectorCmd, inherit_doc setPremiseSelectorCmd]
def elabSetPremiseSelector : CommandElab
  | `(command| set_premise_selector $selector) => do
    let selector ← liftTermElabM do
      try
        let selectorTerm ← Term.elabTermEnsuringType selector (some (Expr.const ``Selector []))
        unsafe Meta.evalExpr Selector (Expr.const ``Selector []) selectorTerm
      catch _ =>
        throwError "Failed to elaborate {selector} as a `MVarId → Config → MetaM (Array Suggestion)`."
    liftCoreM (registerPremiseSelector selector)
  | _ => throwUnsupportedSyntax

open Lean.Elab.Tactic in
@[builtin_tactic Lean.Parser.Tactic.suggestPremises] def evalSuggestPremises : Tactic := fun _ =>
  liftMetaTactic1 fun mvarId => do
    let suggestions ← select mvarId
    logInfo m!"Premise suggestions: {suggestions.map (·.name)}"
    return mvarId

end Lean.PremiseSelection
