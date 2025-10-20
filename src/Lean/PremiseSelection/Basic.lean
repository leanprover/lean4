/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

prelude
public import Lean.Elab.Command
public import Lean.Meta.Eval
public import Lean.Meta.CompletionName
public import Init.Data.Random

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

@[expose] public section

namespace Lean.PremiseSelection

/--
A `Suggestion` is essentially just an identifier and a confidence score that the identifier is relevant.
If the premise selection request included information about the intended use (e.g. in the simplifier, in `grind`, etc.)
the score may be adjusted for that application.

-/
structure Suggestion where
  name : Name
  /--
  The score of the suggestion, as a probability that this suggestion should be used.
  -/
  score : Float
  /--
  Optional flag associated with the suggestion, e.g. "←" or "=",
  if the premise selection algorithm is aware of the tactic consuming the results,
  and wants to suggest modifiers for this suggestion.
  E.g. this supports calling `simp` in the reverse direction,
  or telling `grind` or `aesop` to use the theorem in a particular way.
  -/
  flag : Option String := none

structure Config where
  /--
  The maximum number of suggestions to return.
  -/
  maxSuggestions : Nat := 100
  /--
  The tactic that is calling the premise selection, e.g. `simp`, `grind`, or `aesop`.
  This may be used to adjust the score of the suggestions
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
Construct a `Selector` (which acts on an `MVarId`)
from a function which takes the pretty printed goal.
-/
def ppSelector (selector : String → Config → MetaM (Array Suggestion)) (g : MVarId) (c : Config) :
    MetaM (Array Suggestion) := do
  selector (toString (← Meta.ppGoal g)) c

namespace Selector

/--
Respect the `Config.filter` option by implementing it as a post-filter.
If a premise selection implementation does not natively handle the filter,
it should be wrapped with this function.
-/
def postFilter (selector : Selector) : Selector := fun g c => do
  let suggestions ← selector g { c with filter := fun _ => pure true }
  suggestions.filterM (fun s => c.filter s.name)

/--
Wrapper for `Selector` that ensures
the `maxSuggestions` field in `Config` is respected, post-hoc.
-/
def maxSuggestions (selector : Selector) : Selector := fun g c => do
  let suggestions ← selector g c
  return suggestions.take c.maxSuggestions

/-- Combine two premise selectors, returning the best suggestions. -/
def combine (selector₁ : Selector) (selector₂ : Selector) : Selector := fun g c => do
  let suggestions₁ ← selector₁ g c
  let suggestions₂ ← selector₂ g c

  let mut dedupMap : Std.HashMap (Name × Option String) Suggestion := {}

  for s in suggestions₁ ++ suggestions₂ do
    let key := (s.name, s.flag)
    dedupMap := dedupMap.alter key fun
    | none => some s
    | some s' => if s.score > s'.score then some s else some s'

  let deduped := dedupMap.valuesArray
  let sorted := deduped.qsort (fun s₁ s₂ => s₁.score > s₂.score)

  return sorted.take c.maxSuggestions

end Selector

section DenyList

/-- Premises from a module whose name has one of the following components are not retrieved. -/
builtin_initialize moduleDenyListExt : SimplePersistentEnvExtension String (List String) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := (·.cons)
    addImportedFn := mkStateFromImportedEntries (·.cons) []
  }

/-- A premise whose name has one of the following components is not retrieved. -/
builtin_initialize nameDenyListExt : SimplePersistentEnvExtension String (List String) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := (·.cons)
    addImportedFn := mkStateFromImportedEntries (·.cons) []
  }

/-- A premise whose `type.getForallBody.getAppFn` is a constant that has one of these prefixes is not retrieved. -/
builtin_initialize typePrefixDenyListExt : SimplePersistentEnvExtension Name (List Name) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := (·.cons)
    addImportedFn := mkStateFromImportedEntries (·.cons) []
  }

def isDeniedModule (env : Environment) (moduleName : Name) : Bool :=
  (moduleDenyListExt.getState env).any fun p => moduleName.anyS (· == p)

def isDeniedPremise (env : Environment) (name : Name) : Bool := Id.run do
  if name == ``sorryAx then return true
  if name.isInternalDetail then return true
  if (nameDenyListExt.getState env).any (fun p => name.anyS (· == p)) then return true
  if let some moduleIdx := env.getModuleIdxFor? name then
    let moduleName := env.header.moduleNames[moduleIdx.toNat]!
    if isDeniedModule env moduleName then
      return true
  let some ci := env.find? name | return true
  if let .const fnName _ := ci.type.getForallBody.getAppFn then
    if (typePrefixDenyListExt.getState env).any (fun p => p.isPrefixOf fnName) then return true
  return false

end DenyList

/--
The trivial premise selector, which returns no suggestions.
-/
def empty : Selector := fun _ _ => pure #[]

/-- A random premise selection algorithm, provided solely for testing purposes. -/
def random (gen : StdGen := ⟨37, 59⟩) : Selector := fun _ cfg => do
  IO.stdGenRef.set gen
  let env ← getEnv
  let max := cfg.maxSuggestions
  let consts := env.const2ModIdx.keysArray
  let mut suggestions := #[]
  while suggestions.size < max do
    let i ← IO.rand 0 consts.size
    let name := consts[i]!
    unless isDeniedPremise env name do
      suggestions := suggestions.push { name := name, score := 1.0 / consts.size.toFloat }
  return suggestions

builtin_initialize premiseSelectorExt : EnvExtension (Option Selector) ←
  registerEnvExtension (pure none)

/-- Generate premise suggestions for the given metavariable, using the currently registered premise selector. -/
def select (m : MVarId) (c : Config := {}) : MetaM (Array Suggestion) := do
  let some selector := premiseSelectorExt.getState (← getEnv) |
    throwError "No premise selector registered. \
      (Note the Lean does not provide a default premise selector, these must be installed by a downstream library.)"
  selector m c

/-!
Currently the registration mechanism is just global state.
This means that if multiple modules register premise selectors,
the behaviour will be dependent on the order of loading modules.

We should replace this with a mechanism so that
premise selectors are configured via options in the `lakefile`, and
commands are only used to override in a single declaration or file.
-/

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
