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
public import Lean.Linter.Deprecated
public import Init.Data.Random
public import Lean.Elab.Tactic.Grind.Annotated

/-!
# An API for library suggestion algorithms.

This module provides a basic API for library suggestion algorithms,
which are used to suggest relevant theorems from the library for the current goal.
In the literature this is usually known as "premise selection",
but we mostly avoid that term as most of our users will not be familiar with the term.

The core interface is the `Selector` type, which is a function from a metavariable
and a configuration to a list of suggestions.
The `Selector` is registered as an environment extension,
and the trivial (no suggestions) implementation is `Lean.LibrarySuggestions.empty`.

Lean does not provide a default library suggestion engine, so this module is intended to be used in conjunction
with a downstream package which registers a library suggestion engine.
-/

namespace Lean.Expr.FoldRelevantConstantsImpl

open Lean Meta

unsafe structure State where
 visited       : PtrSet Expr := mkPtrSet
 visitedConsts : NameHashSet := {}

unsafe abbrev FoldM := StateT State MetaM

unsafe def fold {α : Type} (f : Name → α → MetaM α) (e : Expr) (acc : α) : FoldM α :=
  let rec visit (e : Expr) (acc : α) : FoldM α := do
    if (← get).visited.contains e then
      return acc
    modify fun s => { s with visited := s.visited.insert e }
    if ← isProof e then
      -- Don't visit proofs.
      return acc
    match e with
    | .forallE n d b bi  =>
      let r ← visit d acc
      withLocalDecl n bi d fun x =>
        visit (b.instantiate1 x) r
    | .lam n d b bi      =>
      let r ← visit d acc
      withLocalDecl n bi d fun x =>
        visit (b.instantiate1 x) r
    | .mdata _ b         => visit b acc
    | .letE n t v b nondep    =>
      let r₁ ← visit t acc
      let r₂ ← visit v r₁
      withLetDecl n t v (nondep := nondep) fun x =>
        visit (b.instantiate1 x) r₂
    | .app f a           =>
      let fi ← getFunInfo f (some 1)
      if fi.paramInfo[0]!.isInstImplicit then
        -- Don't visit implicit arguments.
        visit f acc
      else
        visit a (← visit f acc)
    | .proj _ _ b        => visit b acc
    | .const c _         =>
      if (← get).visitedConsts.contains c then
        return acc
      else
        modify fun s => { s with visitedConsts := s.visitedConsts.insert c }
        if ← isInstance c then
          return acc
        else
          f c acc
    | _ => return acc
  visit e acc

@[inline] unsafe def foldUnsafe {α : Type} (e : Expr) (init : α) (f : Name → α → MetaM α) : MetaM α :=
  (fold f e init).run' {}

end FoldRelevantConstantsImpl

/-- Apply `f` to every constant occurring in `e` once, skipping instance arguments and proofs. -/
@[implemented_by FoldRelevantConstantsImpl.foldUnsafe]
public opaque foldRelevantConstants {α : Type} (e : Expr) (init : α) (f : Name → α → MetaM α) : MetaM α := pure init

/-- Collect the constants occuring in `e` (once each), skipping instance arguments and proofs. -/
public def relevantConstants (e : Expr) : MetaM (Array Name) := foldRelevantConstants e #[] (fun n ns => return ns.push n)

/-- Collect the constants occuring in `e` (once each), skipping instance arguments and proofs. -/
public def relevantConstantsAsSet (e : Expr) : MetaM NameSet := foldRelevantConstants e ∅ (fun n ns => return ns.insert n)

end Lean.Expr

open Lean Meta MVarId in
public def Lean.MVarId.getConstants (g : MVarId) : MetaM NameSet := withContext g do
  let mut c := (← g.getType).getUsedConstantsAsSet
  for t in (← getLocalHyps) do
    c := c ∪ (← inferType t).getUsedConstantsAsSet
  return c

open Lean Meta MVarId in
public def Lean.MVarId.getRelevantConstants (g : MVarId) : MetaM NameSet := withContext g do
  let mut c ← (← g.getType).relevantConstantsAsSet
  for t in (← getLocalHyps) do
    c := c ∪ (← (← inferType t).relevantConstantsAsSet)
  return c

@[expose] public section

namespace Lean.LibrarySuggestions

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
  caller : Option String := none
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
def combine (selector₁ selector₂ : Selector) : Selector := fun g c => do
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

/--
Filter out theorems from grind-annotated modules when the caller is "grind".
Modules marked with `grind_annotated` contain manually reviewed/annotated theorems,
so they should be excluded from automatic premise selection for grind.
Other callers (like "simp") still receive suggestions from these modules.
-/
def filterGrindAnnotated (selector : Selector) : Selector := fun g c => do
  let suggestions ← selector g c
  -- Only filter when caller is "grind"
  if c.caller == some "grind" then
    let env ← getEnv
    suggestions.filterM fun s => do
      -- Check if the suggestion's module is grind-annotated
      match env.getModuleIdxFor? s.name with
      | none => return true  -- Keep suggestions with no module info
      | some modIdx => return !Lean.Elab.Tactic.Grind.isGrindAnnotatedModule env modIdx
  else
    return suggestions

/--
Combine two premise selectors by interspersing their results (ignoring scores).
The parameter `ratio` (defaulting to 0.5) controls the ratio of suggestions from each selector
while results are available from both.
-/
def intersperse (selector₁ selector₂ : Selector) (ratio : Float := 0.5) : Selector := fun g c => do
  -- Calculate how many suggestions to request from each selector based on the ratio
  let max₁ := (c.maxSuggestions.toFloat * ratio).toUInt32.toNat
  let max₂ := (c.maxSuggestions.toFloat * (1 - ratio)).toUInt32.toNat

  let suggestions₁ ← selector₁ g { c with maxSuggestions := max₁ }
  let suggestions₂ ← selector₂ g { c with maxSuggestions := max₂ }

  let mut result := #[]
  let mut i₁ := 0
  let mut i₂ := 0
  let mut count₁ := 0.0
  let mut count₂ := 0.0

  -- Intersperse while both arrays have elements
  while h : i₁ < suggestions₁.size ∧ i₂ < suggestions₂.size ∧ result.size < c.maxSuggestions do
    -- Decide whether to take from selector₁ or selector₂ based on the ratio
    let currentRatio := if count₁ + count₂ <= 0.0 then 0.0 else count₁ / (count₁ + count₂)
    if currentRatio < ratio then
      result := result.push suggestions₁[i₁]
      i₁ := i₁ + 1
      count₁ := count₁ + 1
    else
      result := result.push suggestions₂[i₂]
      i₂ := i₂ + 1
      count₂ := count₂ + 1

  -- Append remaining elements from selector₁
  while h : i₁ < suggestions₁.size ∧ result.size < c.maxSuggestions do
    result := result.push suggestions₁[i₁]
    i₁ := i₁ + 1

  -- Append remaining elements from selector₂
  while h : i₂ < suggestions₂.size ∧ result.size < c.maxSuggestions do
    result := result.push suggestions₂[i₂]
    i₂ := i₂ + 1

  return result

end Selector

section DenyList

/--
Premises from a module whose name has one of the following components are not retrieved.

Use `run_cmd modifyEnv fun env => moduleDenyListExt.addEntry env module` to add a module to the deny list.
-/
builtin_initialize moduleDenyListExt : SimplePersistentEnvExtension String (List String) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := (·.cons)
    addImportedFn := mkStateFromImportedEntries (·.cons) ["Lake", "Lean", "Internal", "Tactic"]
  }

/--
A premise whose name has one of the following components is not retrieved.

Use `run_cmd modifyEnv fun env => nameDenyListExt.addEntry env name` to add a name to the deny list.
-/
builtin_initialize nameDenyListExt : SimplePersistentEnvExtension String (List String) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := (·.cons)
    addImportedFn := mkStateFromImportedEntries (·.cons) ["Lake", "Lean", "Internal", "Tactic"]
  }

/--
A premise whose `type.getForallBody.getAppFn` is a constant that has one of these prefixes is not retrieved.

Use `run_cmd modifyEnv fun env => typePrefixDenyListExt.addEntry env typePrefix` to add a type prefix to the deny list.
-/
builtin_initialize typePrefixDenyListExt : SimplePersistentEnvExtension Name (List Name) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := (·.cons)
    addImportedFn := mkStateFromImportedEntries (·.cons) [`Lake, `Lean]
  }

def isDeniedModule (env : Environment) (moduleName : Name) : Bool :=
  (moduleDenyListExt.getState env).any fun p => moduleName.anyS (· == p)

def isDeniedPremise (env : Environment) (name : Name) (allowPrivate : Bool := false) : Bool := Id.run do
  if name == ``sorryAx then return true
  -- Allow private names through if allowPrivate is set (e.g., for currentFile selector)
  if name.isInternalDetail && !(allowPrivate && isPrivateName name) then return true
  if Lean.Meta.isInstanceCore env name then return true
  if Lean.Linter.isDeprecated env name then return true
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

/-- A library suggestion engine that returns locally defined theorems (those in the current file). -/
def currentFile : Selector := fun _ cfg => do
  let env ← getEnv
  let max := cfg.maxSuggestions
  -- Use map₂ from the staged map, which contains locally defined constants
  let mut suggestions := #[]
  for (name, _) in env.constants.map₂ do
    if suggestions.size >= max then
      break
    -- Allow private names since they're accessible from the current module
    if isDeniedPremise env name (allowPrivate := true) then
      continue
    if wasOriginallyTheorem env name then
      suggestions := suggestions.push { name := name, score := 1.0 }
  return suggestions

builtin_initialize librarySuggestionsExt : SimplePersistentEnvExtension Name (Option Name) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun _ name => some name  -- Last entry wins
    addImportedFn := fun entries =>
      -- Take the last selector name from all imported modules
      entries.foldl (init := none) fun acc moduleEntries =>
        moduleEntries.foldl (init := acc) fun _ name => some name
  }

/-- Attribute for registering library suggestions selectors. -/
builtin_initialize librarySuggestionsAttr : TagAttribute ←
  registerTagAttribute `library_suggestions "library suggestions selector" fun declName => do
    let decl ← getConstInfo declName
    unless decl.type == mkConst ``Selector do
      throwError "declaration '{declName}' must have type `Selector`"
    modifyEnv fun env => librarySuggestionsExt.addEntry env declName

/--
Get the currently registered library suggestions selector by looking up the stored declaration name.
Returns `none` if no selector is registered or if evaluation fails.
-/
unsafe def getSelectorImpl : MetaM (Option Selector) := do
  let some declName := librarySuggestionsExt.getState (← getEnv) | return none
  try
    evalConstCheck Selector ``Selector declName
  catch _ =>
    return none

@[implemented_by getSelectorImpl]
opaque getSelector : MetaM (Option Selector)

/-- Generate library suggestions for the given metavariable, using the currently registered library suggestions engine. -/
def select (m : MVarId) (c : Config := {}) : MetaM (Array Suggestion) := do
  let some selector ← getSelector |
    throwError "No library suggestions engine registered. \
      (Add `import Lean.LibrarySuggestions.Default` to use Lean's built-in engine, \
      or use `set_library_suggestions` to configure a custom one.)"
  selector m c

/-!
Currently the registration mechanism is just global state.
This means that if multiple modules register library suggestions engines,
the behaviour will be dependent on the order of loading modules.

We should replace this with a mechanism so that
library suggestions engines are configured via options in the `lakefile`, and
commands are only used to override in a single declaration or file.
-/

open Lean Elab Command in
@[builtin_command_elab setLibrarySuggestionsCmd, inherit_doc setLibrarySuggestionsCmd]
def elabSetLibrarySuggestions : CommandElab
  | `(command| set_library_suggestions $selector) => do
    if `Lean.LibrarySuggestions.Basic ∉ (← getEnv).header.moduleNames then
      logWarning "Add `import Lean.LibrarySuggestions.Basic` before using the `set_library_suggestions` command."
    -- Generate a fresh name for the selector definition
    let name ← liftMacroM <| Macro.addMacroScope `_librarySuggestions
    -- Elaborate the definition with the library_suggestions attribute
    -- Note: @[expose] public, to ensure visibility across module boundaries
    -- Use fully qualified `Lean.LibrarySuggestions.Selector` for module compatibility
    elabCommand (← `(@[expose, library_suggestions] public def $(mkIdent name) : Lean.LibrarySuggestions.Selector := $selector))
  | _ => throwUnsupportedSyntax

open Lean.Elab.Tactic in
@[builtin_tactic Lean.Parser.Tactic.suggestions] def evalSuggestions : Tactic := fun _ =>
  liftMetaTactic1 fun mvarId => do
    let suggestions ← select mvarId
    let mut msg : MessageData := "Library suggestions:"
    -- Check if all scores are 1.0
    let allScoresOne := suggestions.all (·.score == 1.0)
    for s in suggestions do
      msg := msg ++ Format.line ++ "  " ++ MessageData.ofConstName s.name
      if !allScoresOne then
        msg := msg ++ m!" (score: {s.score})"
      if let some flag := s.flag then
        msg := msg ++ m!" [{flag}]"
    logInfo msg
    return mvarId

end Lean.LibrarySuggestions
