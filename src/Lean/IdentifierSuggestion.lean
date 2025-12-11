/-
Copyright (c) 2025 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob Simmons
-/
module

prelude
public import Lean.Attributes
public import Lean.Exception
public import Lean.Meta.Hint
public import Lean.Elab.DeclModifiers
public import Lean.ResolveName
import all Lean.Elab.ErrorUtils

namespace Lean

set_option doc.verso true

public abbrev NameMapExtension := PersistentEnvExtension (Name × Array Name) (Name × Array Name) (NameMap NameSet)

builtin_initialize identifierSuggestionsImpl : NameMapExtension × NameMapExtension ←
  -- This is mostly equivalent to a standard `ParametricAttribute` implementation
  let existingToIncorrect : NameMapExtension ← registerPersistentEnvExtension {
    name := `Lean.identifierSuggestForAttr.existingToIncorrect
    mkInitial := pure {},
    addImportedFn := fun _ => pure {},
    addEntryFn := fun table (trueName, altNames) =>
      table.alter trueName fun old =>
        altNames.foldl (β := NameSet) (init := old.getD {}) fun accum altName =>
          accum.insert altName
    exportEntriesFn table :=
      table.toArray.map (fun (trueName, altNames) =>(trueName, altNames.toArray))
        |>.qsort (lt := fun a b => Name.quickLt a.1 b.1)
  }

  -- This indexes information the opposite of the way a `ParametricAttribute` does
  let incorrectToExisting : NameMapExtension ← registerPersistentEnvExtension {
    name := `Lean.identifierSuggestForAttr.incorrectToExisting
    mkInitial := pure {},
    addImportedFn := fun _ => pure {},
    addEntryFn := fun table (trueName, altNames) =>
      altNames.foldl (init := table) fun accum altName =>
        accum.alter altName fun old =>
          old.getD {} |>.insert trueName
    exportEntriesFn table :=
      table.toArray.map (fun (altName, trueNames) => (altName, trueNames.toArray))
        |>.qsort (lt := fun a b => Name.quickLt a.1 b.1)
  }

  registerBuiltinAttribute {
    name := `suggest_for,
    descr := "suggest other (incorrect, not-existing) identifiers that someone might use when they actually want this definition",
    add (decl : Name) (stx : Syntax) (kind : AttributeKind) := do
      unless kind == AttributeKind.global do throwAttrMustBeGlobal `suggest_for kind
      let altSyntaxIds : Array Syntax ← match stx with
        | -- Attributes parsed _after_ the suggest_for notation is added
          .node _ ``suggest_for #[.atom _ "suggest_for", .node _ `null ids] => pure ids
        | -- Attributes parsed _before the suggest_for notation is added
          .node _ ``Parser.Attr.simple #[.ident _ _ `suggest_for [], .node _ `null #[id]] => pure #[id]
        | _ => throwError "Invalid `[suggest_for]` attribute syntax {repr stx}"
      if isPrivateName decl then
        throwError "Cannot make suggestions for private names"
      let altIds := altSyntaxIds.map (·.getId)
      modifyEnv (existingToIncorrect.addEntry · (decl, altIds))
      modifyEnv (incorrectToExisting.addEntry · (decl, altIds))
  }

  return (existingToIncorrect, incorrectToExisting)

/--
Given a name, find all the stored correct, existing identifiers that mention that name in a
{lit}`suggest_for` annotation.
-/
public def getSuggestions [Monad m] [MonadEnv m] (incorrectName : Name) : m NameSet := do
  let env ← getEnv
  let { state, importedEntries } := identifierSuggestionsImpl.2.toEnvExtension.getState env
  let localEntries := state.find? incorrectName |>.getD {}
  return importedEntries.foldl (init := localEntries) fun results moduleEntry =>
    match moduleEntry.binSearch (incorrectName, default) (fun a b => Name.quickLt a.1 b.1) with
    | none => results
    | some (_, extras) => extras.foldl (init := results) fun accum extra => accum.insert extra

/--
Given a (presumably existing) identifier, find all the {lit}`suggest_for` annotations that were given
for that identifier.
-/
public def getStoredSuggestions [Monad m] [MonadEnv m] (trueName : Name) : m NameSet := do
  let env ← getEnv
  let { state, importedEntries } := identifierSuggestionsImpl.1.toEnvExtension.getState env
  let localEntries := state.find? trueName |>.getD {}
  return importedEntries.foldl (init := localEntries) fun results moduleEntry =>
    match moduleEntry.binSearch (trueName, default) (fun a b => Name.quickLt a.1 b.1) with
    | none => results
    | some (_, extras) => extras.foldl (init := results) fun accum extra => accum.insert extra

/--
Throw an unknown constant error message, potentially suggesting alternatives using
{name}`suggest_for` attributes. (Like {name}`throwUnknownConstantAt` but with suggestions.)

The "Unknown constant `<id>`" message will fully qualify the name, whereas the
-/
public def throwUnknownConstantWithSuggestions (constName : Name) (ref? : Option Syntax := .none) : CoreM α := do
  let suggestions := (← getSuggestions constName).toArray
  let ref := ref?.getD (← getRef)
  let hint ← if suggestions.size = 0 then
      pure MessageData.nil
    else
      -- Modify suggestions to have the same structure as the user-provided identifier, but only
      -- if that doesn't cause ambiguity.
      let rawId := ref.getId
      let env ← getEnv
      let ns ← getCurrNamespace
      let openDecls ← getOpenDecls
      let modifySuggestion := match constName.eraseSuffix? rawId with
        | .none => id
        | .some prefixName => fun (suggestion : Name) =>
            let candidate := suggestion.replacePrefix prefixName .anonymous
            if (ResolveName.resolveGlobalName env {} ns openDecls candidate |>.length) != 1 then
              suggestion
            else
              candidate

      let alternative := if h : suggestions.size = 1 then m!"`{.ofConstName suggestions[0]}`" else m!"one of these"
      let inPlaceOfThis := if rawId.isAnonymous then .nil else m!" in place of `{.ofName rawId}`"
      m!"Perhaps you meant {alternative}{inPlaceOfThis}:".hint (suggestions.map fun suggestion =>
        let modified := modifySuggestion suggestion
        {
          suggestion := s!"{modified}",
          toCodeActionTitle? := .some (s!"Change to {·}"),
          messageData? := .some m!"`{.ofConstName suggestion}`",
        }) ref
  throwUnknownIdentifierAt (declHint := constName) ref (m!"Unknown constant `{.ofConstName constName}`" ++ hint)
