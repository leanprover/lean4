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
open Elab.Term

set_option doc.verso true

/--
Create the extension mapping from existing identifiers to the incorrect alternatives for which we
want to provide suggestions. This is mostly equivalent to a {name}`MapDeclarationExtension` or the
extensions underlying {name}`ParametricAttribute` attributes, but it differs in allowing
{name}`suggest_for` attributes to be assigned in files other than the ones where they were defined.
-/
def mkExistingToIncorrect : IO (PersistentEnvExtension (Name × Array Name) (Name × Array Name) (NameMap NameSet)) := registerPersistentEnvExtension {
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

/--
Create the extension mapping incorrect identifiers to the existing identifiers we want to suggest as
replacements. This association is the opposite of the usual mapping for {name}`ParametricAttribute`
attributes.
-/
def mkIncorrectToExisting : IO (PersistentEnvExtension (Name × Array Name) (Name × Array Name) (NameMap NameSet)) := registerPersistentEnvExtension {
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

builtin_initialize identifierSuggestionsImpl : (PersistentEnvExtension (Name × Array Name) (Name × Array Name) (NameMap NameSet)) × (PersistentEnvExtension (Name × Array Name) (Name × Array Name) (NameMap NameSet)) ←
  let existingToIncorrect ← mkExistingToIncorrect
  let incorrectToExisting ← mkIncorrectToExisting

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
{name}`suggest_for` annotation.
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
Throw an unknown constant/identifier error message, potentially suggesting alternatives using
{name}`suggest_for` attributes.

The replacement will mimic the path structure of the original as much as possible if they share a
path prefix: if there is a suggestion for replacing `Foo.Bar.jazz` with `Foo.Bar.baz`, then
`Bar.jazz` will be replaced by `Bar.baz` unless the resulting constant is ambiguous.
-/
public def throwUnknownNameWithSuggestions (constName : Name) (idOrConst := "identifier") (declHint := constName) (ref? : Option Syntax := .none) (extraMsg : MessageData := .nil) : TermElabM α := do
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
  throwUnknownIdentifierAt (declHint := declHint) ref (m!"Unknown {idOrConst} `{.ofConstName constName}`" ++ extraMsg ++ hint)

public def Elab.Term.hintAutoImplicitFailure (exp : Expr) (expected := "a function") : TermElabM MessageData := do
  let autoBound := (← readThe Context).autoBoundImplicitContext
  unless autoBound.isSome && exp.isFVar && autoBound.get!.boundVariables.any (· == exp) do
    return .nil
  let name ← exp.fvarId!.getUserName
  let baseMessage := m!"The identifier `{.ofName name}` is unknown, \
    and Lean's `autoImplicit` option causes an unknown identifier to be treated as an implicitly \
    bound variable with an unknown type. \
    However, the unknown type cannot be {expected}, and {expected} is what Lean expects here. \
    This is often the result of a typo or a missing `import` or `open` statement."
  let suggestionExtra : MessageData := match (← getSuggestions name).toList with
    | [] => .nil
    | [opt] => Format.line ++ Format.line ++ m!"Perhaps you meant `{.ofConstName opt}` in place of `{.ofName name}`?"
    | opts =>  Format.line ++ Format.line ++ m!"Perhaps you meant one of these in place of `{.ofName name}`:" ++
        .joinSep (opts.map (indentD m!"• `{.ofConstName ·}`")) .nil
  return MessageData.hint' (baseMessage ++ suggestionExtra)
