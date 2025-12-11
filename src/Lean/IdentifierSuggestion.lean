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

public structure IdentSuggestion where
  existingToIncorrect : NameMap NameSet := {}
  incorrectToExisting : NameMap NameSet := {}
deriving Inhabited

def IdentSuggestion.add (table : IdentSuggestion) (trueName : Name) (altNames : Array Name) : IdentSuggestion :=
  { existingToIncorrect :=
      table.existingToIncorrect.alter trueName fun old =>
        altNames.foldl (β := NameSet) (init := old.getD {}) fun accum altName =>
          accum.insert altName
    incorrectToExisting :=
      altNames.foldl (init := table.incorrectToExisting) fun accum altName =>
        accum.alter altName fun old =>
          old.getD {} |>.insert trueName
  }

builtin_initialize identifierSuggestionForAttr : PersistentEnvExtension
    (Name × Array Name) /- Mapping from existing constant to potential incorrect alternative names -/
    (Name × Array Name) /- Mapping from existing constant to potential incorrect alternative names -/
    IdentSuggestion /- Two directional mapping between existing identifier and alternative incorrect mappings -/ ←
  let ext ← registerPersistentEnvExtension {
    mkInitial := pure {},
    addImportedFn := fun modules => pure <|
      (modules.foldl (init := {}) fun accum entries =>
        entries.foldl (init := accum) fun accum (trueName, altNames) =>
          accum.add trueName altNames),
    addEntryFn := fun table (trueName, altNames) => table.add trueName altNames
    exportEntriesFn table := table.existingToIncorrect.toArray.map fun (trueName, altNames) =>
      (trueName, altNames.toArray)
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
      modifyEnv (ext.addEntry · (decl, altSyntaxIds.map (·.getId)))
  }

  return ext

/--
Given a name, find all the stored correct, existing identifiers that mention that name in a
{lit}`suggest_for` annotation.
-/
public def getSuggestions [Monad m] [MonadEnv m] (incorrectName : Name) : m NameSet := do
  return identifierSuggestionForAttr.getState (← getEnv)
    |>.incorrectToExisting
    |>.find? incorrectName
    |>.getD {}

/--
Given a (presumably existing) identifier, find all the {lit}`suggest_for` annotations that were given
for that identifier.
-/
public def getStoredSuggestions [Monad m] [MonadEnv m] (trueName : Name) : m NameSet := do
  return identifierSuggestionForAttr.getState (← getEnv)
    |>.existingToIncorrect
    |>.find? trueName
    |>.getD {}

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
