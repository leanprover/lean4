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


builtin_initialize identifierSuggestionForAttr : PersistentEnvExtension
    (Name × Array Name) /- *Store* mappings from incorrect names to corrections (identifiers that exist) -/
    (Name × Array Name) /- *Add* mappings from existing functions to possible incorrect namings -/
    (NameMap NameSet) /- *Use* mapping from incorrect names to corrections (identifiers that exist) -/ ←
  let ext ← registerPersistentEnvExtension {
    mkInitial := pure {},
    addImportedFn := fun modules => pure <|
      modules.foldl (init := {}) fun accum entries =>
        entries.foldl (init := accum) fun accum (altName, trueNames) =>
          accum.alter altName (fun old => trueNames.foldl (β := NameSet) (init := old.getD ∅) fun accum trueName =>
            accum.insert trueName),
    addEntryFn := fun table (trueName, altNames) =>
      altNames.foldl (init := table) fun accum alt =>
        accum.alter alt (·.getD {} |>.insert trueName)
    exportEntriesFn table := table.toArray.map fun (altName, trueNames) =>
      (altName, trueNames.toArray)
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
      modifyEnv (ext.addEntry · (decl, altSyntaxIds.map (·.getId)))
  }

  return ext

public def getSuggestions [Monad m] [MonadEnv m] (fullName : Name) : m (Array Name) := do
  return identifierSuggestionForAttr.getState (← getEnv)
    |>.find? fullName
    |>.getD {}
    |>.toArray

/--
Throw an unknown constant error message, potentially suggesting alternatives using
{name}`suggest_for` attributes. (Like {name}`throwUnknownConstantAt` but with suggestions.)

The "Unknown constant `<id>`" message will fully qualify the name, whereas the
-/
public def throwUnknownConstantWithSuggestions (constName : Name) : CoreM α := do
  let suggestions ← getSuggestions constName
  let ref ← getRef
  let hint ← if suggestions.size = 0 then
      pure MessageData.nil
    else
      -- Modify suggestions to have the same structure as the user-provided identifier, but only
      -- if that doesn't cause ambiguity.
      let rawId := (← getRef).getId
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
      m!"Perhaps you meant {alternative} in place of `{.ofName rawId}`:".hint (suggestions.map fun suggestion =>
        let modified := modifySuggestion suggestion
        {
          suggestion := s!"{modified}",
          toCodeActionTitle? := .some (s!"Suggested replacement: {·}"),
          diffGranularity := .all,
          -- messageData? := .some m!"replace `{.ofName rawId}` with `{.ofName modified}`",
        }) ref
  throwUnknownIdentifierAt (declHint := constName) ref (m!"Unknown constant `{.ofConstName constName}`" ++ hint)
