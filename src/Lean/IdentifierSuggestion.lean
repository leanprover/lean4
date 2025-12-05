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

builtin_initialize identifierSuggestionForAttr : ParametricAttribute (Name × Array Name) ←
  registerParametricAttribute {
    name := `suggest_for,
    descr := "suggest other (incorrect, not-existing) identifiers that someone might use when they actually want this definition",
    getParam := fun trueDeclName stx => do
      let `(attr| suggest_for $altNames:ident*) := stx
        | throwError "Invalid `[suggest_for]` attribute syntax"
      let ns := trueDeclName.getPrefix
      return (trueDeclName, altNames.map (·.getId))
    }

public def getSuggestions [Monad m] [MonadEnv m] (fullName : Name) : m (Array Name) := do
  let mut possibleReplacements := #[]
  let (_, allSuggestions) := identifierSuggestionForAttr.ext.getState (← getEnv)
  for (_, trueName, suggestions) in allSuggestions do
    for suggestion in suggestions do
      if fullName = suggestion then
        possibleReplacements := possibleReplacements.push trueName
  return possibleReplacements.qsort (lt := lt)
where
  -- Ensure the result of getSuggestions is stable (if arbitrary)
  lt : Name -> Name -> Bool
    | .anonymous, _ => false
    | .str _ _, .anonymous => true
    | .num _ _, .anonymous => true
    | .str _ _, .num _ _ => true
    | .num _ _, .str _ _ => false
    | .num a n, .num b m => n < m || n == m && lt a b
    | .str a s1, .str b s2 => s1 < s2 || s1 == s2 && lt a b

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
