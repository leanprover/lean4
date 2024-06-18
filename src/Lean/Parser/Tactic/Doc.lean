/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Thrane Christiansen
-/
prelude
import Lean.Attributes
import Lean.Data.NameMap
import Lean.DocString
import Lean.Environment
import Lean.Elab.InfoTree.Main
import Lean.Parser.Types

set_option linter.missingDocs true

namespace Lean.Parser.Tactic.Doc

/--
Stores a collection of tactic aliases, to track which new syntax rules represent new forms of
existing tactics.
-/
builtin_initialize tacticAliasExt
    : PersistentEnvExtension (Name × Name) (Name × Name) (NameMap Name) ←
  registerPersistentEnvExtension {
    mkInitial := pure {},
    addImportedFn := fun _ => pure {},
    addEntryFn := fun as (src, tgt) => as.insert src tgt,
    exportEntriesFn := fun es =>
      es.fold (fun a src tgt => a.push (src, tgt)) #[] |>.qsort (Name.quickLt ·.1 ·.1)
  }

/--
If `tac` is registered as the alias of another tactic, then return the canonical name for it.
-/
def aliasOfTactic [Monad m] [MonadEnv m] (tac : Name) : m (Option Name) := do
  let env ← getEnv
  match env.getModuleIdxFor? tac with
  | some modIdx =>
    match (tacticAliasExt.getModuleEntries env modIdx).binSearch (tac, .anonymous) (Name.quickLt ·.1 ·.1) with
    | some (_, val) => pure (some val)
    | none => pure none
  | none => pure (tacticAliasExt.getState env |>.find? tac)

/--
Find all aliases of a given canonical tactic name.
-/
def aliases [Monad m] [MonadEnv m] (tac : Name) : m NameSet := do
  let env ← getEnv
  let mut found := {}
  for (src, tgt) in tacticAliasExt.getState env do
    if tgt == tac then found := found.insert src
  for arr in tacticAliasExt.toEnvExtension.getState env |>.importedEntries do
    for (src, tgt) in arr do
      if tgt == tac then found := found.insert src
  pure found

/--
Declare this tactic to be an alias or alternative form of an existing tactic.

This has the following effects:
 * The alias relationship is saved
 * The docstring is taken from the original tactic, if present
-/
syntax (name := tactic_alias) "tactic_alias" (ppSpace ident) : attr

builtin_initialize
  let name := `tactic_alias
  registerBuiltinAttribute {
    name := name,
    ref := by exact decl_name%,
    add := fun decl stx kind => do
      unless kind == AttributeKind.global do throwError "invalid attribute '{name}', must be global"
      unless ((← getEnv).getModuleIdxFor? decl).isNone do
        throwError "invalid attribute '{name}', declaration is in an imported module"
      let `(attr|tactic_alias $tgt:ident) := stx
        | throwError "invalid '{name}' attribute"

      let tgtName ← Lean.Elab.realizeGlobalConstNoOverloadWithInfo tgt

      if let some tgt' ← aliasOfTactic tgtName then
        throwError "'{tgtName}' is itself an alias of '{tgt'}'"
      modifyEnv fun env => tacticAliasExt.addEntry env (decl, tgtName)
      if let some docs ← findDocString? (← getEnv) tgtName then
        if (← findDocString? (← getEnv) decl).isSome then
          logWarningAt stx m!"Replacing docstring for '{decl}' with the one from '{tgtName}'"
        addDocString decl docs
    descr := "Register a tactic parser as an alias of an existing tactic, so they can be grouped together in documentation.",
    applicationTime := .afterTypeChecking
  }

/--
The known tactic tags that allow tactics to be grouped by purpose.
-/
builtin_initialize knownTacticTagExt
    : PersistentEnvExtension
        (Name × String × Option String)
        (Name × String × Option String)
        (NameMap (String × Option String)) ←
  registerPersistentEnvExtension {
    mkInitial := pure {},
    addImportedFn := fun _ => pure {},
    addEntryFn := fun as (src, tgt) => as.insert src tgt,
    exportEntriesFn := fun es =>
      es.fold (fun a src tgt => a.push (src, tgt)) #[] |>.qsort (Name.quickLt ·.1 ·.1)
  }

/--
Get the user-facing name and docstring for a tactic tag.
-/
def tagInfo [Monad m] [MonadEnv m] (tag : Name) : m (Option (String × Option String)) := do
  let env ← getEnv
  match env.getModuleIdxFor? tag with
  | some modIdx =>
    match (knownTacticTagExt.getModuleEntries env modIdx).binSearch (tag, default) (Name.quickLt ·.1 ·.1) with
    | some (_, val) => pure (some val)
    | none => pure none
  | none => pure (knownTacticTagExt.getState env |>.find? tag)

/-- Enumerate the tactic tags that are available -/
def allTags [Monad m] [MonadEnv m] : m (List Name) := do
  let env ← getEnv
  let mut found : NameSet := {}
  for (tag, _) in knownTacticTagExt.getState env do
    found := found.insert tag
  for arr in tacticAliasExt.toEnvExtension.getState env |>.importedEntries do
    for (tag, _) in arr do
      found := found.insert tag
  pure (found.toArray.qsort (·.toString < ·.toString) |>.toList)

/--
Register a tactic tag, saving its user-facing name and docstring.
-/
syntax (name := register_tactic_tag) (docComment ppLine)? "register_tactic_tag" ident str : command

/--
The mapping between tags and tactics. Tags may be applied in any module, not just the defining
module for the tactic.

Because this is expected to be augmented regularly, but queried rarely (only when generating
documentation indices), it is just stored as flat unsorted arrays of pairs. Before it is used for
some other purpose, consider a new representation.

The first projection in each pair is the tactic name, and the second is the tag name.
-/
builtin_initialize tacticTagExt
    : PersistentEnvExtension (Name × Name) (Name × Name) (Array (Name × Name)) ←
  registerPersistentEnvExtension {
    mkInitial := pure {},
    addImportedFn := fun _ => pure #[],
    addEntryFn := Array.push,
    exportEntriesFn := id
  }


/--
Add a tag to a tactic.

Tags should be applied to the canonical names for tactics.
-/
syntax (name := tactic_tag) "tactic_tag" (ppSpace ident)+ : attr

builtin_initialize
  let name := `tactic_tag
  registerBuiltinAttribute {
    name := name,
    ref := by exact decl_name%,
    add := fun decl stx kind => do
      unless kind == AttributeKind.global do throwError "invalid attribute '{name}', must be global"
      let `(attr|tactic_tag $tags:ident*) := stx
        | throwError "invalid '{name}' attribute"
      if let some tgt' ← aliasOfTactic decl then
        throwError "'{decl}' is an alias of '{tgt'}'"
      for t in tags do
        let tagName := t.getId
        if let some _ ← tagInfo tagName then
          modifyEnv (tacticTagExt.addEntry · (decl, tagName))
        else
          let all ← allTags
          let extra : MessageData :=
              let count := all.length
              let name := (m!"'{·}'")
              let suggestions :=
                if count == 0 then m!"(no tags defined)"
                else if count == 1 then
                  m!"(expected {MessageData.joinSep (all.map name) ", "})"
                else if count < 10 then
                  m!"(expected one of {MessageData.joinSep (all.map name) ", "})"
                else
                  m!"(expected one of {
                    MessageData.joinSep (all.take 10 |>.map name) ", " ++ ", ..."
                  })"
              m!"(expected one of {suggestions})"

          throwErrorAt t (m!"unknown tag '{tagName}' " ++ extra)
    descr := "Register a tactic parser as an alias of an existing tactic, so they can be " ++
      "grouped together in documentation.",
    applicationTime := .afterTypeChecking
  }

/--
Extensions to tactic documentation.

This provides a structured way to indicate that an extensible tactic has been extended (for
instance, new cases tried by `trivial`).
-/
builtin_initialize tacticDocExtExt
    : PersistentEnvExtension (Name × Array String) (Name × String) (NameMap (Array String)) ←
  registerPersistentEnvExtension {
    mkInitial := pure {},
    addImportedFn := fun _ => pure {},
    addEntryFn := fun es (x, ext) => es.insert x (es.findD x #[] |>.push ext),
    exportEntriesFn := fun es =>
      es.fold (fun a src tgt => a.push (src, tgt)) #[] |>.qsort (Name.quickLt ·.1 ·.1)
  }

/-- Add more documentation as an extension of the documentation for a given tactic. -/
syntax (docComment)? "tactic_extension" ident : command
