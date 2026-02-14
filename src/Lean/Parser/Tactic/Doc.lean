/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Thrane Christiansen
-/
module

prelude
public import Lean.Environment
import Lean.Elab.InfoTree.Main
meta import Lean.Parser.Attr
import Lean.Parser.Extension
import Lean.ExtraModUses

public section

set_option linter.missingDocs true

namespace Lean.Parser.Tactic.Doc

open Lean.Parser (registerParserAttributeHook)
open Lean.Parser.Attr

/-- Check whether a name is a tactic syntax kind -/
def isTactic (env : Environment) (kind : Name) : Bool := Id.run do
  let some tactics := (Lean.Parser.parserExtension.getState env).categories.find? `tactic
    | return false
  return tactics.kinds.contains kind

/--
Stores a collection of *tactic alternatives*, to track which new syntax rules represent new forms of
existing tactics.
-/
builtin_initialize tacticAlternativeExt
    : PersistentEnvExtension (Name × Name) (Name × Name) (NameMap Name) ←
  registerPersistentEnvExtension {
    mkInitial := pure {},
    addImportedFn := fun _ => pure {},
    addEntryFn := fun as (src, tgt) => as.insert src tgt,
    exportEntriesFn := fun es =>
      es.foldl (fun a src tgt => a.push (src, tgt)) #[] |>.qsort (Name.quickLt ·.1 ·.1)
  }

/--
If `tac` is registered as the alternative form of another tactic, then return the canonical name for
it.
-/
def alternativeOfTactic (env : Environment) (tac : Name) : Option Name :=
  match env.getModuleIdxFor? tac with
  | some modIdx =>
    match (tacticAlternativeExt.getModuleEntries env modIdx).binSearch (tac, .anonymous) (Name.quickLt ·.1 ·.1) with
    | some (_, val) => some val
    | none => none
  | none => tacticAlternativeExt.getState env |>.find? tac

/--
Find all alternatives for a given canonical tactic name.
-/
def aliases [Monad m] [MonadEnv m] (tac : Name) : m NameSet := do
  let env ← getEnv
  let mut found := {}
  for (src, tgt) in tacticAlternativeExt.getState env do
    if tgt == tac then found := found.insert src
  for arr in tacticAlternativeExt.toEnvExtension.getState env |>.importedEntries do
    for (src, tgt) in arr do
      if tgt == tac then found := found.insert src
  pure found

builtin_initialize
  let name := `tactic_alt
  registerBuiltinAttribute {
    name := name,
    ref := by exact decl_name%,
    add := fun decl stx kind => do
      unless kind == AttributeKind.global do throwAttrMustBeGlobal name kind
      unless ((← getEnv).getModuleIdxFor? decl).isNone do
        throwAttrDeclInImportedModule name decl
      let `(«tactic_alt»|tactic_alt $tgt) := stx
        | throwError "Invalid `[{name}]` attribute syntax"

      let tgtName ← Lean.Elab.realizeGlobalConstNoOverloadWithInfo tgt
      recordExtraModUseFromDecl (isMeta := false) tgtName

      if !(isTactic (← getEnv) tgtName) then throwErrorAt tgt "`{tgtName}` is not a tactic"
      -- If the target is a known syntax kind, ensure that it's a tactic
      let mut cats := #[]
      for (catName, cat) in parserExtension.getState (← getEnv) |>.categories do
        if cat.kinds.contains decl then cats := cats.push catName
      if !cats.isEmpty && cats.all (· ≠ `tactic) then
        let catNames := cats.map fun c => m!"`{c}`"
        let s := if catNames.size > 1 then m!"ies" else m!"y"
        throwError "`{decl}` is not a tactic (it is in the categor{s} {.andList catNames.toList})"

      if let some tgt' := alternativeOfTactic (← getEnv) tgtName then
        throwError "`{tgtName}` is itself an alternative for `{tgt'}`"
      modifyEnv fun env => tacticAlternativeExt.addEntry env (decl, tgtName)

    descr :=
      "Register a tactic parser as an alternative form of an existing tactic, so they " ++
      "can be grouped together in documentation.",
    -- This runs prior to elaboration because it allows a check for whether the decl is present
    -- in the environment to determine whether we can see if it's a tactic name. This is useful
    -- when the attribute is applied after definition, using an `attribute` command (error checking
    -- for the `@[tactic_alt TAC]` syntax is performed by the parser attribute hook). If this
    -- attribute ran later, then the decl would already be present.
    applicationTime := .afterCompilation --.beforeElaboration
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
      es.foldl (fun a src tgt => a.push (src, tgt)) #[] |>.qsort (Name.quickLt ·.1 ·.1)
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
  for arr in knownTacticTagExt.toEnvExtension.getState env |>.importedEntries do
    for (tag, _) in arr do
      found := found.insert tag
  pure (found.toArray.qsort (·.toString < ·.toString) |>.toList)

/-- Enumerate the tactic tags that are available, with their user-facing name and docstring -/
def allTagsWithInfo [Monad m] [MonadEnv m] : m (List (Name × String × Option String)) := do
  let env ← getEnv
  let mut found : NameMap (String × Option String) := {}
  for (tag, info) in knownTacticTagExt.getState env do
    found := found.insert tag info
  for arr in knownTacticTagExt.toEnvExtension.getState env |>.importedEntries do
    for (tag, info) in arr do
      found := found.insert tag info
  let arr := found.foldl (init := #[]) (fun arr k v => arr.push (k, v))
  pure (arr.qsort (·.1.toString < ·.1.toString) |>.toList)

/--
The mapping between tags and tactics. Tags may be applied in any module, not just the defining
module for the tactic.

Because this is expected to be augmented regularly, but queried rarely (only when generating
documentation indices), it is just stored as flat unsorted arrays of pairs. Before it is used for
some other purpose, consider a new representation.

The first projection in each pair is the tactic name, and the second is the tag name.
-/
builtin_initialize tacticTagExt
    : PersistentEnvExtension (Name × Name) (Name × Name) (NameMap NameSet) ←
  registerPersistentEnvExtension {
    mkInitial := pure {},
    addImportedFn := fun _ => pure {},
    addEntryFn := fun tags (decl, newTag) => tags.insert decl (tags.getD decl {} |>.insert newTag)
    exportEntriesFn := fun tags => Id.run do
      let mut exported := #[]
      for (decl, dTags) in tags do
        for t in dTags do
          exported := exported.push (decl, t)
      exported
  }

builtin_initialize
  let name := `tactic_tag
  registerBuiltinAttribute {
    name := name,
    ref := by exact decl_name%,
    add := fun decl stx kind => do
      unless kind == AttributeKind.global do throwAttrMustBeGlobal name kind
      let `(«tactic_tag»|tactic_tag $tags*) := stx
        | throwError "Invalid `[{name}]` attribute syntax"

      if (← getEnv).find? decl |>.isSome then
        if !(isTactic (← getEnv) decl) then
          throwErrorAt stx "`{.ofConstName decl}` is not a tactic"

      if let some tgt' := alternativeOfTactic (← getEnv) decl then
        throwErrorAt stx "`{.ofConstName decl}` is an alternative form of `{.ofConstName tgt'}`"

      for t in tags do
        let tagName := t.getId
        if let some _ ← tagInfo tagName then
          modifyEnv (tacticTagExt.addEntry · (decl, tagName))
        else
          let all ← allTags
          let extra : MessageData :=
              let count := all.length
              let name := (m!"`{·}`")
              let suggestions :=
                if count == 0 then m!"(no tags defined)"
                else if count == 1 then
                  MessageData.joinSep (all.map name) ", "
                else if count < 10 then
                  m!"one of " ++ MessageData.joinSep (all.map name) ", "
                else
                  m!"one of " ++
                  MessageData.joinSep (all.take 10 |>.map name) ", " ++ ", ..."
              m!"(expected {suggestions})"

          throwErrorAt t (m!"Unknown tag `{tagName}` " ++ extra)
    descr := "Register a tactic parser as an alternative of an existing tactic, so they can be " ++
      "grouped together in documentation.",
    -- This runs prior to elaboration because it allows a check for whether the decl is present
    -- in the environment to determine whether we can see if it's a tactic name. This is useful
    -- when the attribute is applied after definition, using an `attribute` command (error checking
    -- for the `@[tactic_tag ...]` syntax is performed by the parser attribute hook). If this
    -- attribute ran later, then the decl would already be present.
    applicationTime := .beforeElaboration
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
    addEntryFn := fun es (x, ext) => es.insert x (es.getD x #[] |>.push ext),
    exportEntriesFn := fun es =>
      es.foldl (fun a src tgt => a.push (src, tgt)) #[] |>.qsort (Name.quickLt ·.1 ·.1)
  }

/-- Gets the extensions declared for the documentation for the given canonical tactic name -/
def getTacticExtensions (env : Environment) (tactic : Name) : Array String := Id.run do
  let mut extensions := #[]
  -- Extensions may be declared in any module, so they must all be searched
  for modArr in tacticDocExtExt.toEnvExtension.getState env |>.importedEntries do
    if let some (_, strs) := modArr.binSearch (tactic, #[]) (Name.quickLt ·.1 ·.1) then
      extensions := extensions ++ strs
  if let some strs := tacticDocExtExt.getState env |>.find? tactic then
    extensions := extensions ++ strs
  pure extensions

/-- Gets the rendered extensions for the given canonical tactic name -/
def getTacticExtensionString (env : Environment) (tactic : Name) : String := Id.run do
  let exts := getTacticExtensions env tactic
  if exts.size == 0 then ""
  else "\n\nExtensions:\n\n" ++ String.join (exts.toList.map bullet) |>.trimAsciiEnd |>.copy
where
  indentLine (str : String.Slice) : String :=
    (if str.all Char.isWhitespace then str.copy else "   " ++ str) ++ "\n"
  bullet (str : String) : String :=
    let lines := str.split '\n' |>.toList
    match lines with
    | [] => ""
    | [l] => " * " ++ l ++ "\n\n"
    | l::ls => " * " ++ l ++ "\n" ++ String.join (ls.map indentLine) ++ "\n\n"

/--
The mapping between tactics and their custom names.

The first projection in each pair is the tactic name, and the second is the custom name.
-/
builtin_initialize tacticNameExt
    : PersistentEnvExtension
        (Name × String)
        (Name × String)
        (NameMap String) ←
  registerPersistentEnvExtension {
    mkInitial := pure {},
    addImportedFn := fun _ => pure {},
    addEntryFn := fun as (src, tgt) => as.insert src tgt,
    exportEntriesFn := fun es =>
      es.foldl (fun a src tgt => a.push (src, tgt)) #[] |>.qsort (Name.quickLt ·.1 ·.1)
  }

/--
Finds the custom name assigned to `tac`, or returns `none` if there is no such custom name.
-/
def customTacticName [Monad m] [MonadEnv m] (tac : Name) : m (Option String) := do
  let env ← getEnv
  match env.getModuleIdxFor? tac with
  | some modIdx =>
    match (tacticNameExt.getModuleEntries env modIdx).binSearch (tac, default) (Name.quickLt ·.1 ·.1) with
    | some (_, val) => return some val
    | none => return none
  | none => return tacticNameExt.getState env |>.find? tac

builtin_initialize
  let name := `tactic_name
  registerBuiltinAttribute {
    name := name,
    ref := by exact decl_name%,
    add := fun decl stx kind => do
      unless kind == AttributeKind.global do throwAttrMustBeGlobal name kind
      let name ←
        match stx with
        | `(«tactic_name»|tactic_name $name:str) =>
          pure name.getString
        | `(«tactic_name»|tactic_name $name:ident) =>
          pure (name.getId.toString (escape := false))
        | _ => throwError "Invalid `[{name}]` attribute syntax"

      if (← getEnv).find? decl |>.isSome then
        if !(isTactic (← getEnv) decl) then
          throwErrorAt stx m!"`{.ofConstName decl}` is not a tactic"
        if let some idx := (← getEnv).getModuleIdxFor? decl then
          if let some mod := (← getEnv).allImportedModuleNames[idx]? then
            throwErrorAt stx m!"`{.ofConstName decl}` is defined in `{mod}`, but custom names can only be added in the tactic's defining module."
          else
            throwErrorAt stx m!"`{.ofConstName decl}` is defined in an imported module, but custom names can only be added in the tactic's defining module."

      if let some tgt' := alternativeOfTactic (← getEnv) decl then
        throwErrorAt stx "`{.ofConstName decl}` is an alternative form of `{.ofConstName tgt'}`"

      if let some n ← customTacticName decl then
        throwError m!"The tactic `{.ofConstName decl}` already has the custom name `{n}`"

      modifyEnv fun env => tacticNameExt.addEntry env (decl, name)

    descr :=
      "Registers a custom name for a tactic. This custom name should be a prefix of the " ++
      "tactic's syntax, because it is used in completion.",
    applicationTime := .beforeElaboration
  }

-- Note: this error handler doesn't prevent all cases of non-tactics being added to the data
-- structure. But the module will throw errors during elaboration, and there doesn't seem to be
-- another way to implement this, because the category parser extension attribute runs *after* the
-- attributes specified before a `syntax` command.
/--
Validates that a tactic alternative is actually a tactic, that syntax tagged as tactics are
tactics, and that syntax with tactic names are tactics.
-/
private def tacticDocsOnTactics : ParserAttributeHook where
  postAdd (catName declName : Name) (_builtIn : Bool) := do
    if catName == `tactic then
      return
    if alternativeOfTactic (← getEnv) declName |>.isSome then
      throwError m!"`{.ofConstName declName}` is not a tactic"
    -- It's sufficient to look in the state (and not the imported entries) because this validation
    -- only needs to check tags added in the current module
    if let some tags := tacticTagExt.getState (← getEnv) |>.find? declName then
      if !tags.isEmpty then
        throwError m!"`{.ofConstName declName}` is not a tactic"
    if let some n := tacticNameExt.getState (← getEnv) |>.find? declName then
      throwError m!"`{MessageData.ofConstName declName}` is not a tactic, but it was assigned a tactic name `{n}`"

builtin_initialize
  registerParserAttributeHook tacticDocsOnTactics
