/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.DeclarationRange
public import Lean.Data.Options
public import Lean.DocString.Links
public import Lean.MonadEnv
public import Init.Data.String.Extra
public import Lean.DocString.Types
import Lean.DocString.Markdown

public section

-- This module contains the underlying data for docstrings, with as few imports as possible, so that
-- docstrings can be saved in as much of the compiler as possible.
-- The module `Lean.DocString` contains the query interface, which needs to look at additional data
-- to construct user-visible docstrings.

namespace Lean


/--
Saved data that describes the contents. The `name` should determine both the type of the value and
its interpretation; if in doubt, use the name of the elaborator that produces the data.
-/
structure ElabInline where
  name : Name
  val : Dynamic

private instance : Doc.MarkdownInline ElabInline where
  -- TODO extensibility
  toMarkdown go _i content := content.forM go


/--
Saved data that describes the contents. The `name` should determine both the type of the value and
its interpretation; if in doubt, use the name of the elaborator that produces the data.
-/
structure ElabBlock where
  name : Name
  value : Dynamic

-- TODO extensible toMarkdown
private instance : Doc.MarkdownBlock ElabInline ElabBlock where
  toMarkdown _goI goB _b content := content.forM goB

structure VersoDocString where
  text : Array (Doc.Block ElabInline ElabBlock)
  subsections : Array (Doc.Part ElabInline ElabBlock Empty)
deriving Inhabited

register_builtin_option doc.verso : Bool := {
  defValue := false,
  descr := "whether to use Verso syntax in docstrings"
  group := "doc"
}

private builtin_initialize builtinDocStrings : IO.Ref (NameMap String) ← IO.mkRef {}
builtin_initialize docStringExt : MapDeclarationExtension String ←
  mkMapDeclarationExtension
    (asyncMode := .async .asyncEnv)
    (exportEntriesFn := fun _ s level =>
      if level < .server then
        {}
      else
        s.toArray)
private builtin_initialize inheritDocStringExt : MapDeclarationExtension Name ←
  mkMapDeclarationExtension (exportEntriesFn := fun _ s level =>
    if level < .server then
      {}
    else
      s.toArray)

private builtin_initialize builtinVersoDocStrings : IO.Ref (NameMap VersoDocString) ← IO.mkRef {}
builtin_initialize versoDocStringExt : MapDeclarationExtension VersoDocString ←
  mkMapDeclarationExtension
    (asyncMode := .async .asyncEnv)
    (exportEntriesFn := fun _ s level =>
      if level < .server then
        {}
      else
        s.toArray)

/--
Adds a builtin docstring to the compiler.

Links to the Lean manual aren't validated.
-/
-- See the test `lean/run/docstringRewrites.lean` for the validation of builtin docstring links
def addBuiltinDocString (declName : Name) (docString : String) : IO Unit := do
  builtinDocStrings.modify (·.insert declName docString.removeLeadingSpaces)

def addDocStringCore [Monad m] [MonadError m] [MonadEnv m] [MonadLiftT BaseIO m] (declName : Name) (docString : String) : m Unit := do
  unless (← getEnv).getModuleIdxFor? declName |>.isNone do
    throwError m!"invalid doc string, declaration `{.ofConstName declName}` is in an imported module"
  modifyEnv fun env => docStringExt.insert env declName docString.removeLeadingSpaces

def addDocStringCore' [Monad m] [MonadError m] [MonadEnv m] [MonadLiftT BaseIO m] (declName : Name) (docString? : Option String) : m Unit :=
  match docString? with
  | some docString => addDocStringCore declName docString
  | none => return ()

def addInheritedDocString [Monad m] [MonadError m] [MonadEnv m] (declName target : Name) : m Unit := do
  unless (← getEnv).getModuleIdxFor? declName |>.isNone do
    throwError "invalid `[inherit_doc]` attribute, declaration `{.ofConstName declName}` is in an imported module"
  modifyEnv fun env => inheritDocStringExt.insert env declName target

/--
Finds a docstring without performing any alias resolution or enrichment with extra metadata.
For Markdown docstrings, the result is a string; for Verso docstrings, it's a `VersoDocString`.

Docstrings to be shown to a user should be looked up with `Lean.findDocString?` instead.
-/
partial def findInternalDocString? (env : Environment) (declName : Name) (includeBuiltin := true) : IO (Option (String ⊕ VersoDocString)) := do
  if let some target := inheritDocStringExt.find? (level := .server) env declName then
    return (← findInternalDocString? env target includeBuiltin)
  match docStringExt.find? (level := .server) env declName with
  | some md => return some (.inl md)
  | none => pure ()
  match versoDocStringExt.find? (level := .server) env declName with
  | some v => return some (.inr v)
  | none => pure ()
  if includeBuiltin then
    if let some docStr := (← builtinDocStrings.get).find? declName then
      return some (.inl docStr)
    else if let some doc := (← builtinVersoDocStrings.get).find? declName then
      return some (.inr doc)
  return none

/--
Finds a docstring without performing any alias resolution or enrichment with extra metadata. The
result is rendered as Markdown.

Docstrings to be shown to a user should be looked up with `Lean.findDocString?` instead.
-/
def findSimpleDocString? (env : Environment) (declName : Name) (includeBuiltin := true) : IO (Option String) := do
  match (← findInternalDocString? env declName (includeBuiltin := includeBuiltin)) with
  | some (.inl str) => return some str
  | some (.inr verso) => return some (toMarkdown verso)
  | none => return none

where
  toMarkdown : VersoDocString → String
  | .mk bs ps => Doc.MarkdownM.run' do
      for b in bs do
        Doc.ToMarkdown.toMarkdown b
      for p in ps do
        Doc.ToMarkdown.toMarkdown p


structure ModuleDoc where
  doc : String
  declarationRange : DeclarationRange

private builtin_initialize moduleDocExt : SimplePersistentEnvExtension ModuleDoc (PersistentArray ModuleDoc) ← registerSimplePersistentEnvExtension {
  addImportedFn := fun _ => {}
  addEntryFn    := fun s e => s.push e
  exportEntriesFnEx? := some fun _ _ es level =>
    if level < .server then
      #[]
    else
      es.toArray
}

def addMainModuleDoc (env : Environment) (doc : ModuleDoc) : Environment :=
  moduleDocExt.addEntry env doc

def getMainModuleDoc (env : Environment) : PersistentArray ModuleDoc :=
  moduleDocExt.getState env

def getModuleDoc? (env : Environment) (moduleName : Name) : Option (Array ModuleDoc) :=
  env.getModuleIdx? moduleName |>.map fun modIdx =>
    moduleDocExt.getModuleEntries (level := .server) env modIdx

def getDocStringText [Monad m] [MonadError m] (stx : TSyntax `Lean.Parser.Command.docComment) : m String :=
  match stx.raw[1] with
  | Syntax.atom _ val => return val.extract 0 (val.endPos - ⟨2⟩)
  | _                 => throwErrorAt stx "unexpected doc string{indentD stx.raw[1]}"
