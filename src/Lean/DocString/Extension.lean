/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.DeclarationRange
public import Lean.DocString.Markdown
public import Init.Data.String.Extra
import Init.Omega

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

instance : Repr ElabInline where
  reprPrec v _ :=
    .group <| .nestD <|
      .group (.nestD ("{ name :=" ++ .line ++ repr v.name)) ++ .line ++
      .group (.nestD ("val :=" ++ .line ++ "Dynamic.mk " ++ repr v.val.typeName ++ " _ }"))

instance : Doc.MarkdownInline ElabInline where
  -- TODO extensibility
  toMarkdown go _i content := content.forM go


/--
Saved data that describes the contents. The `name` should determine both the type of the value and
its interpretation; if in doubt, use the name of the elaborator that produces the data.
-/
structure ElabBlock where
  name : Name
  val : Dynamic

instance : Repr ElabBlock where
  reprPrec v _ :=
    .group <| .nestD <|
      .group (.nestD ("{ name :=" ++ .line ++ repr v.name)) ++ .line ++
      .group (.nestD ("val :=" ++ .line ++ "Dynamic.mk " ++ repr v.val.typeName ++ " _ }"))


-- TODO extensible toMarkdown
instance : Doc.MarkdownBlock ElabInline ElabBlock where
  toMarkdown _goI goB _b content := content.forM goB

structure VersoDocString where
  text : Array (Doc.Block ElabInline ElabBlock)
  subsections : Array (Doc.Part ElabInline ElabBlock Empty)
deriving Inhabited

register_builtin_option doc.verso : Bool := {
  defValue := false,
  descr := "whether to use Verso syntax in docstrings"
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

/--
Removes a builtin docstring from the compiler. This is used when translating between formats.
-/
def removeBuiltinDocString (declName : Name) : IO Unit := do
  builtinDocStrings.modify (·.erase declName)

/--
Retrieves all builtin Verso docstrings.
-/
def getBuiltinVersoDocStrings : IO (NameMap VersoDocString) :=
  builtinVersoDocStrings.get

def addDocStringCore [Monad m] [MonadError m] [MonadEnv m] [MonadLiftT BaseIO m] (declName : Name) (docString : String) : m Unit := do
  unless (← getEnv).getModuleIdxFor? declName |>.isNone do
    throwError m!"invalid doc string, declaration `{.ofConstName declName}` is in an imported module"
  modifyEnv fun env => docStringExt.insert env declName docString.removeLeadingSpaces

def removeDocStringCore [Monad m] [MonadError m] [MonadEnv m] [MonadLiftT BaseIO m] (declName : Name) : m Unit := do
  unless (← getEnv).getModuleIdxFor? declName |>.isNone do
    throwError m!"invalid doc string removal, declaration `{.ofConstName declName}` is in an imported module"
  modifyEnv fun env => docStringExt.modifyState env (·.erase declName) (asyncMode := .mainOnly)

def addDocStringCore' [Monad m] [MonadError m] [MonadEnv m] [MonadLiftT BaseIO m] (declName : Name) (docString? : Option String) : m Unit :=
  match docString? with
  | some docString => addDocStringCore declName docString
  | none => return ()

def addInheritedDocString [Monad m] [MonadError m] [MonadEnv m] (declName target : Name) : m Unit := do
  unless (← getEnv).getModuleIdxFor? declName |>.isNone do
    throwError "invalid `[inherit_doc]` attribute, declaration `{.ofConstName declName}` is in an imported module"
  if inheritDocStringExt.find? (level := .server) (← getEnv) declName |>.isSome then
    throwError "invalid `[inherit_doc]` attribute, declaration `{.ofConstName declName}` already has an `[inherit_doc]` attribute"
  if inheritDocStringExt.find? (level := .server) (← getEnv) target == some declName then
    throwError "invalid `[inherit_doc]` attribute, cycle detected"
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

private builtin_initialize moduleDocExt :
    SimplePersistentEnvExtension ModuleDoc (PersistentArray ModuleDoc) ← registerSimplePersistentEnvExtension {
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
  | Syntax.atom _ val =>
    return String.Pos.Raw.extract val 0 (val.rawEndPos.unoffsetBy ⟨2⟩)
  | Syntax.node _ `Lean.Parser.Command.versoCommentBody _ =>
    match stx.raw[1][0] with
    | Syntax.atom _ val =>
      return String.Pos.Raw.extract val 0 (val.rawEndPos.unoffsetBy ⟨2⟩)
    | _ =>
      throwErrorAt stx "unexpected doc string{indentD stx}"
  | _ =>
    throwErrorAt stx "unexpected doc string{indentD stx}"



/--
A snippet of a Verso module text.

A snippet consists of text followed by subsections. Because the sequence of snippets that occur in a
source file are conceptually a single document, they have a consistent header nesting structure.
This means that initial textual content of a snippet is a continuation of the text at the end of the
prior snippet.

The actual hierarchical structure of the document is reconstructed from the sequence of snippets.

The _terminal nesting_ of a sequence of snippets is 0 if there are no sections in the sequence.
Otherwise, it is one greater than the nesting of the last snippet's last section. The module
docstring elaborator maintains the invariant that each snippet's first section's level is at most
the terminal nesting of the preceding snippets, and that the level of each section within a snippet
is at most one greater than the preceding section's level.
-/
structure VersoModuleDocs.Snippet where
  /-- Text to be inserted after the prior snippet's ending text. -/
  text : Array (Doc.Block ElabInline ElabBlock) := #[]
  /--
  A sequence of parts with their absolute document nesting levels and header positions.
  None of these parts may contain sub-parts.
  -/
  sections : Array (Nat × DeclarationRange × Doc.Part ElabInline ElabBlock Empty) := #[]
  /--
  The location of the snippet in the source file.
  -/
  declarationRange : DeclarationRange
deriving Inhabited, Repr

namespace VersoModuleDocs.Snippet

def canNestIn (level : Nat) (snippet : Snippet) : Bool :=
  if let some s := snippet.sections[0]? then s.1 ≤ level + 1 else true

def terminalNesting (snippet : Snippet) : Option Nat :=
  if let some s := snippet.sections.back? then s.1
  else none

def addBlock (snippet : Snippet) (block : Doc.Block ElabInline ElabBlock) : Snippet :=
  if h : snippet.sections.size = 0 then
    { snippet with text := snippet.text.push block }
  else
    { snippet with
      sections[snippet.sections.size - 1].2.2.content :=
        snippet.sections[snippet.sections.size - 1].2.2.content.push block }

def addPart (snippet : Snippet) (level : Nat) (range : DeclarationRange) (part : Doc.Part ElabInline ElabBlock Empty) : Snippet :=
  { snippet with
    sections := snippet.sections.push (level, range, part) }

end VersoModuleDocs.Snippet

open Lean Doc ToMarkdown MarkdownM in
instance : ToMarkdown VersoModuleDocs.Snippet where
  toMarkdown
    | {text, sections, ..} => do
      text.forM toMarkdown
      endBlock
      for (level, _, part) in sections do
        push ("".pushn '#' (level + 1))
        push " "
        for i in part.title do toMarkdown i
        endBlock
        for b in part.content do toMarkdown b
        endBlock

structure VersoModuleDocs where
  snippets : PersistentArray VersoModuleDocs.Snippet := {}
  terminalNesting : Option Nat := snippets.findSomeRev? (·.terminalNesting)
deriving Inhabited

instance : Repr VersoModuleDocs where
  reprPrec v _ :=
    .group <| .nest 2 <|
      "{ " ++
      (.group <| .nest 2 <| "snippets := " ++ .line ++ repr v.snippets.toArray) ++ .line ++
      (.group <| .nest 2 <| "snippets := " ++ .line ++ repr v.snippets.toArray) ++
      " }"

namespace VersoModuleDocs

def isEmpty (docs : VersoModuleDocs) : Bool := docs.snippets.isEmpty

def canAdd (docs : VersoModuleDocs) (snippet : Snippet) : Bool :=
  if let some level := docs.terminalNesting then
    snippet.canNestIn level
  else true


def add (docs : VersoModuleDocs) (snippet : Snippet) : Except String VersoModuleDocs := do
  unless docs.canAdd snippet do
    throw "Can't nest this snippet here"

  return { docs with
    snippets := docs.snippets.push snippet,
    terminalNesting := snippet.terminalNesting
  }

def add! (docs : VersoModuleDocs) (snippet : Snippet) : VersoModuleDocs :=
  let ok :=
    if let some level := docs.terminalNesting then
      snippet.canNestIn level
    else true
  if not ok then
    panic! "Can't nest this snippet here"
  else
    { docs with
      snippets := docs.snippets.push snippet,
      terminalNesting := snippet.terminalNesting
    }


private structure DocFrame where
  content : Array (Doc.Block ElabInline ElabBlock)
  priorParts : Array (Doc.Part ElabInline ElabBlock Empty)
  titleString : String
  title : Array (Doc.Inline ElabInline)

private structure DocContext where
  content : Array (Doc.Block ElabInline ElabBlock)
  priorParts : Array (Doc.Part ElabInline ElabBlock Empty)
  context : Array DocFrame

private def DocContext.level (ctx : DocContext) : Nat := ctx.context.size

private def DocContext.close (ctx : DocContext) : Except String DocContext := do
  if h : ctx.context.size = 0 then
    throw "Can't close a section: none are open"
  else
    let last := ctx.context.back
    pure {
      content := last.content,
      priorParts := last.priorParts.push {
        title := last.title,
        titleString := last.titleString,
        metadata := none,
        content := ctx.content,
        subParts := ctx.priorParts,
      },
      context := ctx.context.pop
    }

private partial def DocContext.closeAll (ctx : DocContext) : Except String DocContext := do
  if ctx.context.size = 0 then
    return ctx
  else
    (← ctx.close).closeAll

private partial def DocContext.addPart (ctx : DocContext) (partLevel : Nat) (part : Doc.Part ElabInline ElabBlock Empty) : Except String DocContext := do
  if partLevel > ctx.level then throw s!"Invalid nesting: expected at most {ctx.level} but got {partLevel}"
  else if partLevel = ctx.level then pure { ctx with priorParts := ctx.priorParts.push part }
  else
    let ctx ← ctx.close
    ctx.addPart partLevel part

private def DocContext.addBlocks (ctx : DocContext) (blocks : Array (Doc.Block ElabInline ElabBlock)) : Except String DocContext := do
  if ctx.priorParts.isEmpty then pure { ctx with content := ctx.content ++ blocks }
  else throw "Can't add content after sub-parts"

private def DocContext.addSnippet (ctx : DocContext) (snippet : Snippet) : Except String DocContext := do
  let mut ctx ← ctx.addBlocks snippet.text
  for (l, _, p) in snippet.sections do
    ctx ← ctx.addPart l p
  return ctx

def assemble (docs : VersoModuleDocs) : Except String VersoDocString := do
  let mut ctx : DocContext := {content := #[], priorParts := #[], context := #[]}
  for snippet in docs.snippets do
    ctx ← ctx.addSnippet snippet
  ctx ← ctx.closeAll
  return { text := ctx.content, subsections := ctx.priorParts }

end VersoModuleDocs

private builtin_initialize versoModuleDocExt :
    SimplePersistentEnvExtension VersoModuleDocs.Snippet VersoModuleDocs ← registerSimplePersistentEnvExtension {
  addImportedFn := fun _ => {}
  addEntryFn    := fun s e => s.add! e
  exportEntriesFnEx? := some fun _ _ es level =>
    if level < .server then
      #[]
    else
      es.toArray
}


/--
Returns the Verso module docs for the current main module.

During elaboration, this will return the modules docs that have been added thus far, rather than
those for the entire module.
-/
def getMainVersoModuleDocs (env : Environment) : VersoModuleDocs :=
  versoModuleDocExt.getState env

@[deprecated getMainVersoModuleDocs (since := "2026-01-21")]
def getVersoModuleDocs := @getMainVersoModuleDocs


/--
Returns all snippets of the Verso module docs from the indicated module, if they exist.
-/
def getVersoModuleDoc? (env : Environment) (moduleName : Name) :
    Option (Array VersoModuleDocs.Snippet) :=
  env.getModuleIdx? moduleName |>.map fun modIdx =>
    versoModuleDocExt.getModuleEntries (level := .server) env modIdx

def addVersoModuleDocSnippet (env : Environment) (snippet : VersoModuleDocs.Snippet) : Except String Environment :=
  let docs := getMainVersoModuleDocs env
  if docs.canAdd snippet then
    pure <| versoModuleDocExt.addEntry env snippet
  else throw s!"Can't add - incorrect nesting {docs.terminalNesting.map (s!"(expected at most {·})") |>.getD ""})"
