/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Thrane Christiansen
-/

module

prelude
import Lean.Environment
import Lean.Exception
import Lean.Log
import Lean.Elab.DocString
import Lean.DocString.Extension
import Lean.DocString.Links
import Lean.Parser.Types
public import Lean.DocString.Parser
import Lean.ResolveName
public import Lean.Elab.Term.TermElabM
import Std.Data.HashMap

public section

set_option linter.missingDocs true

namespace Lean

open Lean.Elab.Term (TermElabM)

/--
Validates all links to the Lean reference manual in `docstring`.

This is intended to be used before saving a docstring that is later subject to rewriting with
`rewriteManualLinks`.
-/
def validateDocComment
    [Monad m] [MonadLiftT IO m] [MonadLog m] [AddMessageContext m] [MonadOptions m]
    (docstring : TSyntax `Lean.Parser.Command.docComment) :
    m Unit := do
  let str := docstring.getDocString
  let pos? := docstring.raw[1].getHeadInfo? >>= (·.getPos?)

  let (errs, out) ← (rewriteManualLinksCore str : IO _)

  for (⟨start, stop⟩, err) in errs do
    -- Report errors at their actual location if possible
    if let some pos := pos? then
      let urlStx : Syntax := .atom (.synthetic (pos + start) (pos + stop)) (str.extract start stop)
      logErrorAt urlStx err
    else
      logError err

open Lean.Parser Command in
/--
Parses a docstring as Verso, returning the syntax if successful.

When not successful, parser errors are logged.
-/
def parseVersoDocString
    [Monad m] [MonadFileMap m] [MonadError m] [MonadEnv m] [MonadOptions m] [MonadLog m]
    [MonadResolveName m]
    (docComment : TSyntax [``docComment, ``moduleDoc]) : m (Option Syntax) := do
  if docComment.raw.getKind == ``docComment then
    match docComment.raw[0] with
    | docStx@(.node _ ``versoCommentBody _) => return docStx[1]?
    | _ => pure ()
  let text ← getFileMap
  -- TODO fallback to string version without nice interactivity
  let some startPos := docComment.raw[1].getPos? (canonicalOnly := true)
    | throwErrorAt docComment m!"Documentation comment has no source location, cannot parse"
  let some endPos := docComment.raw[1].getTailPos? (canonicalOnly := true)
    | throwErrorAt docComment m!"Documentation comment has no source location, cannot parse"

  -- Skip trailing `-/`
  let endPos := text.source.prev <| text.source.prev endPos
  let endPos := if endPos ≤ text.source.endPos then endPos else text.source.endPos
  have endPos_valid : endPos ≤ text.source.endPos := by
    unfold endPos
    split <;> simp [*]

  let env ← getEnv
  let ictx : InputContext :=
    .mk text.source (← getFileName) (fileMap := text)
      (endPos := endPos) (endPos_valid := endPos_valid)
  let pmctx : ParserModuleContext := {
    env,
    options := ← getOptions,
    currNamespace := (← getCurrNamespace),
    openDecls := (← getOpenDecls)
  }
  let s := mkParserState text.source |>.setPos startPos
  -- TODO parse one block at a time for error recovery purposes
  let s := Doc.Parser.document.run ictx pmctx (getTokenTable env) s

  if !s.allErrors.isEmpty then
    for (pos, _, err) in s.allErrors do
      logMessage {
        fileName := (← getFileName),
        pos := text.toPosition pos,
        -- TODO end position
        data := err.toString
      }
    return none
  return some s.stxStack.back



open Lean.Doc in
open Lean.Parser.Command in
/--
Elaborates a Verso docstring for the specified declaration, which should already be present in the
environment.

`binders` should be the syntax of the parameters to the constant that is being documented, as a null
node that contains a sequence of bracketed binders. It is used to allow interactive features such as
document highlights and “find references” to work for documented parameters. If no parameter binders
are available, pass `Syntax.missing` or an empty null node.
-/

def versoDocString
    (declName : Name) (binders : Syntax) (docComment : TSyntax ``docComment) :
    TermElabM (Array (Doc.Block ElabInline ElabBlock) × Array (Doc.Part ElabInline ElabBlock Empty)) := do
  if let some stx ← parseVersoDocString docComment then
    Doc.elabBlocks (stx.getArgs.map (⟨·⟩)) |>.exec declName binders
  else return (#[], #[])

open Lean.Doc Parser in
open Lean.Parser.Command in
/--
Parses and elaborates a Verso module docstring.
-/
def versoModDocString
    (range : DeclarationRange) (doc : TSyntax ``document) :
    TermElabM VersoModuleDocs.Snippet := do
  let level := getVersoModuleDocs (← getEnv) |>.terminalNesting |>.map (· + 1)
  Doc.elabModSnippet range (doc.raw.getArgs.map (⟨·⟩)) (level.getD 0) |>.execForModule



open Lean.Doc in
open Parser in
/--
Adds a Verso docstring to the specified declaration, which should already be present in the
environment. The docstring is added from a string value, rather than syntax, which means that the
interactive features are disabled.
-/
def versoDocStringFromString
    (declName : Name) (docComment : String) :
    TermElabM (Array (Doc.Block ElabInline ElabBlock) × Array (Doc.Part ElabInline ElabBlock Empty)) := do

  let env ← getEnv
  let ictx : InputContext := .mk docComment (← getFileName)
  let text := ictx.fileMap
  let pmctx : ParserModuleContext := {
    env,
    options := ← getOptions,
    currNamespace := (← getCurrNamespace),
    openDecls := (← getOpenDecls)
  }
  let s := mkParserState docComment
  -- TODO parse one block at a time for error recovery purposes
  let s := Doc.Parser.document.run ictx pmctx (getTokenTable env) s

  if !s.allErrors.isEmpty then
    for (pos, _, err) in s.allErrors do
      logError err.toString
    return (#[], #[])
  else
    let stx := s.stxStack.back
    let stx := stx.getArgs
    let msgs ← Core.getAndEmptyMessageLog
    let (val, msgs') ←
      try
        let range? := (← getRef).getRange?
        let val ←
          Elab.withEnableInfoTree false <| withTheReader Core.Context ({· with fileMap := text}) <|
            (Doc.elabBlocks (stx.map (⟨·⟩))).exec declName (mkNullNode #[]) (suggestionMode := .batch)
        let msgs' ← Core.getAndEmptyMessageLog
        pure (val, msgs')
      finally
        Core.setMessageLog msgs
    -- Adjust messages to show them at the call site
    for msg in msgs'.toArray do
      logAt (← getRef) msg.data (severity := msg.severity)
    pure val

/--
Adds a Markdown docstring to the environment, validating documentation links.
-/
def addMarkdownDocString
    [Monad m] [MonadLiftT IO m] [MonadOptions m] [MonadEnv m]
    [MonadError m] [MonadLog m] [AddMessageContext m]
    (declName : Name) (docComment : TSyntax `Lean.Parser.Command.docComment) :
    m Unit := do
  if declName.isAnonymous then
    -- This case might happen on partial elaboration; ignore instead of triggering any panics below
    return
  unless (← getEnv).getModuleIdxFor? declName |>.isNone do
    throwError m!"invalid doc string, declaration `{.ofConstName declName}` is in an imported module"
  validateDocComment docComment
  let docString : String ← getDocStringText docComment
  modifyEnv fun env => docStringExt.insert env declName docString.removeLeadingSpaces

/--
Adds an elaborated Verso docstring to the environment.
-/
def addVersoDocStringCore [Monad m] [MonadEnv m] [MonadLiftT BaseIO m] [MonadError m]
    (declName : Name) (docs : VersoDocString) : m Unit := do
  -- The decl name can be anonymous due to attempts to elaborate incomplete syntax. If the name is
  -- anonymous, the `MapDeclarationExtension.insert` panics due to not being on the right async
  -- branch. Better to just do nothing.
  if declName.isAnonymous then return
  unless (← getEnv).getModuleIdxFor? declName |>.isNone do
    throwError s!"invalid doc string, declaration '{declName}' is in an imported module"
  modifyEnv fun env =>
    versoDocStringExt.insert env declName docs

/--
Adds an elaborated Verso module docstring to the environment.
-/
def addVersoModDocStringCore [Monad m] [MonadEnv m] [MonadLiftT BaseIO m] [MonadError m]
  (docs : VersoModuleDocs.Snippet) : m Unit := do
  if (getMainModuleDoc (← getEnv)).isEmpty then
    match addVersoModuleDocSnippet (← getEnv) docs with
    | .error e => throwError "Error adding module docs: {indentD <| toMessageData e}"
    | .ok env' => setEnv env'
  else
    throwError m!"Can't add Verso-format module docs because there is already Markdown-format content present."

open Lean.Parser.Command in
/--
Adds a Verso docstring to the environment.

`binders` should be the syntax of the parameters to the constant that is being documented, as a null
node that contains a sequence of bracketed binders. It is used to allow interactive features such as
document highlights and “find references” to work for documented parameters. If no parameter binders
are available, pass `Syntax.missing` or an empty null node.
-/
def addVersoDocString
    (declName : Name) (binders : Syntax) (docComment : TSyntax ``docComment) :
    TermElabM Unit := do
  unless (← getEnv).getModuleIdxFor? declName |>.isNone do
    throwError s!"invalid doc string, declaration '{declName}' is in an imported module"
  let (blocks, parts) ← versoDocString declName binders docComment
  addVersoDocStringCore declName ⟨blocks, parts⟩

/--
Adds a Verso docstring to the environment from a string value, which disables the interactive
features. This should be used for programs that add documentation when there is no syntax available.
-/
def addVersoDocStringFromString (declName : Name) (docComment : String) :
    TermElabM Unit := do
  unless (← getEnv).getModuleIdxFor? declName |>.isNone do
    throwError s!"invalid doc string, declaration '{declName}' is in an imported module"
  let (blocks, parts) ← versoDocStringFromString declName docComment
  addVersoDocStringCore declName ⟨blocks, parts⟩


/--
Adds a docstring to the environment. If `isVerso` is `false`, then the docstring is interpreted as
Markdown.
-/
def addDocStringOf
    (isVerso : Bool) (declName : Name) (binders : Syntax)
    (docComment : TSyntax `Lean.Parser.Command.docComment) :
    TermElabM Unit := do
  if isVerso then
    addVersoDocString declName binders docComment
  else
    addMarkdownDocString declName docComment

/--
Interprets a docstring that has been saved as a Markdown string as Verso, elaborating it. This is
used during bootstrapping.
-/
def makeDocStringVerso (declName : Name) : TermElabM Unit := do
  let some doc ← findInternalDocString? (← getEnv) declName (includeBuiltin := true)
    | throwError "No documentation found for `{.ofConstName declName}`"
  let .inl md := doc
    | throwError "Documentation for `{.ofConstName declName}` is already in Verso format"
  removeBuiltinDocString declName
  removeDocStringCore declName
  addVersoDocStringFromString declName md

/--
Adds a docstring to the environment.

If the option `doc.verso` is `true`, the docstring is processed as a Verso docstring. Otherwise, it
is considered a Markdown docstring, and documentation links are validated. To explicitly control
whether the docstring is in Verso format, use `addDocStringOf` instead.

For Verso docstrings, `binders` should be the syntax of the parameters to the constant that is being
documented, as a null node that contains a sequence of bracketed binders. It is used to allow
interactive features such as document highlights and “find references” to work for documented
parameters. If no parameter binders are available, pass `Syntax.missing` or an empty null node.
`binders` is not used for Markdown docstrings.
-/
def addDocString
    (declName : Name) (binders : Syntax) (docComment : TSyntax `Lean.Parser.Command.docComment) :
    TermElabM Unit := do
  addDocStringOf (doc.verso.get (← getOptions)) declName binders docComment

/--
Adds a docstring to the environment, if it is provided. If no docstring is provided, nothing
happens.

If the option `doc.verso` is `true`, the docstring is processed as a Verso docstring. Otherwise, it
is considered a Markdown docstring, and documentation links are validated. To explicitly control
whether the docstring is in Verso format, use `addDocStringOf` instead.

For Verso docstrings, `binders` should be the syntax of the parameters to the constant that is being
documented, as a null node that contains a sequence of bracketed binders. It is used to allow
interactive features such as document highlights and “find references” to work for documented
parameters. If no parameter binders are available, pass `Syntax.missing` or an empty null node.
`binders` is not used for Markdown docstrings.

-/
def addDocString'
    (declName : Name) (binders : Syntax) (docString? : Option (TSyntax `Lean.Parser.Command.docComment)) :
    TermElabM Unit :=
  match docString? with
  | some docString => addDocString declName binders docString
  | none => return ()


open Lean.Parser.Command in
open Lean.Doc.Parser in
/--
Adds a Verso docstring to the environment.

`binders` should be the syntax of the parameters to the constant that is being documented, as a null
node that contains a sequence of bracketed binders. It is used to allow interactive features such as
document highlights and “find references” to work for documented parameters. If no parameter binders
are available, pass `Syntax.missing` or an empty null node.
-/
def addVersoModDocString
    (range : DeclarationRange) (docComment : TSyntax ``document) :
    TermElabM Unit := do
  let snippet ← versoModDocString range docComment
  addVersoModDocStringCore snippet
