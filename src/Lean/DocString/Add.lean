/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Thrane Christiansen
-/

module

prelude
import Lean.Elab.DocString
public import Lean.DocString.Parser
public import Lean.Elab.Term.TermElabM

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
      let urlStx : Syntax := .atom (.synthetic (start.offsetBy pos) (stop.offsetBy pos)) (String.Pos.Raw.extract str start stop)
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
  let endPos := String.Pos.Raw.prev text.source <| endPos.prev text.source
  let endPos := if endPos ≤ text.source.rawEndPos then endPos else text.source.rawEndPos
  have endPos_valid : endPos ≤ text.source.rawEndPos := by
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
  let blockCtxt := .forDocString text startPos endPos
  let s := mkParserState text.source |>.setPos startPos
  -- TODO parse one block at a time for error recovery purposes
  let s := (Doc.Parser.document blockCtxt).run ictx pmctx (getTokenTable env) s

  -- If document succeeded but didn't consume everything, try parsing a block at the stopped
  -- position to get the actual error message (document uses sepByFn which swallows errors).
  let s :=
    if s.allErrors.isEmpty && !ictx.atEnd s.pos then
      (Doc.Parser.block {}).run ictx pmctx (getTokenTable env) (mkParserState text.source |>.setPos s.pos)
    else s
  if !s.allErrors.isEmpty then
    for (pos, _, err) in s.allErrors do
      logMessage {
        fileName := (← getFileName),
        pos := text.toPosition pos,
        -- TODO end position
        data := err.toString
      }
    return none
  if !ictx.atEnd s.pos then
    -- Fallback: block parse also didn't produce an error
    logMessage {
      fileName := (← getFileName),
      pos := text.toPosition s.pos,
      data := s!"unexpected '{ictx.get s.pos}'"
    }
    return none
  return some s.stxStack.back



open Lean.Parser Command in
/--
Reports parse errors from a Verso docstring parse failure.

When Verso docstring parsing fails at parse time, a `parseFailure` node is created containing the
raw text, because emitting an error at that stage could lead to unwanted parser backtracking. This
function reports the actual error messages with proper source positions.
-/
def reportVersoParseFailure
    [Monad m] [MonadFileMap m] [MonadError m] [MonadEnv m] [MonadOptions m] [MonadLog m]
    [MonadResolveName m]
    (parseFailure : Syntax) : m Unit := do
  let some rawAtom := parseFailure[0]?
    | return  -- malformed node, nothing to report
  let some startPos := rawAtom.getPos? (canonicalOnly := true)
    | return
  let some endPos := rawAtom.getTailPos? (canonicalOnly := true)
    | return

  let text ← getFileMap
  let endPos := if endPos ≤ text.source.rawEndPos then endPos else text.source.rawEndPos
  have endPos_valid : endPos ≤ text.source.rawEndPos := by
    unfold endPos; split <;> simp [*]

  let env ← getEnv
  let ictx : InputContext :=
    .mk text.source (← getFileName) (fileMap := text)
      (endPos := endPos) (endPos_valid := endPos_valid)
  let pmctx : ParserModuleContext := {
    env,
    options := ← getOptions,
    currNamespace := ← getCurrNamespace,
    openDecls := ← getOpenDecls
  }
  let blockCtxt := Doc.Parser.BlockCtxt.forDocString text startPos endPos
  let s := mkParserState text.source |>.setPos startPos
  let s := (Doc.Parser.document blockCtxt).run ictx pmctx (getTokenTable env) s

  -- If document succeeded but didn't consume everything, try parsing a block at the stopped
  -- position to get the actual error message (document uses sepByFn which swallows errors).
  let s :=
    if s.allErrors.isEmpty && !ictx.atEnd s.pos then
      (Doc.Parser.block {}).run ictx pmctx (getTokenTable env) (mkParserState text.source |>.setPos s.pos)
    else s
  for (pos, _, err) in s.allErrors do
    logMessage {
      fileName := ← getFileName,
      pos := text.toPosition pos,
      data := err.toString,
      severity := .error
    }
  if s.allErrors.isEmpty && !ictx.atEnd s.pos then
    -- Fallback: block parse also didn't produce an error
    logMessage {
      fileName := ← getFileName,
      pos := text.toPosition s.pos,
      data := s!"unexpected '{ictx.get s.pos}'",
      severity := .error
    }

open Lean.Doc in
/--
Elaborates already-parsed Verso `blocks` for the specified declaration with interactive features
disabled, reporting any elaboration messages at the current reference. When `fileMap?` is provided,
message positions are interpreted against it.
-/
private def execVersoBlocks
    (declName : Name) (binders : Syntax) (blocks : Array Syntax) (fileMap? : Option FileMap) :
    TermElabM (Array (Doc.Block ElabInline ElabBlock) × Array (Doc.Part ElabInline ElabBlock Empty)) := do
  let msgs ← Core.getAndEmptyMessageLog
  let (val, msgs') ←
    try
      let act := (Doc.elabBlocks (blocks.map (⟨·⟩))).exec declName binders (suggestionMode := .batch)
      let val ←
        Elab.withEnableInfoTree false <|
          match fileMap? with
          | some fileMap => withTheReader Core.Context ({· with fileMap }) act
          | none => act
      pure (val, ← Core.getAndEmptyMessageLog)
    finally
      Core.setMessageLog msgs
  for msg in msgs'.toArray do
    logAt (← getRef) msg.data (severity := msg.severity) (isSilent := msg.isSilent)
  pure val

open Lean.Doc in
open Parser in
/--
Parses a Verso docstring from its text and elaborates it for the specified declaration. Because the
text carries no source positions, interactive features are disabled and any messages are reported at
the current reference.

`binders` should be the syntax of the parameters to the constant that is being documented, as a null
node that contains a sequence of bracketed binders, or an empty null node when none are available.
-/
def versoDocStringOfText
    (declName : Name) (binders : Syntax) (docComment : String) :
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
    for (_, _, err) in s.allErrors do
      logError err.toString
    return (#[], #[])
  else
    execVersoBlocks declName binders s.stxStack.back.getArgs (fileMap? := some text)

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
  -- A docstring already parsed as Verso, or one re-parsable from its source range, supports
  -- interactive features. A macro-generated docstring has neither, so fall back to its text.
  let body := docComment.raw[1]
  if (body.getPos? (canonicalOnly := true)).isSome then
    -- Source positions are available, so re-parse from source for interactive features.
    if let some stx ← parseVersoDocString docComment then
      Doc.elabBlocks (stx.getArgs.map (⟨·⟩)) |>.exec declName binders
    else return (#[], #[])
  else if body.isOfKind ``versoCommentBody then
    if body[0].isOfKind `Lean.Doc.Syntax.parseFailure then
      -- The markup failed to parse, so re-parse its text to report the error.
      versoDocStringOfText declName binders body[0][0].getAtomVal
    else
      -- A docstring parsed as Verso by a macro, with positions stripped.
      execVersoBlocks declName binders body[0].getArgs (fileMap? := none)
  else
    -- A plain-text doc comment without source positions; parse and elaborate from its text.
    versoDocStringOfText declName binders docComment.getDocString

open Lean.Doc Parser in
open Lean.Parser.Command in
/--
Parses and elaborates a Verso module docstring.
-/
def versoModDocString
    (range : DeclarationRange) (doc : TSyntax ``document) :
    TermElabM VersoModuleDocs.Snippet := do
  let level := getMainVersoModuleDocs (← getEnv) |>.terminalNesting |>.map (· + 1)
  Doc.elabModSnippet range (doc.raw.getArgs.map (⟨·⟩)) (level.getD 0) |>.execForModule



/--
Adds a Verso docstring to the specified declaration, which should already be present in the
environment. The docstring is added from a string value, rather than syntax, which means that the
interactive features are disabled.
-/
def versoDocStringFromString
    (declName : Name) (docComment : String) :
    TermElabM (Array (Doc.Block ElabInline ElabBlock) × Array (Doc.Part ElabInline ElabBlock Empty)) :=
  versoDocStringOfText declName (mkNullNode #[]) docComment

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

Whether the docstring is processed as Verso or as Markdown is determined by the form of its syntax
tree. To explicitly control whether the docstring is in Verso format, use `addDocStringOf` instead.

Markdown docstrings have their documentation links validated.

For Verso docstrings, `binders` should be the syntax of the parameters to the constant that is being
documented, as a null node that contains a sequence of bracketed binders. It is used to allow
interactive features such as document highlights and “find references” to work for documented
parameters. If no parameter binders are available, pass `Syntax.missing` or an empty null node.
`binders` is not used for Markdown docstrings.
-/
def addDocString
    (declName : Name) (binders : Syntax) (docComment : TSyntax `Lean.Parser.Command.docComment) :
    TermElabM Unit := do
  addDocStringOf (isVersoDocComment docComment) declName binders docComment

/--
Adds a docstring to the environment, if it is provided. If no docstring is provided, nothing
happens.

Whether the docstring is processed as Verso or as Markdown is determined by its syntax tree, which
reflects the `doc.verso` option at the docstring's parse site.  To explicitly control whether the
docstring is in Verso format, use `addDocStringOf` instead.

Markdown docstrings have their documentation links validated.

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
