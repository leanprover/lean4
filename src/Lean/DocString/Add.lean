/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Thrane Christiansen
-/

module

prelude
import Lean.Elab.DocString
public import Lean.DocString.DeferredCheck
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

open Lean.Parser in
/-- Builds the message for a Verso parse error. -/
private def mkVersoParseMessage (ictx : InputContext) (pos : String.Pos.Raw) (e : Parser.Error) :
    Message :=
  let (pos, endPos?, e) := Doc.Parser.locateError ictx pos e
  { fileName := ictx.fileName
    pos := ictx.fileMap.toPosition pos
    endPos := endPos?.map ictx.fileMap.toPosition
    keepFullRange := true
    data := toString e }

open Lean.Parser in
/--
The errors to report for a document parse that ended at `s`.

`documentFn` is built on `sepByFn`, which stops at the first block that does not parse and discards
its error. Reading a block again at the position where it stopped recovers that error, so `ctxt`
is the context the document was parsed with.
-/
private def parseErrors
    (ictx : InputContext) (pmctx : ParserModuleContext) (tokens : TokenTable)
    (input : String) (ctxt : Doc.Parser.BlockCtxt) (s : ParserState) :
    Array (String.Pos.Raw × SyntaxStack × Error) :=
  if s.allErrors.isEmpty && !ictx.atEnd s.pos then
    ((Doc.Parser.blockFn ctxt).run ictx pmctx tokens (mkParserState input |>.setPos s.pos)).allErrors
  else s.allErrors

open Lean.Doc in
/--
The markup of a Verso doc comment.

Parsing may have succeeded or failed, and the two cases are distinct.

Lean's docstring parser records an error in Verso syntax as a parse failure node rather than
emitting a failure so that syntax errors in docstrings don't break processing of their associated
definitions.
-/
inductive VersoDocstringMarkup where
  /-- Markup that parsed. -/
  | document (doc : VersoDocument)
  /--
  Markup that did not parse. `text` is the content that was actually sent to the parser, excluding
  opening and closing docstring delimiters.
  -/
  | parseFailure (text : Syntax)

/-- The syntax that covers the markup, whether or not it parsed. -/
def VersoDocstringMarkup.stx : VersoDocstringMarkup → Syntax
  | .document doc => doc.raw
  | .parseFailure text => text

/--
A view of a Verso doc comment: its delimiters and the markup between them.
-/
structure VersoDocstringView where
  /-- The token that opens the comment. -/
  opener : Syntax
  /-- The markup between the delimiters. -/
  markup : VersoDocstringMarkup
  /-- The token that closes the comment. -/
  closer : Syntax

open Lean.Parser Command in
/--
Views a Verso documentation comment as its delimiters and the markup between them.

The comment's body must have been parsed as Verso markup, which `isVersoDocComment` reports.
-/
def VersoDocstringView.of (docComment : TSyntax [``docComment, ``moduleDoc]) : VersoDocstringView :=
  let body := docComment.raw[1]
  { opener := docComment.raw[0]
    markup :=
      if body[0].isOfKind `Lean.Doc.Syntax.parseFailure then .parseFailure body[0][0]
      else .document ⟨body[0]⟩
    closer := body[1] }

/--
The report for a documentation comment that cannot be parsed because the part `what` names has no
source position.
-/
private def noSourceLocation (what : String) : MessageData :=
  m!"The {what} of this documentation comment has no source location, so it cannot be parsed."

/--
The source positions a Verso docstring is parsed from: its opening delimiter, the start of its
markup, and its closing delimiter. If any are missing original or canonical source, an error
is thrown.
-/
private def docCommentRange (view : VersoDocstringView) :
    Except MessageData (String.Pos.Raw × String.Pos.Raw × String.Pos.Raw) := do
  let some openPos := view.opener.getPos? (canonicalOnly := true)
    | throw (noSourceLocation "opening delimiter")
  let some startPos := view.markup.stx.getPos? (canonicalOnly := true)
    | throw (noSourceLocation "content")
  let some endPos := view.closer.getPos? (canonicalOnly := true)
    | throw (noSourceLocation "closing delimiter")
  return (openPos, startPos, endPos)

open Lean.Parser Command in
/--
The source positions of a docstring whose body was parsed as Markdown: its opening delimiter, the
start of its text, and its closing delimiter.

Such a body is one token that runs through the closing delimiter, so that delimiter comes off the
end of the token rather than from a token of its own.
-/
private def markdownCommentRange (source : String)
    (docComment : TSyntax [``docComment, ``moduleDoc]) :
    Except MessageData (String.Pos.Raw × String.Pos.Raw × String.Pos.Raw) := do
  let some openPos := docComment.raw[0].getPos? (canonicalOnly := true)
    | throw (noSourceLocation "opening delimiter")
  let some startPos := docComment.raw[1].getPos? (canonicalOnly := true)
    | throw (noSourceLocation "content")
  let some contentEnd := docComment.raw[1].getTailPos? (canonicalOnly := true)
    | throw (noSourceLocation "content")
  return (openPos, startPos, String.Pos.Raw.prev source <| contentEnd.prev source)

open Lean.Parser Command in
/--
The source positions a docstring is read from. Only the closing delimiter is found differently: a
body parsed as Verso markup has it as a token of its own, while one parsed as Markdown includes the
closing delimiter in the body token.
-/
private def docStringRange (source : String) (docComment : TSyntax [``docComment, ``moduleDoc]) :
    Except MessageData (String.Pos.Raw × String.Pos.Raw × String.Pos.Raw) :=
  if docComment.raw[1].isOfKind ``versoCommentBody then docCommentRange (.of docComment)
  else markdownCommentRange source docComment

open Lean.Doc in
open Lean.Parser Command in
/--
Parses a docstring as Verso, returning the syntax if successful.

When not successful, parser errors are logged.
-/
def parseVersoDocString
    [Monad m] [MonadFileMap m] [MonadError m] [MonadEnv m] [MonadOptions m] [MonadLog m]
    [MonadResolveName m]
    (docComment : TSyntax [``docComment, ``moduleDoc]) :
    m (Option VersoDocument) := do
  let text ← getFileMap
  -- TODO fallback to string version without nice interactivity
  let (openPos, startPos, endPos) ←
    match docStringRange text.source docComment with
    | .ok range => pure range
    | .error msg => throwError msg

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
  let blockCtxt := .forDocString text openPos startPos endPos
  let s := mkParserState text.source |>.setPos startPos
  -- TODO parse one block at a time for error recovery purposes
  let s := (Doc.Parser.documentFn blockCtxt).run ictx pmctx (getTokenTable env) s

  let errors := parseErrors ictx pmctx (getTokenTable env) text.source blockCtxt s
  if !errors.isEmpty then
    for (pos, _, err) in errors do
      logMessage (mkVersoParseMessage ictx pos err)
    return none
  if !ictx.atEnd s.pos then
    -- Reading a block at the stopped position reported nothing, so the character there is named.
    logMessage {
      fileName := (← getFileName),
      pos := text.toPosition s.pos,
      data := s!"unexpected '{ictx.get s.pos}'"
    }
    return none
  return some ⟨s.stxStack.back⟩



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
    (view : VersoDocstringView) : m Unit := do
  let (openPos, startPos, endPos) ←
    match docCommentRange view with
    | .ok range => pure range
    | .error msg => throwError msg

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
  let blockCtxt := Doc.Parser.BlockCtxt.forDocString text openPos startPos endPos
  let s := mkParserState text.source |>.setPos startPos
  let s := (Doc.Parser.documentFn blockCtxt).run ictx pmctx (getTokenTable env) s

  let errors := parseErrors ictx pmctx (getTokenTable env) text.source blockCtxt s
  for (pos, _, err) in errors do
    logMessage (mkVersoParseMessage ictx pos err)
  if errors.isEmpty && !ictx.atEnd s.pos then
    -- Reading a block at the stopped position reported nothing, so the character there is named.
    logMessage {
      fileName := ← getFileName,
      pos := text.toPosition s.pos,
      data := s!"unexpected '{ictx.get s.pos}'",
      severity := .error
    }

open Lean.Doc in
/--
The result of elaborating a Verso docstring, which consists of the docstring contents paired with a
set of deferred checks.
-/
public structure VersoDocResult extends VersoDocString where
  /--
  Checks that cannot be carried out during elaboration, typically because they require information
  that is not yet available.
  -/
  deferredChecks : Array DeferredCheck


open Lean.Doc in
/--
Elaborates already-parsed Verso `blocks` for the specified declaration with interactive features
disabled, reporting any elaboration messages at the current reference. When `fileMap?` is provided,
message positions are interpreted against it.
-/
private def execVersoBlocks
    (declName : Name) (binders : Syntax) (blocks : TSyntaxArray ``Parser.block)
    (fileMap? : Option FileMap) : TermElabM VersoDocResult := do
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
  let ((text, subsections), deferredChecks) := val
  pure { text, subsections, deferredChecks }

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
    TermElabM VersoDocResult := do
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
  let s := Doc.Parser.documentFn.run ictx pmctx (getTokenTable env) s

  let errors := parseErrors ictx pmctx (getTokenTable env) docComment {} s
  if !errors.isEmpty then
    for (_, _, err) in errors do
      logError err.toString
    return { text := #[], subsections := #[], deferredChecks := #[] }
  if !ictx.atEnd s.pos then
    -- Reading a block at the stopped position reported nothing, so the character there is named.
    logError s!"unexpected '{ictx.get s.pos}'"
    return { text := #[], subsections := #[], deferredChecks := #[] }
  let doc : VersoDocument := ⟨s.stxStack.back⟩
  execVersoBlocks declName binders doc (fileMap? := some text)

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
    TermElabM VersoDocResult := do
  -- A docstring already parsed as Verso, or one re-parsable from its source range, supports
  -- interactive features. A macro-generated docstring has neither, so fall back to its text.
  let body := docComment.raw[1]
  -- Re-parsing reads the comment from its delimiters and its content, so every one of those needs a
  -- source position. A macro-generated docstring may lack any of them.
  if (docStringRange (← getFileMap).source docComment).toOption.isSome then
    -- Source positions are available, so re-parse from source for interactive features.
    if let some stx ← parseVersoDocString docComment then
      let ((text, subsections), deferredChecks) ←
        Doc.elabBlocks stx |>.exec declName binders
      return { text, subsections, deferredChecks }
    else return { text := #[], subsections := #[], deferredChecks := #[] }
  else if body.isOfKind ``versoCommentBody then
    match (VersoDocstringView.of docComment).markup with
    | .parseFailure text =>
      -- The markup failed to parse, so re-parse its text to report the error.
      versoDocStringOfText declName binders text.getAtomVal
    | .document doc =>
      -- A docstring parsed as Verso by a macro, with positions stripped.
      execVersoBlocks declName binders doc (fileMap? := none)
  else
    -- A plain-text doc comment without source positions; parse and elaborate from its text.
    versoDocStringOfText declName binders docComment.getDocString

open Lean.Doc in
/--
Parses and elaborates a Verso module docstring.
-/
def versoModDocString
    (range : DeclarationRange) (doc : VersoDocument) :
    TermElabM (VersoModuleDocs.Snippet × Array Doc.DeferredCheck) := do
  let level := getMainVersoModuleDocs (← getEnv) |>.terminalNesting |>.map (· + 1)
  Doc.elabModSnippet range doc (level.getD 0) |>.execForModule



/--
Adds a Verso docstring to the specified declaration, which should already be present in the
environment. The docstring is added from a string value, rather than syntax, which means that the
interactive features are disabled.
-/
def versoDocStringFromString
    (declName : Name) (docComment : String) :
    TermElabM VersoDocResult :=
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
Adds an elaborated Verso docstring to the environment, recording its `deferred` checks under this
declaration as their `site`.
-/
def addVersoDocStringCore [Monad m] [MonadEnv m] [MonadLiftT BaseIO m] [MonadError m]
    (declName : Name) (docs : VersoDocString) (deferred : Array Doc.DeferredCheck) : m Unit := do
  -- The decl name can be anonymous due to attempts to elaborate incomplete syntax. If the name is
  -- anonymous, the `MapDeclarationExtension.insert` panics due to not being on the right async
  -- branch. Better to just do nothing.
  if declName.isAnonymous then return
  unless (← getEnv).getModuleIdxFor? declName |>.isNone do
    throwError s!"invalid doc string, declaration '{declName}' is in an imported module"
  modifyEnv fun env =>
    let env := versoDocStringExt.insert env declName docs
    deferred.foldl (init := env) fun env c =>
      Doc.deferredCheckExt.addEntry env { c with site := .decl declName }

/--
Adds an elaborated Verso module docstring to the environment.
-/
def addVersoModDocStringCore [Monad m] [MonadEnv m] [MonadLiftT BaseIO m] [MonadError m]
  (docs : VersoModuleDocs.Snippet) (deferred : Array Doc.DeferredCheck) : m Unit := do
  if (getMainModuleDoc (← getEnv)).isEmpty then
    -- The snippet's index is the number of snippets already present.
    let n := (getMainVersoModuleDocs (← getEnv)).snippets.size
    match addVersoModuleDocSnippet (← getEnv) docs with
    | .error e => throwError "Error adding module docs: {indentD <| toMessageData e}"
    | .ok env' =>
      setEnv <| deferred.foldl (init := env') fun env c =>
        Doc.deferredCheckExt.addEntry env { c with site := .moduleDoc n }
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
  let { toVersoDocString, deferredChecks } ← versoDocString declName binders docComment
  addVersoDocStringCore declName toVersoDocString deferredChecks

/--
Adds a Verso docstring to the environment from a string value, which disables the interactive
features. This should be used for programs that add documentation when there is no syntax available.
-/
def addVersoDocStringFromString (declName : Name) (docComment : String) :
    TermElabM Unit := do
  unless (← getEnv).getModuleIdxFor? declName |>.isNone do
    throwError s!"invalid doc string, declaration '{declName}' is in an imported module"
  let { toVersoDocString, deferredChecks } ← versoDocStringFromString declName docComment
  addVersoDocStringCore declName toVersoDocString deferredChecks


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


open Lean.Doc in
/--
Adds a Verso module docstring to the environment.
-/
def addVersoModDocString
    (range : DeclarationRange) (doc : VersoDocument) :
    TermElabM Unit := do
  let (snippet, deferred) ← versoModDocString range doc
  addVersoModDocStringCore snippet deferred
