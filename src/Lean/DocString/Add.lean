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
import Lean.DocString.Parser
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
    (docstring : TSyntax `Lean.Parser.Command.docComment) :
    TermElabM Unit := do
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


open Lean.Doc in
open Parser in
/--
Adds a Verso docstring to the specified declaration, which should already be present in the
environment.
-/
def versoDocString
    (declName : Name) (docComment : TSyntax `Lean.Parser.Command.docComment) :
    TermElabM (Array (Doc.Block ElabInline ElabBlock) × Array (Doc.Part ElabInline ElabBlock Empty)) := do

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
  let s := (Doc.Parser.document).run ictx pmctx (getTokenTable env) s

  if !s.allErrors.isEmpty then
    for (pos, _, err) in s.allErrors do
      logMessage {
        fileName := (← getFileName),
        pos := text.toPosition pos,
        -- TODO end position
        data := err.toString
      }
    return (#[], #[])
  else
    let stx := s.stxStack.back
    let stx := stx.getArgs
    Doc.elabBlocks (stx.map (⟨·⟩)) |>.exec declName

/--
Adds a Markdown docstring to the environment, validating documentation links.
-/
def addMarkdownDocString (declName : Name) (docComment : TSyntax `Lean.Parser.Command.docComment) : TermElabM Unit := do
  unless (← getEnv).getModuleIdxFor? declName |>.isNone do
    throwError s!"invalid doc string, declaration '{declName}' is in an imported module"
  validateDocComment docComment
  let docString : String ← getDocStringText docComment
  modifyEnv fun env => docStringExt.insert env declName docString.removeLeadingSpaces

/--
Adds an elaborated Verso docstring to the environment.
-/
def addVersoDocStringCore [Monad m] [MonadEnv m]
    (declName : Name) (docs : VersoDocString) : m Unit := do
  let ⟨blocks, parts⟩ := docs
  modifyEnv fun env =>
    versoDocStringExt.addEntry (asyncDecl := declName) (asyncMode := .mainOnly)
      env (declName, ⟨blocks, parts⟩) -- Using .insert env declName ⟨blocks, parts⟩ leads to panics

/--
Adds a Verso docstring to the environment.
-/
def addVersoDocString (declName : Name) (docComment : TSyntax `Lean.Parser.Command.docComment) : TermElabM Unit := do
  unless (← getEnv).getModuleIdxFor? declName |>.isNone do
    throwError s!"invalid doc string, declaration '{declName}' is in an imported module"
  let (blocks, parts) ← versoDocString declName docComment
  addVersoDocStringCore declName ⟨blocks, parts⟩

/--
Adds a docstring to the environment. If `isVerso` is `false`, then the docstring is interpreted as
Markdown.
-/
def addDocStringOf
    (isVerso : Bool) (declName : Name) (docComment : TSyntax `Lean.Parser.Command.docComment) :
    TermElabM Unit := do
  if isVerso then
    addVersoDocString declName docComment
  else
    addMarkdownDocString declName docComment

/--
Adds a docstring to the environment.

If the option `doc.verso` is `true`, the docstring is processed as a Verso docstring.

Otherwise, it is considered a Markdown docstring, and documentation links are validated.
-/
def addDocString
    (declName : Name) (docComment : TSyntax `Lean.Parser.Command.docComment) :
    TermElabM Unit := do
  addDocStringOf (doc.verso.get (← getOptions)) declName docComment

/--
Adds a docstring to the environment, if it is provided. If no docstring is provided, nothing
happens.

If the option `doc.verso` is `true`, the docstring is processed as a Verso docstring.

Otherwise, it is considered a Markdown docstring, and documentation links are validated.
-/
def addDocString'
    (declName : Name) (docString? : Option (TSyntax `Lean.Parser.Command.docComment)) :
    TermElabM Unit :=
  match docString? with
  | some docString => addDocString declName docString
  | none => return ()
