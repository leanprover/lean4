/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

prelude
public import Lean.Server.Requests
import Lean.PrettyPrinter.Source

public section

namespace Lean.Server.FileWorker.Formatting
open Lsp
open Snapshots

/-- Format commands in `[rangeStart, rangeEnd)` byte range. Commands outside the range
are emitted verbatim from the original source. Returns a full-document `TextEdit`. -/
def formatCommandRange
    (doc : EditableDocument) (text : FileMap)
    (initSnap : Language.Lean.InitialSnapshot)
    (headerParsed : Language.Lean.HeaderParsedState)
    (headerSuccess : Language.Lean.HeaderProcessedState)
    (rangeStart rangeEnd : String.Pos.Raw)
    : EIO RequestError (Array TextEdit) := do
  -- Collect all parsed command syntax by walking the CommandParsedSnapshot chain.
  let mut cmdStxs : Array Syntax := #[]
  let mut next? := some headerSuccess.firstCmdSnap
  repeat do
    match next? with
    | none => break
    | some snapshotTask =>
      let cmdParsed := snapshotTask.get
      cmdStxs := cmdStxs.push cmdParsed.stx
      next? := cmdParsed.nextCmdSnap?
  let headerSnap : Snapshots.Snapshot := {
    stx := initSnap.stx
    mpState := headerParsed.parserState
    cmdState := headerSuccess.cmdState
  }
  -- Emit header (imports) verbatim — ppCommand would incorrectly indent it.
  let headerStx := initSnap.stx
  let mut result : String := ""
  let headerOriginal := match headerStx.getPos?, headerStx.getTailPos? with
    | some s, some e => String.Pos.Raw.extract text.source s e
    | _, _ => headerStx.reprint.getD ""
  result := result ++ headerOriginal.trimAsciiEnd.copy
  let mut prevTailPos := headerStx.getTailPos?
  for stx in cmdStxs do
    match prevTailPos, stx.getPos? with
    | some prevEnd, some curStart =>
      let gap := String.Pos.Raw.extract text.source prevEnd curStart
      result := result ++ PrettyPrinter.collapseBlankLines gap
    | none, _ => pure ()
    | _, none => result := result ++ "\n"
    let cmdStart := stx.getPos?.getD 0
    let cmdEnd := stx.getTailPos?.getD 0
    let overlaps := cmdStart < rangeEnd && cmdEnd > rangeStart
    if overlaps then
      let fmtResult ← (headerSnap.runCoreM doc.meta (PrettyPrinter.ppCommand ⟨stx⟩)).toBaseIO
      let formatted := match fmtResult with
        | .ok fmt => PrettyPrinter.trimTrailingCommentLines fmt.pretty.trimAsciiEnd.copy
        | .error _ => PrettyPrinter.trimTrailingCommentLines (stx.reprint.getD "").trimAsciiEnd.copy
      result := result ++ formatted
    else
      -- Outside requested range: emit original source verbatim
      let original := match stx.getPos?, stx.getTailPos? with
        | some s, some e => String.Pos.Raw.extract text.source s e
        | _, _ => stx.reprint.getD ""
      result := result ++ original.trimAsciiEnd.copy
    prevTailPos := stx.getTailPos?
  let endPos := text.utf8PosToLspPos text.source.rawEndPos
  let fullRange : Range := ⟨⟨0, 0⟩, endPos⟩
  return #[{ range := fullRange, newText := result }]

end Lean.Server.FileWorker.Formatting
