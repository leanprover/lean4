/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alok Singh
-/
module

prelude
public import Lean.Server.CodeActions.Basic
public import Lean.Server.FileWorker.Utils
public import Lean.Parser.Module

public section

namespace Lean.Server

open Lean Lsp Server RequestM

/--
Code action provider that offers to wrap keywords in guillemets when they're used
where an identifier is expected.
-/
@[builtin_code_action_provider] def guillemetsEscapeCodeActionProvider : CodeActionProvider := fun params _snap => do
  let doc ← readDoc
  let text := doc.meta.text
  let startPos := text.lspPosToUtf8Pos params.range.start
  let endPos := text.lspPosToUtf8Pos params.range.end
  let requestedRange : Lean.Syntax.Range := ⟨startPos, endPos⟩

  -- Collect messages from all snapshots
  let snaps := Language.toSnapshotTree doc.initSnap |>.getAll
  let msgLog : MessageLog := snaps.map (·.diagnostics.msgLog) |>.foldl (· ++ ·) {}

  let mut codeActions : Array LazyCodeAction := #[]

  for msg in msgLog.unreported do
    -- Check if this message has the guillemets-fixable tag
    if !msg.data.hasTag (· == Lean.Parser.guillemetsFixableMessageTag) then
      continue

    -- Check if the message range overlaps with the requested range
    let msgRange : Lean.Syntax.Range := ⟨text.ofPosition msg.pos, text.ofPosition <| msg.endPos.getD msg.pos⟩
    if !msgRange.overlaps requestedRange (includeFirstStop := true) (includeSecondStop := true) then
      continue

    -- Extract the token from the source text at the message position
    let tokenText : String := String.Pos.Raw.extract text.source msgRange.start msgRange.stop

    -- Skip if empty or already escaped
    if tokenText.isEmpty || tokenText.front == '«' then
      continue

    -- Create the fix: wrap in guillemets
    let escapedText := s!"{idBeginEscape}{tokenText}{idEndEscape}"
    let lspRange := text.utf8RangeToLspRange msgRange

    let codeAction : CodeAction := {
      title := s!"Escape `{tokenText}` with guillemets"
      kind? := "quickfix"
      edit? := WorkspaceEdit.ofTextDocumentEdit {
        textDocument := doc.versionedIdentifier
        edits := #[{ range := lspRange, newText := escapedText }]
      }
    }
    codeActions := codeActions.push codeAction

  return codeActions

end Lean.Server
