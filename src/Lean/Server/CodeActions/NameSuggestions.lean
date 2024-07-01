/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Thrane Christiansen
-/
prelude
import Lean.Elab.NameSuggestions
import Lean.Server.CodeActions.Basic

set_option linter.missingDocs true

open Lean Elab Server RequestM

/--
A code action provider for spelling suggestions for identifiers.

This presents quickfixes based on the data saved by `Lean.Elab.saveNameSuggestions`.
-/
@[builtin_code_action_provider]
def holeCodeActionProvider : CodeActionProvider := fun params snap => do
  let doc ← readDoc
  let fileMap := doc.meta.text
  let startPos := doc.meta.text.lspPosToUtf8Pos params.range.start
  let endPos := doc.meta.text.lspPosToUtf8Pos params.range.end
  let names : Array NameSuggestionInfo := snap.infoTree.foldInfo (init := #[]) fun _ctx info result => Id.run do
    let .ofCustomInfo info := info | result
    if let some v := info.value.get? NameSuggestionInfo then
      let (some head, some tail) := (info.stx.getPos? true, info.stx.getTailPos? true) | return result
      unless head ≤ endPos && startPos ≤ tail do return result
      result.push v
    else result
  let mut quickfixes : Array LazyCodeAction:= #[]
  for ⟨range, xs⟩ in names do
    let range := fileMap.utf8RangeToLspRange range
    for x in xs.get do
      quickfixes := quickfixes.push {
        eager := {
          title := s!"Replace with '{x}'",
          kind? := some "quickfix",
          isPreferred? := some true,
          edit? := some <| .ofTextEdit doc.versionedIdentifier { range, newText := x }
        }
      }
  return quickfixes
