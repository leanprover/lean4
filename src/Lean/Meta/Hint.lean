/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Rotella
-/

prelude

import Lean.CoreM
import Lean.Data.Lsp.Utf16
import Lean.Message
import Lean.Meta.TryThis
import Lean.Util.Diff
import Lean.Widget.Types
import Lean.PrettyPrinter

namespace Lean.Meta.Hint

open Elab Tactic PrettyPrinter TryThis

/--
A widget for rendering code-action suggestions in error messages. Generally, this widget should not
be used directly; instead, use `MessageData.hint`. Note that this widget is intended only for use
within message data; it may not display line breaks properly if rendered as a panel widget.

The props to this widget are of the following form:
```json
{
  "diff": [
    {"type": "unchanged", "text": "h"},
    {"type": "deletion", "text": "ello"},
    {"type": "insertion", "text": "i"}
  ]
}
```
-/
def tryThisDiffWidget : Widget.Module where
  javascript := "
import * as React from 'react';
import { EditorContext, EnvPosContext } from '@leanprover/infoview';
const e = React.createElement;
export default function ({ diff, range, suggestion }) {
  const pos = React.useContext(EnvPosContext)
  const editorConnection = React.useContext(EditorContext)
  const insStyle = { className: 'information' }
  const delStyle = {
    style: { color: 'var(--vscode-errorForeground)', textDecoration: 'line-through' }
  }
  const defStyle = {
    style: { color: 'var(--vscode-textLink-foreground)' }
  }
  function onClick() {
    editorConnection.api.applyEdit({
      changes: { [pos.uri]: [{ range, newText: suggestion }] }
    })
  }

  const spans = diff.map (comp =>
    comp.type === 'deletion' ? e('span', delStyle, comp.text) :
    comp.type === 'insertion' ? e('span', insStyle, comp.text) :
      e('span', defStyle, comp.text)
  )
  const fullDiff = e('span',
    { onClick, title: 'Apply suggestion', className: 'link pointer dim font-code', },
    spans)
  return fullDiff
}"

def mkDiffJson (ds : Array (Diff.Action × Char)) :=
  -- Avoid cluttering the DOM by grouping "runs" of the same action
  let unified : List (Diff.Action × List Char) := ds.foldr (init := []) fun
    | (act, c), [] => [(act, [c])]
    | (act, c), (act', cs) :: acc =>
      if act == act' then
        (act, c :: cs) :: acc
      else
        (act, [c]) :: (act', cs) :: acc
  toJson <| unified.map fun
    | (.insert, s) => json% { type: "insertion", text: $(String.mk s) }
    | (.delete, s) => json% { type: "deletion", text: $(String.mk s) }
    | (.skip  , s) => json% { type: "unchanged", text: $(String.mk s) }

def mkDiffString (ds : Array (Diff.Action × Char)) : String :=
  let rangeStrs := ds.map fun
    | (.insert, s) => String.mk [s, '\u0332']
    | (.delete, s) => String.mk [s, '\u0335']
    | (.skip  , s) => String.mk [s]
  rangeStrs.foldl (· ++ ·) ""

structure Suggestion extends TryThis.Suggestion where
  span? : Option Syntax := none

abbrev SuggestionText := TryThis.SuggestionText

instance : Coe SuggestionText Suggestion where
  coe t := { suggestion := t }

instance : ToMessageData Suggestion where
  toMessageData s := toMessageData s.toSuggestion

structure Suggestions where
  ref : Syntax
  suggestions : Array Suggestion
  codeActionPrefix? : Option String := none

/--
Creates message data corresponding to a `HintSuggestions` collection and adds the corresponding info
leaf.
-/
def Suggestions.toHintMessage (suggestions : Suggestions) : CoreM MessageData := do
  let { ref, codeActionPrefix?, suggestions } := suggestions
  let mut msg := m!""
  if suggestions.size > 0 then
    for suggestion in suggestions do
      if let some range := (suggestion.span?.getD ref).getRange? then
        let { info, suggestions := suggestionArr, range := lspRange } ← processSuggestions ref range
          #[suggestion.toSuggestion] codeActionPrefix?
        pushInfoLeaf info
        let suggestionText := suggestionArr[0]!.2.1
        let map ← getFileMap
        let rangeContents := Substring.mk map.source range.start range.stop |>.toString
        let split (s : String) := s.toList.toArray
        let edits := Diff.diff (split rangeContents) (split suggestionText)
        let diff := mkDiffJson edits
        let json := json% {
          diff: $diff,
          suggestion: $suggestionText,
          range: $lspRange
        }
        let preInfo := suggestion.preInfo?.getD ""
        let postInfo := suggestion.postInfo?.getD ""
        let widget := MessageData.ofWidget {
            id := ``tryThisDiffWidget
            javascriptHash := tryThisDiffWidget.javascriptHash
            props := return json
          } (suggestion.messageData?.getD (mkDiffString edits))
        let widgetMsg := m!"{preInfo}{widget}{postInfo}"
        let suggestionMsg := if suggestions.size == 1 then m!"\n{widgetMsg}" else m!"\n• {widgetMsg}"
        msg := msg ++ MessageData.nestD suggestionMsg
  return msg

/--
Appends a hint `hint` to `msg`. If `suggestions?` is non-`none`, will also append an inline
suggestion widget.
-/
def _root_.Lean.MessageData.hint (hint : MessageData) (suggestions? : Option Suggestions := none)
    : CoreM MessageData := do
  let mut hintMsg := m!"\n\nhint: {hint}"
  if let some suggestions := suggestions? then
    hintMsg := hintMsg ++ (← suggestions.toHintMessage)
  return .tagged `hint hintMsg
