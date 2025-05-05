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
A widget for rendering code action suggestions in error messages. Generally, this widget should not
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

Note: we cannot add the `builtin_widget_module` attribute here because that would require importing
`Lean.Widget.UserWidget`, which in turn imports much of `Lean.Elab` -- the module where we want to
be able to use this widget. Instead, we register the attribute post-hoc when we declare the regular
"Try This" widget in `Lean.Meta.Tactic.TryThis`.
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

/--
Converts an array of diff actions into corresponding JSON interpretable by `tryThisDiffWidget`.
-/
private def mkDiffJson (ds : Array (Diff.Action × Char)) :=
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

/--
Converts an array of diff actions into a Unicode string that visually depicts the diff.

Note that this function does not return the string that results from applying the diff to some
input; rather, it returns a string representation of the actions that the diff itself comprises, such as `b̵a̵c̲h̲e̲e̲rs̲`.

-/
private def mkDiffString (ds : Array (Diff.Action × Char)) : String :=
  let rangeStrs := ds.map fun
    | (.insert, s) => String.mk [s, '\u0332'] -- U+0332 Combining Low Line
    | (.delete, s) => String.mk [s, '\u0335'] -- U+0335 Combining Short Stroke Overlay
    | (.skip  , s) => String.mk [s]
  rangeStrs.foldl (· ++ ·) ""

/--
A code action suggestion associated with a hint in a message.

Refer to `TryThis.Suggestion`; this extends that structure with a `span?` field, allowing a single
hint to suggest modifications at different locations. If `span?` is not specified, then the `ref`
for the containing `Suggestions` value is used.
-/
structure Suggestion extends TryThis.Suggestion where
  span? : Option Syntax := none

instance : Coe TryThis.SuggestionText Suggestion where
  coe t := { suggestion := t }

instance : ToMessageData Suggestion where
  toMessageData s := toMessageData s.toSuggestion

/--
A collection of code action suggestions to be included in a hint in a diagnostic message.

Contains the following fields:
* `ref`: the syntax location for the code action suggestions. Will be overridden by the `span?`
  field on any suggestions that specify it.
* `suggestions`: the suggestions to display.
* `codeActionPrefix?`: if specified, text to display in place of "Try this: " in the code action
  label
-/
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
  let mut hintMsg := m!"\n\nHint: {hint}"
  if let some suggestions := suggestions? then
    hintMsg := hintMsg ++ (← suggestions.toHintMessage)
  return .tagged `hint hintMsg
