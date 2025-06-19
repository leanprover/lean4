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
  ],
  "suggestion": "hi",
  "range": {
    "start": {"line": 100, "character": 0},
    "end":   {"line": 100, "character": 5}
  }
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
    { onClick,
      title: 'Apply suggestion',
      className: 'link pointer dim font-code',
      style: { display: 'inline-block', verticalAlign: 'text-top' } },
    spans)
  return fullDiff
}"

/--
Converts an array of diff actions into corresponding JSON interpretable by `tryThisDiffWidget`.
-/
private def mkDiffJson (ds : Array (Diff.Action × String)) :=
  toJson <| ds.map fun
    | (.insert, s) => json% { type: "insertion", text: $s }
    | (.delete, s) => json% { type: "deletion", text: $s }
    | (.skip  , s) => json% { type: "unchanged", text: $s }

/--
Converts an array of diff actions into a Unicode string that visually depicts the diff.

Note that this function does not return the string that results from applying the diff to some
input; rather, it returns a string representation of the actions that the diff itself comprises,
such as `b̵a̵c̲h̲e̲e̲rs̲`.
-/
private def mkDiffString (ds : Array (Diff.Action × String)) : String :=
  let rangeStrs := ds.map fun
    | (.insert, s) => String.mk (s.data.flatMap ([·, '\u0332'])) -- U+0332 Combining Low Line
    | (.delete, s) => String.mk (s.data.flatMap ([·, '\u0335'])) -- U+0335 Combining Short Stroke Overlay
    | (.skip  , s) => s
  rangeStrs.foldl (· ++ ·) ""

/--
A code action suggestion associated with a hint in a message.

Refer to `TryThis.Suggestion`; this extends that structure with a `span?` field, allowing a single
hint to suggest modifications at different locations. If `span?` is not specified, then the syntax
reference provided to `MessageData.hint` will be used.
-/
structure Suggestion extends toTryThisSuggestion : TryThis.Suggestion where
  span? : Option Syntax := none

instance : Coe TryThis.SuggestionText Suggestion where
  coe t := { suggestion := t }

instance : ToMessageData Suggestion where
  toMessageData s := toMessageData s.toTryThisSuggestion

/--
Produces a diff that splits either on characters, tokens, or not at all, depending on the edit
distance between the arguments.

Guarantees that all actions in the output will be maximally grouped; that is, instead of returning
`#[(.insert, "a"), (.insert, "b")]`, it will return `#[(.insert, "ab")]`.
-/
partial def readableDiff (s s' : String) : Array (Diff.Action × String) :=
  -- TODO: add additional diff granularities
  let minLength := min s.length s'.length
  -- The coefficient on this value can be tuned:
  let maxCharDiffDistance := minLength

  let charDiff := Diff.diff (splitChars s) (splitChars s')
  -- Note: this is just a rough heuristic, since the diff has no notion of substitution
  let approxEditDistance := charDiff.filter (·.1 != .skip) |>.size
  let preStrDiff := joinEdits charDiff
  -- Given that `Diff.diff` returns a minimal diff, any length-≤3 diff can only have edits at the
  -- front and back, or at a single interior point. This will always be fairly readable (and
  -- splitting by a larger unit would likely only be worse). Otherwise, we should only use the
  -- per-character diff if the edit distance isn't so large that it will be hard to read:
  if preStrDiff.size ≤ 3 || approxEditDistance ≤ maxCharDiffDistance then
    preStrDiff.map fun (act, cs) => (act, String.mk cs.toList)
  else
    #[(.delete, s), (.insert, s')]
where
  splitChars (s : String) : Array Char :=
    s.toList.toArray

  joinEdits {α} (ds : Array (Diff.Action × α)) : Array (Diff.Action × Array α) :=
    ds.foldl (init := #[]) fun acc (act, c) =>
      if h : acc.isEmpty then
        #[(act, #[c])]
      else
        have : acc.size - 1 < acc.size := Nat.sub_one_lt <| mt Array.size_eq_zero_iff.mp <|
          Array.isEmpty_eq_false_iff.mp (Bool.of_not_eq_true h)
        let (act', cs) := acc[acc.size - 1]
        if act == act' then
          acc.set (acc.size - 1) (act, cs.push c)
        else
          acc.push (act, #[c])

/--
Creates message data corresponding to a `HintSuggestions` collection and adds the corresponding info
leaf.
-/
def mkSuggestionsMessage (suggestions : Array Suggestion)
    (ref : Syntax)
    (codeActionPrefix? : Option String) : CoreM MessageData := do
  let mut msg := m!""
  for suggestion in suggestions do
    if let some range := (suggestion.span?.getD ref).getRange? then
      let { info, suggestions := suggestionArr, range := lspRange } ←
        processSuggestions ref range #[suggestion.toTryThisSuggestion] codeActionPrefix?
      pushInfoLeaf info
      -- The following access is safe because
      -- `suggestionsArr = #[suggestion.toTryThisSuggestion].map ...` (see `processSuggestions`)
      let suggestionText := suggestionArr[0]!.2.1
      let map ← getFileMap
      let rangeContents := Substring.mk map.source range.start range.stop |>.toString
      let edits := readableDiff rangeContents suggestionText
      let diffJson := mkDiffJson edits
      let json := json% {
        diff: $diffJson,
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
      let suggestionMsg := if suggestions.size == 1 then
        m!"\n{widgetMsg}"
      else
        m!"\n" ++ MessageData.nest 2 m!"• {widgetMsg}"
      msg := msg ++ MessageData.nestD suggestionMsg
  return msg

/--
Creates a hint message with associated code action suggestions.

To provide a hint without an associated code action, use `MessageData.hint'`.

The arguments are as follows:
* `hint`: the main message of the hint, which precedes its code action suggestions.
* `suggestions`: the suggestions to display.
* `ref?`: if specified, the syntax location for the code action suggestions; otherwise, default to
  the syntax reference in the monadic state. Will be overridden by the `span?` field on any
  suggestions that specify it.
* `codeActionPrefix?`: if specified, text to display in place of "Try this: " in the code action
  label
-/
def _root_.Lean.MessageData.hint (hint : MessageData)
    (suggestions : Array Suggestion) (ref? : Option Syntax := none)
    (codeActionPrefix? : Option String := none)
    : CoreM MessageData := do
  let ref := ref?.getD (← getRef)
  let suggs ← mkSuggestionsMessage suggestions ref codeActionPrefix?
  return .tagged `hint (m!"\n\nHint: " ++ hint ++ suggs)
