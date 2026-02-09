/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Rotella
-/

module

prelude

public import Lean.Meta.TryThis
public import Lean.Util.Diff

public section

namespace Lean.Meta.Hint

open Elab Tactic PrettyPrinter TryThis

/--
A widget for a clickable link (or icon) that inserts text into the document at a given position.

The props to this widget are of the following form:
```json
{
  "range": {
    "start": {"line": 100, "character": 0},
    "end":   {"line": 100, "character": 5}
  },
  "suggestion": "hi",
  "acceptSuggestionProps": {
    "kind": "text",
    "hoverText": "Displayed on hover",
    "linkText": "Displayed as the text of the link"
  }
}
```
... or the following form, where `codiconName` is one of the icons at
https://microsoft.github.io/vscode-codicons/dist/codicon.html and `gaps` determines
whether there are clickable spaces surrounding the icon:
```json
{
  "range": {
    "start": {"line": 100, "character": 0},
    "end":   {"line": 100, "character": 5}
  },
  "suggestion": "hi",
  "acceptSuggestionProps": {
    "kind": "icon",
    "hoverText": "Displayed on hover",
    "codiconName": "search",
    "gaps": true
  }
}
```

Note: we cannot add the `builtin_widget_module` attribute here because that would require importing
`Lean.Widget.UserWidget`, which in turn imports much of `Lean.Elab` -- the module where we want to
be able to use this widget. Instead, we register the attribute post-hoc when we declare the regular
"Try This" widget in `Lean.Meta.Tactic.TryThis`.
-/
def textInsertionWidget : Widget.Module where
  javascript := "
import * as React from 'react';
import { EditorContext, EnvPosContext } from '@leanprover/infoview';

const e = React.createElement;
export default function ({ range, suggestion, acceptSuggestionProps }) {
  const pos = React.useContext(EnvPosContext)
  const editorConnection = React.useContext(EditorContext)
  function onClick() {
    editorConnection.api.applyEdit({
      changes: { [pos.uri]: [{ range, newText: suggestion }] }
    })
  }

  if (acceptSuggestionProps.kind === 'text') {
    return e('span', {
        onClick,
        title: acceptSuggestionProps.hoverText,
        className: 'link pointer dim font-code',
        style: { color: 'var(--vscode-textLink-foreground)' }
      },
      acceptSuggestionProps.linkText)
  } else if (acceptSuggestionProps.kind === 'icon') {
    if (acceptSuggestionProps.gaps) {
      const icon = e('span', {
        className: `codicon codicon-${acceptSuggestionProps.codiconName}`,
        style: {
          verticalAlign: 'sub',
          fontSize: 'var(--vscode-editor-font-size)'
        }
      })
      return e('span', {
        onClick,
        title: acceptSuggestionProps.hoverText,
        className: `link pointer dim font-code`,
        style: { color: 'var(--vscode-textLink-foreground)' }
      }, ' ', icon, ' ')
    } else {
      return e('span', {
        onClick,
        title: acceptSuggestionProps.hoverText,
        className: `link pointer dim font-code codicon codicon-${acceptSuggestionProps.codiconName}`,
        style: {
          color: 'var(--vscode-textLink-foreground)',
          verticalAlign: 'sub',
          fontSize: 'var(--vscode-editor-font-size)'
        }
      })
    }

  }
  throw new Error('Unexpected `acceptSuggestionProps` kind: ' + acceptSuggestionProps.kind)
}"

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
  const insStyle = {
    style: { color: 'var(--vscode-textLink-foreground)' }
  }
  const delStyle = {
    style: { color: 'var(--vscode-editorError-foreground)', textDecoration: 'line-through' }
  }
  const defStyle = {
    style: { color: 'var(--vscode-editor-foreground)' }
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
    | (.insert, s) => String.ofList (s.toList.flatMap ([·, '\u0332'])) -- U+0332 Combining Low Line
    | (.delete, s) => String.ofList (s.toList.flatMap ([·, '\u0335'])) -- U+0335 Combining Short Stroke Overlay
    | (.skip  , s) => s
  rangeStrs.foldl (· ++ ·) ""

/-- The granularity at which to display an inline diff for a suggested edit. -/
inductive DiffGranularity where
  /-- Automatically select diff granularity based on edit distance. -/
  | auto
  /-- Character-level diff. -/
  | char
  /-- Diff using whitespace-separated tokens. -/
  | word
  /--
  "Monolithic" diff: shows a deletion of the entire existing source, followed by an insertion of the
  entire suggestion.
  -/
  | all
  /--
  No diff: Shows no deletion of the existing source, only an insertion of the suggestion.
  -/
  | none

/--
A code action suggestion associated with a hint in a message.

Refer to `TryThis.Suggestion`. This extends that structure with several fields specific to inline
hints.
-/
structure Suggestion extends toTryThisSuggestion : TryThis.Suggestion where
  /--
  The span at which this suggestion should apply. This allows a single hint to suggest modifications
  at different locations. If `span?` is not specified, then the syntax reference provided to
  `MessageData.hint` will be used.
  -/
  span? : Option Syntax := none
  /--
  The syntax to render in the inline diff preview. This syntax must have valid position information
  and must contain the span at which the edit occurs.
  -/
  previewSpan? : Option Syntax := none
  /--
  The granularity at which the diff for this suggestion should be rendered in the Infoview. See
  `DiffMode` for the possible granularities. This is `.auto` by default.
  -/
  diffGranularity : DiffGranularity := .auto

instance : Coe TryThis.SuggestionText Suggestion where
  coe t := { suggestion := t }

instance : ToMessageData Suggestion where
  toMessageData s := toMessageData s.toTryThisSuggestion

/--
Produces a diff that splits either on characters, tokens, or not at all, depending on the selected
`diffMode`.

Guarantees that all actions in the output will be maximally grouped; that is, instead of returning
`#[(.insert, "a"), (.insert, "b")]`, it will return `#[(.insert, "ab")]`.
-/
partial def readableDiff (s s' : String) (granularity : DiffGranularity := .auto) : Array (Diff.Action × String) :=
  match granularity with
  | .none => #[(.insert, s')]
  | .char => charDiff
  | .word => wordDiff
  | .all => maxDiff
  | .auto =>
    let minLength := min s.length s'.length
    -- The coefficients on these values can be tuned:
    let maxCharDiffDistance := minLength / 5
    let maxWordDiffDistance := minLength / 2 + (max s.length s'.length) / 2

    let charDiffRaw := Diff.diff (splitChars s) (splitChars s')
    -- Note: this is just a rough heuristic, since the diff has no notion of substitution
    let approxEditDistance := charDiffRaw.filter (·.1 != .skip) |>.size
    let charArrDiff := joinEdits charDiffRaw

    -- Given that `Diff.diff` returns a minimal diff, any length-≤3 diff can only have edits at the
    -- front and back, or at a single interior point. This will always be fairly readable (and
    -- splitting by a larger unit would likely only be worse)
    if charArrDiff.size ≤ 3 || approxEditDistance ≤ maxCharDiffDistance then
      charArrDiff.map fun (act, cs) => (act, String.ofList cs.toList)
    else if approxEditDistance ≤ maxWordDiffDistance then
      wordDiff
    else
      maxDiff
where
  /-
  Note on whitespace insertion:
  Because we display diffs fully inline, we must trade off between accurately rendering changes to
  whitespace and accurately previewing what will be inserted. We err on the side of the latter.
  Within a "run" of deletions or insertions, we maintain the whitespace from the deleted/inserted
  text and mark it as a deletion/insertion. After an unchanged word or a substitution (i.e., a
  deletion and insertion without an intervening unchanged word), we show a whitespace diff iff the
  old whitespace did not contain a line break (as rendering a deleted newline still visually
  suggests a line break in the new output); otherwise, we use the whitespace from the new version
  but mark it as unchanged, since there was also whitespace here originally too. Within a
  substitution, we omit whitespace entirely. After an insertion, we show the new whitespace and mark
  it as an insertion. After a deletion, we render the old whitespace as a deletion unless it
  contains a newline, for the same reason mentioned previously.
  -/
  wordDiff := Id.run do
    let (words, wss) := splitWords s
    let (words', wss') := splitWords s'
    let diff := Diff.diff words words'
    let mut withWs := #[]
    let mut (wssIdx, wss'Idx) := (0, 0)
    let mut inSubst := false
    for h : diffIdx in *...diff.size do
      let (a₁, s₁) := diff[diffIdx]
      withWs := withWs.push (a₁, s₁)
      if let some (a₂, s₂) := diff[diffIdx + 1]? then
        match a₁, a₂ with
        | .skip, .delete =>
          -- Unchanged word: show whitespace diff unless this is followed by a deleted terminal
          -- substring of the old, in which case show the old whitespace (since there is no new)
          let ws := wss[wssIdx]!
          let wsDiff := if let some ws' := wss'[wss'Idx]? then
            mkWhitespaceDiff ws ws'
          else
            #[(.delete, ws)]
          withWs := withWs ++ wsDiff
          wssIdx := wssIdx + 1
          wss'Idx := wss'Idx + 1
        | .skip, .skip | .skip, .insert =>
          -- Unchanged word: inverse of the above case: new has whitespace here, and old does too so
          -- long as we haven't reached an appended terminal new portion
          let ws' := wss'[wss'Idx]!
          let wsDiff := if let some ws := wss[wssIdx]? then
            mkWhitespaceDiff ws ws'
          else
            #[(.insert, ws')]
          withWs := withWs ++ wsDiff
          wssIdx := wssIdx + 1
          wss'Idx := wss'Idx + 1
        | .insert, .insert =>
          -- Insertion separator: include whitespace, and mark it as inserted
          let ws := wss'[wss'Idx]!
          withWs := withWs.push (.insert, ws)
          wss'Idx := wss'Idx + 1
        | .insert, .skip =>
          -- End of insertion: if this was a substitution, new and old have whitespace here; if it
          -- wasn't, only new has whitespace here
          let ws' := wss'[wss'Idx]!
          let wsDiff := if inSubst then
            mkWhitespaceDiff wss[wssIdx]! ws'
          else
            #[(.insert, ws')]
          withWs := withWs ++ wsDiff
          wss'Idx := wss'Idx + 1
          if inSubst then wssIdx := wssIdx + 1
          inSubst := false
        | .delete, .delete =>
          -- Deletion separator: include and mark as deleted
          let ws := wss[wssIdx]!
          withWs := withWs.push (.delete, ws)
          wssIdx := wssIdx + 1
        | .delete, .skip =>
          -- End of deletion: include the deletion's whitespace as deleted iff it is not a newline
          -- (see earlier note); in principle, we should never have a substitution ending with a
          -- deletion (`diff` should prefer `a̵b̲` to `b̲a̵`), but we handle this in case `diff` changes
          let ws := wss[wssIdx]!
          unless inSubst || ws.contains '\n' do
            withWs := withWs.push (.delete, ws)
            wssIdx := wssIdx + 1
          if inSubst then wss'Idx := wss'Idx + 1
          inSubst := false
        | .insert, .delete | .delete, .insert =>
          -- "Substitution point": don't include any whitespace, since we're switching this word
          inSubst := true
    withWs
      |> joinEdits
      |>.map fun (act, ss) => (act, ss.foldl (· ++ ·) "")

  charDiff :=
    Diff.diff (splitChars s) (splitChars s') |> joinCharDiff

  /-- Given a `Char` diff, produces an equivalent `String` diff, joining actions of the same kind. -/
  joinCharDiff (d : Array (Diff.Action × Char)) :=
    joinEdits d |>.map fun (act, cs) => (act, String.ofList cs.toList)

  maxDiff :=
    #[(.delete, s), (.insert, s')]

  mkWhitespaceDiff (oldWs newWs : String) :=
    if !oldWs.contains '\n' then
      Diff.diff oldWs.toList.toArray newWs.toList.toArray |> joinCharDiff
    else
      #[(.skip, newWs)]

  splitChars (s : String) : Array Char :=
    s.toList.toArray

  splitWords (s : String) : Array String × Array String :=
    splitWordsAux s 0 0 #[] #[]

  splitWordsAux (s : String) (b : String.Pos.Raw) (i : String.Pos.Raw) (r ws : Array String) : Array String × Array String :=
    if h : i.atEnd s then
      (r.push (String.Pos.Raw.extract s b i), ws)
    else
      have := Nat.sub_lt_sub_left (Nat.gt_of_not_le (mt decide_eq_true h)) (String.Pos.Raw.lt_next s _)
      if (i.get s).isWhitespace then
        let skipped := (Substring.Raw.mk s i s.rawEndPos).takeWhile (·.isWhitespace)
        let i' := skipped.stopPos
        splitWordsAux s i' i' (r.push (String.Pos.Raw.extract s b i)) (ws.push (String.Pos.Raw.extract s i i'))
      else
        splitWordsAux s b (i.next s) r ws

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
def mkSuggestionsMessage (suggestions : Array Suggestion) (ref : Syntax)
    (codeActionPrefix? : Option String) (forceList : Bool) : CoreM MessageData := do
  let mut msg := m!""
  for suggestion in suggestions do
    let some range := suggestion.span?.getD ref |>.getRange?
      | continue
    let edit ← suggestion.processEdit range
    let suggestionText := edit.newText
    let ref := Syntax.ofRange <| ref.getRange?.getD range
    let codeActionTitleOverride? := suggestion.toCodeActionTitle?.map (· suggestionText)
    let codeActionTitle := codeActionTitleOverride?.getD <| (codeActionPrefix?.getD "Try this: ") ++ suggestionText
    let info := Info.ofCustomInfo {
      stx := ref
      value := Dynamic.mk {
        edit
        suggestion := suggestion.toTryThisSuggestion
        codeActionTitle
        : TryThisInfo
      }
    }
    pushInfoLeaf info
    let map ← getFileMap
    let rangeContents := String.Pos.Raw.extract map.source range.start range.stop
    let edits ← do
      if let some msgData := suggestion.messageData? then
        pure #[(.insert, toString <| ← msgData.format)]
      else
        pure <| readableDiff rangeContents suggestionText suggestion.diffGranularity
    let mut edits := edits
    if let some previewRange := suggestion.previewSpan? >>= Syntax.getRange? then
      if previewRange.includes range then
        let map ← getFileMap
        if previewRange.start < range.start then
          edits := #[(.skip, (String.Pos.Raw.extract map.source previewRange.start range.start))] ++ edits
        if range.stop < previewRange.stop then
          edits := edits.push (.skip, (String.Pos.Raw.extract map.source range.stop previewRange.stop))
    let preInfo := suggestion.preInfo?.getD ""
    let postInfo := suggestion.postInfo?.getD ""
    let isDiffSuggestion :=
      ! (suggestion.diffGranularity matches .none) && suggestion.messageData?.isNone
        || suggestion.previewSpan?.isSome
    let suggestionMsg :=
      if ! isDiffSuggestion then
        let applyButton := MessageData.ofWidget {
          id := ``textInsertionWidget
          javascriptHash := textInsertionWidget.javascriptHash
          props := return json% {
            range: $edit.range,
            suggestion: $suggestionText,
            acceptSuggestionProps: {
              kind: "text",
              hoverText: "Apply suggestion",
              linkText: "[apply]"
            }
          }
        } "[apply]"
        m!"\n{applyButton} {preInfo}{toMessageData suggestion}{postInfo}"
      else
        let diffJson := mkDiffJson edits
        let json := json% {
          diff: $diffJson,
          suggestion: $suggestionText,
          range: $edit.range
        }
        let diffString :=
          if suggestion.diffGranularity matches .none then
            edits.foldl (· ++ ·.2) ""
          else
            mkDiffString edits
        let diffWidget := MessageData.ofWidget {
            id := ``tryThisDiffWidget
            javascriptHash := tryThisDiffWidget.javascriptHash
            props := return json
          } diffString
        let msg := m!"{preInfo}{diffWidget}{postInfo}"
        if suggestions.size == 1 && !forceList then
          m!"\n{msg}"
        else
          m!"\n" ++ MessageData.nest 2 m!"• {msg}"
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
* `forceList`: if `true`, suggestions will be displayed as a bulleted list even if there is only one.
-/
def _root_.Lean.MessageData.hint (hint : MessageData)
    (suggestions : Array Suggestion) (ref? : Option Syntax := none)
    (codeActionPrefix? : Option String := none)
    (forceList : Bool := false)
    : CoreM MessageData := do
  let ref := ref?.getD (← getRef)
  let suggs ← mkSuggestionsMessage suggestions ref codeActionPrefix? forceList
  return .tagged `hint (m!"\n\nHint: " ++ hint ++ suggs)
