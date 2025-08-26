/-
Copyright (c) 2021 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Mario Carneiro, Thomas Murrills
-/
module

prelude
public import Lean.CoreM
public import Lean.Message
public import Lean.Elab.InfoTree.Types
public import Lean.Data.Lsp.Basic
public import Lean.PrettyPrinter

public section

/-!
# "Try this" data types

This defines the data types used in constructing "try this" widgets for suggestion-providing tactics
and inline error-message hints, as well as basic infrastructure for generating info trees and
widget content there from.
-/

namespace Lean.Meta.Tactic.TryThis

open PrettyPrinter

/-! # Code action information -/

/-- A packet of information about a "Try this" suggestion
that we store in the infotree for the associated code action to retrieve. -/
structure TryThisInfo : Type where
  /-- The textual range to be replaced by one of the suggestions. -/
  range : Lsp.Range
  /--
  A list of suggestions for the user to choose from.
  Each suggestion may optionally come with an override for the code action title.
  -/
  suggestionTexts : Array (String × Option String)
  /-- The prefix to display before the code action for a "Try this" suggestion if no custom code
  action title is provided. If not provided, `"Try this: "` is used. -/
  codeActionPrefix? : Option String
  deriving TypeName

/-! # `Suggestion` data -/

-- TODO: we could also support `Syntax` and `Format`
/-- Text to be used as a suggested replacement in the infoview. This can be either a `TSyntax kind`
for a single `kind : SyntaxNodeKind` or a raw `String`.

Instead of using constructors directly, there are coercions available from these types to
`SuggestionText`. -/
inductive SuggestionText where
  /-- `TSyntax kind` used as suggested replacement text in the infoview. Note that while `TSyntax`
  is in general parameterized by a list of `SyntaxNodeKind`s, we only allow one here; this
  unambiguously guides pretty-printing. -/
  | tsyntax {kind : SyntaxNodeKind} : TSyntax kind → SuggestionText
  /-- A raw string to be used as suggested replacement text in the infoview. -/
  | string : String → SuggestionText
  deriving Inhabited

instance : ToMessageData SuggestionText where
  toMessageData
  | .tsyntax stx => stx
  | .string s => s

instance {kind : SyntaxNodeKind} : CoeHead (TSyntax kind) SuggestionText where
  coe := .tsyntax

instance : Coe String SuggestionText where
  coe := .string

/--
Style hooks for `Suggestion`s. See `SuggestionStyle.error`, `.warning`, `.success`, `.value`,
and other definitions here for style presets. This is an arbitrary `Json` object, with the following
interesting fields:
* `title`: the hover text in the suggestion link
* `className`: the CSS classes applied to the link
* `style`: A `Json` object with additional inline CSS styles such as `color` or `textDecoration`.
-/
@[expose] def SuggestionStyle := Json deriving Inhabited, ToJson

/-- Style as an error. By default, decorates the text with an undersquiggle; providing the argument
`decorated := false` turns this off. -/
@[deprecated "`SuggestionStyle` is not used anymore." (since := "2025-08-14")]
def SuggestionStyle.error (decorated := true) : SuggestionStyle :=
  let style := if decorated then
    json% {
      -- The VS code error foreground theme color (`--vscode-errorForeground`).
      color: "var(--vscode-errorForeground)",
      textDecoration: "underline wavy var(--vscode-editorError-foreground) 1pt"
    }
  else json% { color: "var(--vscode-errorForeground)" }
  json% { className: "pointer dim", style: $style }

/-- Style as a warning. By default, decorates the text with an undersquiggle; providing the
argument `decorated := false` turns this off. -/
@[deprecated "`SuggestionStyle` is not used anymore." (since := "2025-08-14")]
def SuggestionStyle.warning (decorated := true) : SuggestionStyle :=
  if decorated then
    json% {
      -- The `.gold` CSS class, which the infoview uses when e.g. building a file.
      className: "gold pointer dim",
      style: { textDecoration: "underline wavy var(--vscode-editorWarning-foreground) 1pt" }
    }
  else json% { className: "gold pointer dim" }

/-- Style as a success. -/
@[deprecated "`SuggestionStyle` is not used anymore." (since := "2025-08-14")]
def SuggestionStyle.success : SuggestionStyle :=
  -- The `.information` CSS class, which the infoview uses on successes.
  json% { className: "information pointer dim" }

/-- Style the same way as a hypothesis appearing in the infoview. -/
@[deprecated "`SuggestionStyle` is not used anymore." (since := "2025-08-14")]
def SuggestionStyle.asHypothesis : SuggestionStyle :=
  json% { className: "goal-hyp pointer dim" }

/-- Style the same way as an inaccessible hypothesis appearing in the infoview. -/
@[deprecated "`SuggestionStyle` is not used anymore." (since := "2025-08-14")]
def SuggestionStyle.asInaccessible : SuggestionStyle :=
  json% { className: "goal-inaccessible pointer dim" }

/-- Draws the color from a red-yellow-green color gradient with red at `0.0`, yellow at `0.5`, and
green at `1.0`. Values outside the range `[0.0, 1.0]` are clipped to lie within this range.

With `showValueInHoverText := true` (the default), the value `t` will be included in the `title` of
the HTML element (which appears on hover). -/
@[deprecated "`SuggestionStyle` is not used anymore." (since := "2025-08-14")]
def SuggestionStyle.value (t : Float) (showValueInHoverText := true) : SuggestionStyle :=
  let t := min (max t 0) 1
  json% {
    className: "pointer dim",
    -- interpolates linearly from 0º to 120º with 95% saturation and lightness
    -- varying around 50% in HSL space
    style: { color: $(s!"hsl({(t * 120).round} 95% {60 * ((t - 0.5)^2 + 0.75)}%)") },
    title: $(if showValueInHoverText then s!"Apply suggestion ({t})" else "Apply suggestion")
  }

/-- Holds a `suggestion` for replacement, along with `preInfo` and `postInfo` strings to be printed
immediately before and after that suggestion, respectively. It also includes an optional
`MessageData` to represent the suggestion in logs; by default, this is `none`, and `suggestion` is
used. -/
structure Suggestion where
  /-- Text to be used as a replacement via a code action. -/
  suggestion : SuggestionText
  /-- Optional info to be printed immediately before replacement text in a widget. -/
  preInfo? : Option String := none
  /-- Optional info to be printed immediately after replacement text in a widget. -/
  postInfo? : Option String := none
  /-- Optional style specification for the suggestion. If `none` (the default), the suggestion is
  styled as a text link. Otherwise, the suggestion can be styled as:
  * a status: `.error`, `.warning`, `.success`
  * a hypothesis name: `.asHypothesis`, `.asInaccessible`
  * a variable color: `.value (t : Float)`, which draws from a red-yellow-green gradient, with red
  at `0.0` and green at `1.0`.

  See `SuggestionStyle` for details.

  Note that this property is used only by the "try this" widget; it is ignored by the inline hint
  widget. -/
  style? : Option SuggestionStyle := none
  /-- How to represent the suggestion as `MessageData`. This is used only in the info diagnostic.
  If `none`, we use `suggestion`. Use `toMessageData` to render a `Suggestion` in this manner. -/
  messageData? : Option MessageData := none
  /-- How to construct the text that appears in the lightbulb menu from the suggestion text. If
  `none`, we use `fun ppSuggestionText => "Try this: " ++ ppSuggestionText`. Only the pretty-printed
  `suggestion : SuggestionText` is used here. -/
  toCodeActionTitle? : Option (String → String) := none
  deriving Inhabited

attribute [deprecated "The `style?` property is not used anymore." (since := "2025-08-14")] Suggestion.style?
attribute [deprecated "The `messageData?` property is not used anymore." (since := "2025-08-14")] Suggestion.messageData?

/- Use `toMessageData` of the suggestion text. -/
instance : ToMessageData Suggestion where
  toMessageData s := toMessageData s.suggestion

instance : Coe SuggestionText Suggestion where
  coe t := { suggestion := t }

/-! # Formatting -/

/-- Yields `(indent, column)` given a `FileMap` and a `String.Range`, where `indent` is the number
of spaces by which the line that first includes `range` is initially indented, and `column` is the
column `range` starts at in that line. -/
def getIndentAndColumn (map : FileMap) (range : String.Range) : Nat × Nat :=
  let start := map.source.findLineStart range.start
  let body := map.source.findAux (· ≠ ' ') range.start start
  ((body - start).1, (range.start - start).1)

/--
An option allowing the user to customize the ideal input width. Defaults to 100.
This option controls output format when
the output is intended to be copied back into a lean file -/
register_builtin_option format.inputWidth : Nat := {
  /- The default maximum width of an ideal line in source code. -/
  defValue := 100
  descr := "ideal input width"
}

/-- Get the input width specified in the options -/
def getInputWidth (o : Options) : Nat := format.inputWidth.get o

namespace SuggestionText

/-- Pretty-prints a `SuggestionText` as a `Format`. If the `SuggestionText` is some `TSyntax kind`,
we use the appropriate pretty-printer; strings are coerced to `Format`s as-is. -/
def pretty : SuggestionText → CoreM Format
  | .tsyntax (kind := kind) stx => ppCategory kind stx
  | .string text => return text

/- Note that this is essentially `return (← s.pretty).prettyExtra w indent column`, but we
special-case strings to avoid converting them to `Format`s and back, which adds indentation after each newline. -/
/-- Pretty-prints a `SuggestionText` as a `String` and wraps with respect to the pane width,
indentation, and column, via `Format.prettyExtra`. If `w := none`, then
`w := getInputWidth (← getOptions)` is used. Raw `String`s are returned as-is. -/
def prettyExtra (s : SuggestionText) (w : Option Nat := none)
    (indent column : Nat := 0) : CoreM String :=
  match s with
  | .tsyntax (kind := kind) stx => do
    let w ← match w with | none => do pure <| getInputWidth (← getOptions) | some n => pure n
    return (← ppCategory kind stx).pretty w indent column
  | .string text => return text

end SuggestionText

/-- Converts a `Suggestion` to `Json` in `CoreM`. We need `CoreM` in order to pretty-print syntax.

This also returns a `String × Option String` consisting of the pretty-printed text and any custom
code action title if `toCodeActionTitle?` is provided.

If `w := none`, then `w := getInputWidth (← getOptions)` is used.
-/
def Suggestion.toJsonAndInfoM (s : Suggestion) (w : Option Nat := none) (indent column : Nat := 0) :
    CoreM (Json × String × Option String) := do
  let text ← s.suggestion.prettyExtra w indent column
  let mut json := [("suggestion", (text : Json))]
  if let some preInfo := s.preInfo? then json := ("preInfo", preInfo) :: json
  if let some postInfo := s.postInfo? then json := ("postInfo", postInfo) :: json
  return (Json.mkObj json, text, s.toCodeActionTitle?.map (· text))

/--
Represents processed data for a collection of suggestions that can be passed to a widget and pushed
in an info leaf.

It contains the following data:
* `suggestions`: tuples of the form `(j, t, p)` where `j` is JSON containing a suggestion and its
  pre- and post-info, `t` is the text to be inserted by the suggestion, and `p` is the code action
  prefix thereof.
* `info`: the `TryThisInfo` data corresponding to a collection of suggestions
* `range`: the range at which the suggestion is to be applied.
-/
structure ProcessedSuggestions where
  suggestions : Array (Json × String × Option String)
  info : Elab.Info
  range : Lsp.Range

/--
Processes an array of `Suggestion`s into data that can be used to construct a code-action info leaf
and "try this" widget.
-/
def processSuggestions (ref : Syntax) (range : String.Range) (suggestions : Array Suggestion)
    (codeActionPrefix? : Option String) : CoreM ProcessedSuggestions := do
  let map ← getFileMap
  -- FIXME: this produces incorrect results when `by` is at the beginning of the line, i.e.
  -- replacing `tac` in `by tac`, because the next line will only be 2 space indented
  -- (less than `tac` which starts at column 3)
  let (indent, column) := getIndentAndColumn map range
  let suggestions ← suggestions.mapM (·.toJsonAndInfoM (indent := indent) (column := column))
  let suggestionTexts := suggestions.map (·.2)
  let ref := Syntax.ofRange <| ref.getRange?.getD range
  let range := map.utf8RangeToLspRange range
  let info := .ofCustomInfo {
    stx := ref
    value := Dynamic.mk { range, suggestionTexts, codeActionPrefix? : TryThisInfo }
  }
  return { info, suggestions, range }
