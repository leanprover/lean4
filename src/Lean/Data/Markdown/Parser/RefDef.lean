/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Thrane Christiansen
-/
module

prelude
public import Init.While
public import Lean.Data.Markdown.Basic
public import Lean.Data.Markdown.InlineSource
import Lean.Data.Markdown.Text

namespace Lean.Markdown


/-!
# Link Reference Definitions

Parsers for link reference definitions (CommonMark §4.7), which the block parser extracts from the
front of paragraphs: at a setext heading underline, and after the block structure is complete.
-/

variable {s : String.Slice}

/--
Parses the content of a link label (CommonMark §6.3) at `cur`, which is positioned just after the
`[`. A label may span lines, but blank lines and unescaped brackets are not permitted inside it, and
it must contain at least one non-whitespace character and at most 999 characters. Returns the
label's lines and the cursor, which is positioned at the closing `]`.
-/
public def parseLinkLabel? (cur : InlineCursor s) : Option (Lines s × InlineCursor s) := do
  let labelStart := cur.startPos
  let mut cur := cur
  let mut len := 0
  let mut sawNonWs := false
  let mut sawNewline := false
  while len < 1000 do
    let some c := cur.front? | break
    let curNext := cur.drop1
    if c == '\\' && Option.any isAsciiPunctuation curNext.front? then
      sawNonWs := true
      sawNewline := false
      cur := curNext.drop1
      len := len + 2
    else if c == ']' then
      guard sawNonWs
      return (cur.source.linesBetween labelStart cur.startPos, cur)
    else if c == '[' then
      failure
    else if let some (_, afterEnding) := cur.parseLineEnding? then
      guard !sawNewline  -- blank line in label
      sawNewline := true
      cur := afterEnding
      len := len + 1
    else
      if c != ' ' && c != '\t' then
        sawNonWs := true
        sawNewline := false
      cur := curNext
      len := len + 1
  none

/--
Parses the destination of a link reference definition at the head of `cur`, in the
bracketed `<url>` or unbracketed form. Returns the destination and the cursor, which is positioned
just past it. Fails
on an unclosed `<`, an empty destination, unbalanced parens, or an embedded line ending.
-/
def parseRefDefUrl? (cur : InlineCursor s) : Option (LinkDestination s × InlineCursor s) := do
  let urlStart := cur.startPos
  if cur.front? == some '<' then
    -- Bracketed: read up to the next `>`; reject `<` and line endings.
    let openAngle ← cur.charSubslice?
    let mut cur := cur.drop1
    let urlContentStart := cur.startPos
    let mut closeAngle? : Option s.Subslice := none
    while !cur.isEmpty && closeAngle?.isNone do
      let c := cur.front
      let curNext := cur.drop1
      if c == '\\' && Option.any isAsciiPunctuation curNext.front? then
        cur := curNext.drop1
      else if c == '>' then
        closeAngle? := cur.charSubslice?
        cur := curNext
      else if c == '<' || c == '\n' || c == '\r' then
        failure
      else
        cur := curNext
    let closeAngle ← closeAngle?
    let destination : LinkDestination s :=
      { angles? := some (openAngle, closeAngle)
        url := subsliceClamped urlContentStart closeAngle.startInclusive }
    return (destination, cur)
  else
    -- Unbracketed: stop at whitespace/control; balance parens.
    guard !cur.isEmpty
    let mut cur := cur
    let mut parenDepth : Nat := 0
    while !cur.isEmpty do
      let c := cur.front
      let curNext := cur.drop1
      if c == '\\' && Option.any isAsciiPunctuation curNext.front? then
        cur := curNext.drop1
      else if c.isWhitespace then
        break
      else if c == '(' then
        parenDepth := parenDepth + 1
        cur := curNext
      else if c == ')' then
        if parenDepth == 0 then break
        parenDepth := parenDepth - 1
        cur := curNext
      else if c.toNat < 0x20 then
        break
      else
        cur := curNext
    guard <| cur.startPos != urlStart  -- non-empty destination
    guard <| parenDepth == 0
    return ({ angles? := none, url := subsliceClamped urlStart cur.startPos }, cur)

/--
Skips the whitespace gap between a link reference definition's `:` and its destination: spaces,
tabs, and at most one line ending. Returns `none` if a blank line (two line endings) is encountered.
-/
def skipRefDefDestGap (cur : InlineCursor s) : Option (InlineCursor s) := do
  let mut cur := cur
  let mut endingsSeen := 0
  repeat
    let some c := cur.front? | break
    if c == ' ' || c == '\t' then cur := cur.drop1
    else if let some (_, afterEnding) := cur.parseLineEnding? then
      endingsSeen := endingsSeen + 1
      if endingsSeen ≥ 2 then failure
      cur := afterEnding
    else break
  return cur

/--
Consumes the spaces and tabs at `cur` and then the line ending, if there is one, returning the
cursor after them. Fails when the line has other content after `cur`.
-/
def consumeRefDefLineEnd (cur : InlineCursor s) : Option (InlineCursor s) := do
  let mut cur := cur
  while cur.front? == some ' ' || cur.front? == some '\t' do
    cur := cur.drop1
  if cur.isEmpty then return cur
  if let some (_, afterEnding) := cur.parseLineEnding? then return afterEnding
  none

/--
Parses the optional title of a link reference definition after its destination, together with the
spaces, tabs, and line ending that follow it. Returns the title and the cursor after the line ending
or at the end of the input.

The title is delimited by `"…"`, `'…'`, or `(…)`. It may be on the line of the destination, after
at least one space or tab, or on the next line, after optional indentation.

Blank lines are not permitted inside the title, nor is an unescaped `(` inside a `(…)` title. After
the closing delimiter, only spaces and tabs may follow on the line, then an optional line ending;
otherwise the title attempt fails so that the caller can fall back to a definition without a title.
-/
def parseRefDefTitle? (cur : InlineCursor s) : Option (LinkTitle s × InlineCursor s) := do
  -- Locate the title opener: on the line of the destination after spaces or tabs, or on the next
  -- line after optional indentation.
  let mut sawWs := false
  let mut p := cur
  while p.front? == some ' ' || p.front? == some '\t' do
    sawWs := true
    p := p.drop1
  let mut openerR : InlineCursor s := p
  if let some (_, afterEnding) := p.parseLineEnding? then
    openerR := afterEnding
    while openerR.front? == some ' ' || openerR.front? == some '\t' do
      openerR := openerR.drop1
  else
    guard sawWs
  let opener ← openerR.front?
  guard <| opener == '"' || opener == '\'' || opener == '('
  let openerRange ← openerR.charSubslice?
  -- Parse content up to a matching closer; reject blank lines and unescaped
  -- `(` in `(...)` titles.
  let closer : Char := if opener == '(' then ')' else opener
  let afterOpener := openerR.drop1
  let titleContentStart := afterOpener.startPos
  let mut tt := afterOpener
  let mut titleContentEnd := titleContentStart
  let mut closerRange? : Option s.Subslice := none
  let mut bail := false
  let mut lastWasNewline := false
  while !tt.isEmpty && closerRange?.isNone && !bail do
    let c := tt.front
    let curPos := tt.startPos
    let ttNext := tt.drop1
    if c == '\\' && Option.any isAsciiPunctuation ttNext.front? then
      tt := ttNext.drop1
      lastWasNewline := false
    else if c == closer then
      titleContentEnd := curPos
      closerRange? := tt.charSubslice?
      tt := ttNext
    else if c == opener && opener == '(' then
      bail := true  -- unescaped `(` inside a `(...)` title is forbidden
    else if let some (_, afterEnding) := tt.parseLineEnding? then
      if lastWasNewline then bail := true
      else
        lastWasNewline := true
        tt := afterEnding
    else
      if c != ' ' && c != '\t' then lastWasNewline := false
      tt := ttNext
  guard !bail
  let closerRange ← closerRange?
  let afterEol ← consumeRefDefLineEnd tt
  let title : LinkTitle s :=
    { opener := openerRange, content := cur.source.linesBetween titleContentStart titleContentEnd,
      closer := closerRange }
  return (title, afterEol)

/--
Tries to parse a CommonMark link reference definition that starts at `start` in `source`. Recognizes
both bracketed `<url>` and unbracketed link destinations, and optional `"…"`/`'…'`/`(…)` titles
(which may appear on the line that follows the URL). The label may span multiple lines, but blank
lines are not permitted inside it.

Returns the definition plus the position one past the last consumed character.
-/
public def parseLinkRefDef? (source : InlineSource s) (start : s.Pos) :
    Option (RefDef s × s.Pos) := do
  -- `InlineSource.ofLines` has removed each line's leading spaces and tabs, so `start` is at `[`.
  let cur := source.cursor start source.stopPos
  -- `[label]`.
  let (openBracket, cur) ← cur.parseChar? '['
  let (label, cur) ← parseLinkLabel? cur
  let (closeBracket, cur) ← cur.parseChar? ']'
  -- `:`.
  let (colon, cur) ← cur.parseChar? ':'
  -- Whitespace (including up to one newline) before the destination.
  let cur ← skipRefDefDestGap cur
  -- Destination.
  let (destination, afterUrl) ← parseRefDefUrl? cur
  -- Optional title; on a syntactic failure or on trailing junk, fall back to
  -- a no-title interpretation, in which case the URL itself must end the
  -- line.
  let (title?, finalRest) ←
    (parseRefDefTitle? afterUrl |>.map fun (t, cur) => (some t, cur)) <|>
    (consumeRefDefLineEnd afterUrl |>.map fun cur => (none, cur))
  return ({ openBracket, label, closeBracket, colon, destination, title? }, finalRest.startPos)

/--
Greedily consumes link ref definitions from the front of `source`.

Returns the extracted `linkRefDef` blocks and a residual `InlineSource`.
-/
public def extractRefDefs (source : InlineSource s) :
    Array (Block.Raw s) × InlineSource s := Id.run do
  let mut defs : Array (Block.Raw s) := #[]
  let mut p := source.startPos
  let mut keep := true
  while keep && p < source.stopPos do
    match parseLinkRefDef? source p with
    | none => keep := false
    | some (m, posAfter) =>
      defs := defs.push (.linkRefDef m)
      p := posAfter
  return (defs, source.dropUpTo p)
