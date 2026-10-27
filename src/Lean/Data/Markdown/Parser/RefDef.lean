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
import Lean.Data.Markdown.Parser.LinkSyntax

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

The title is delimited by `"…"`, `'…'`, or `(…)`. It may be on the line of the destination, after at
least one space or tab, or on the next line, after optional indentation.

After the closing delimiter, only spaces and tabs may follow on the same line. Otherwise the title
attempt fails so that the caller can fall back to a definition without a title.
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
  let (title, afterTitle) ← parseLinkTitle? openerR
  let afterEol ← consumeRefDefLineEnd afterTitle
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
  -- Destination, which must be nonempty unless it is bracketed.
  let (destination, afterUrl) ← parseLinkDestination? cur
  guard (destination.angles?.isSome || afterUrl.startPos != cur.startPos)
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
