/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Thrane Christiansen
-/
module

prelude
public import Init.While
import Init.Data.String.Iterate
import Init.Data.Range.Polymorphic.Iterators
import Init.Data.Range.Polymorphic.Nat
import Init.Data.Array.QSort.Basic
import Init.Data.String.Compare
public import Lean.Data.Markdown.Block
public import Lean.Data.Markdown.InlineCursor
public import Lean.Data.Markdown.Parser.RefDef
import Lean.Data.Markdown.Parser.Cursor
import Lean.Data.Markdown.Parser.BlockZipper
import Lean.Data.Markdown.Parser.Html

namespace Lean.Markdown


/-!
# Pass 1: Block Parser

CommonMark is parsed in two passes:
1. The first pass identifies the block structure of the document and accumulates the definitions of
   ref-style links.
2. Within each block, the second pass finds the structure of inlines and applies fallback rules for
   poorly nested or mismatched delimiters.

This file contains the first pass. Ref-style link labels are compared modulo `normalizeLabel`, whose
case folding covers only ASCII, Latin-1, and Greek, rather than the full Unicode case fold specified
by CommonMark.
-/

variable {s : String.Slice}

/--
Counts tab-aware leading whitespace (CommonMark §2.2): each tab advances to the next 4-column tab
stop, computed relative to the cursor's current column. Returns the advanced cursor and the total
number of columns that it consumes. Tabs are always crossed in full.
-/
def countIndentCols (c : Cursor s) : Cursor s × Columns := Id.run do
  let mut c := c
  let mut cols : Columns := 0
  while h : c.pos < c.stop do
    let h' := String.Slice.Pos.ne_endPos_of_lt h
    let ch := c.pos.get h'
    if ch == ' ' then
      cols := cols.space
      c := { c with pos := c.pos.next h', col := c.col.space, partialTab := false }
    else if ch == '\t' then
      cols := cols + c.col.tabWidth
      c := { c with pos := c.pos.next h', col := c.col.tab, partialTab := false }
    else
      break
  return (c, cols)

/--
The rest of a line after its indentation, together with the width of that indentation.

Whether a line begins a block depends on how far it is indented and on what follows the indentation
(CommonMark §4): four or more columns begin indented code, and the other blocks allow at most
three. The indentation is measured in columns, and tabs advance to the next tab stop (CommonMark
§2.2).
-/
structure IndentedLine (s : String.Slice) where
  /-- The cursor at the first character after the indentation. -/
  after : Cursor s
  /-- The width of the indentation. -/
  indent : Columns

/-- The line at `c` after its indentation. -/
def Cursor.skipIndent (c : Cursor s) : IndentedLine s :=
  let (after, indent) := countIndentCols c
  { after, indent }

/--
Consumes up to `maxCols` columns of leading whitespace at `c`, with tab-aware column counting.
Returns the advanced cursor and the number of columns actually consumed.

Tabs may be split: if a tab would move the cursor past `maxCols`, the position stays at the tab and
the column count advances by exactly the requested amount, leaving “leftover” tab columns for
subsequent consumers (CommonMark §2.2's partial-tab rule).
-/
def consumeIndentCapped (c : Cursor s) (maxCols : Columns) : Cursor s × Columns := Id.run do
  let mut c := c
  let mut cols : Columns := 0
  while h : c.pos < c.stop do
    if cols ≥ maxCols then break
    let h' := String.Slice.Pos.ne_endPos_of_lt h
    let ch := c.pos.get h'
    if ch == ' ' then
      cols := cols.space
      c := { c with pos := c.pos.next h', col := c.col.space, partialTab := false }
    else if ch == '\t' then
      let width := c.col.tabWidth
      if cols + width > maxCols then
        c := c.intoTab (maxCols - cols)
        cols := maxCols
      else
        cols := cols + width
        c := { c with pos := c.pos.next h', col := c.col.tab, partialTab := false }
    else
      break
  return (c, cols)

/--
The line at `c` as a line of an indented code block: its content after four columns of indentation.
-/
def indentedCodeLine (c : Cursor s) : VerbatimLine s :=
  let (afterIndent, _) := consumeIndentCapped c 4
  afterIndent.verbatimLine

/-- `text` without its trailing spaces and tabs. -/
def trimTrailingWs (text : s.Subslice) : s.Subslice :=
  trimTrailing text fun c => c == ' ' || c == '\t'

/-- Moves the start of `line` past up to `indent` leading spaces. -/
def dropIndent (line : s.Subslice) (indent : Nat) : s.Subslice := Id.run do
  let mut p := line.startInclusive
  for _ in 0...indent do
    if h : p < line.endExclusive then
      let h' := String.Slice.Pos.ne_endPos_of_lt h
      if p.get h' == ' ' then p := p.next h' else break
    else break
  return subsliceClamped p line.endExclusive

/-- Splits `text` into lines, each excluding its line ending (`\r\n`, `\r`, or `\n`). -/
partial def splitLines (text : s.Subslice) : Array s.Subslice :=
  go text.startInclusive text.startInclusive #[]
where
  /-- Scans from `p`. `lineStart` is the start of the current line and `lines` the lines so far. -/
  go (p lineStart : s.Pos) (lines : Array s.Subslice) : Array s.Subslice :=
    if h : p < text.endExclusive then
      let h' := String.Slice.Pos.ne_endPos_of_lt h
      let c := p.get h'
      if c == '\n' || c == '\r' then
        let q := (parseLineEnding? text p).getD (p.next h')
        go q q (lines.push (subsliceClamped lineStart p))
      else
        go (p.next h') lineStart lines
    else if lineStart < p then
      lines.push (subsliceClamped lineStart p)
    else
      lines

/--
A successful ATX heading match.
-/
structure AtxHeadingMatch (s : String.Slice) where
  /-- The heading level (1-6). -/
  level : Nat
  /-- The opening `#`s. -/
  hashes : s.Subslice
  /-- The trimmed inline content. -/
  content : s.Subslice
  /-- The optional closing hashes. -/
  closeHashes : Option s.Subslice

/--
Parses an ATX heading at `line`. Trailing whitespace is trimmed from `content`.
-/
def parseAtxHeading? (line : IndentedLine s) : Option (AtxHeadingMatch s) := do
  let { after := c, indent } := line
  guard (indent ≤ 3)
  let hashStart := c.pos
  -- CommonMark §4.2 caps ATX heading levels at 6. Up to 7 hashes are counted, so sequences of 7 or
  -- more fall through the `count ≤ 6` guard below as non-headings.
  let mut rest := c
  let mut count := 0
  while rest.front? == some '#' && count < 7 do
    count := count + 1
    rest := rest.next
  guard (count > 0 && count ≤ 6)
  if let some next := rest.front? then
    guard (next == ' ' || next == '\t')
  let hashes := subsliceClamped hashStart rest.pos
  -- Skip whitespace (spaces or tabs) between the hashes and the content.
  let (cAfterGap, _) := countIndentCols rest
  let contentStart := cAfterGap.pos
  let mut content := trimTrailingWs cAfterGap.toEol
  -- Optional closing `#` sequence: a trailing sequence of `#` characters that
  -- is either preceded by a space/tab or extends to the start of content
  -- (CommonMark §4.2). Strip it from the content.
  let mut closeStart := content.endExclusive
  while contentStart < closeStart do
    match closeStart.prev? with
    | some q => if q.get? == some '#' then closeStart := q else break
    | none => break
  let mut closeHashes? : Option s.Subslice := none
  if closeStart < content.endExclusive then
    if closeStart == contentStart then
      closeHashes? := some (subsliceClamped closeStart content.endExclusive)
      content := subsliceClamped contentStart closeStart
    else if let some beforeClose := closeStart.prev? then
      let cb := beforeClose.get?
      if cb == some ' ' || cb == some '\t' then
        closeHashes? := some (subsliceClamped closeStart content.endExclusive)
        content := trimTrailingWs (subsliceClamped contentStart closeStart)
  return { level := count, hashes, content, closeHashes := closeHashes? }

/-- The result of checking a line for a thematic break. -/
inductive ThematicBreakCheck (s : String.Slice) where
  /-- The line is a thematic break. -/
  | isBreak
  /--
  The scan of the line failed at `pos`, which is the first character that is neither the marker
  character nor a space or tab, or the end of the line when it has fewer than three marker
  characters. A scan that starts before `pos` and after the first marker fails at `pos` too.
  -/
  | failsAt (pos : s.Pos)
  /-- The line is indented too far or does not begin with a marker character. -/
  | notCandidate

/--
Checks whether `line` is a thematic break: up to 3 leading spaces, followed by 3+ matching
`*`/`-`/`_` characters, with only spaces or tabs allowed between or after them (CommonMark §4.1).
-/
def checkThematicBreak (line : IndentedLine s) : ThematicBreakCheck s := Id.run do
  let { after := c, indent } := line
  if indent > 3 then return .notCandidate
  let some markerChar := c.front? | return .notCandidate
  if markerChar != '*' && markerChar != '-' && markerChar != '_' then
    return .notCandidate
  let mut rest := c
  let mut markerCount := 0
  repeat
    let some ch := rest.front? | break
    if ch == markerChar then
      markerCount := markerCount + 1
      rest := rest.next
    else if ch == ' ' || ch == '\t' then
      rest := rest.next
    else
      return .failsAt rest.pos
  return if markerCount ≥ 3 then .isBreak else .failsAt rest.pos

@[inherit_doc checkThematicBreak]
def isThematicBreak (line : IndentedLine s) : Bool :=
  match checkThematicBreak line with
  | .isBreak => true
  | _ => false

/--
Parses a setext heading underline (CommonMark §4.3): up to three leading spaces, then a sequence of
`=` (level 1) or `-` (level 2), then optional trailing whitespace. Returns the heading level and the
marker sequence.

The `---` underline overlaps with the thematic-break syntax. The caller must enforce the precedence
rule: setext header parsing applies only when an open paragraph immediately precedes the underline.
Otherwise, the same line is interpreted as a thematic break.
-/
def parseSetextUnderline? (line : IndentedLine s) : Option (Nat × s.Subslice) := do
  let { after := c, indent } := line
  guard (indent ≤ 3)
  let markerChar ← c.front?
  guard (markerChar == '=' || markerChar == '-')
  let (cAfterSequence, _) := c.advanceWhile (· == markerChar)
  -- After the sequence, only whitespace is permitted to end of line.
  let (cAfterWs, _) := cAfterSequence.advanceWhile fun ch =>
    ch == ' ' || ch == '\t'
  guard cAfterWs.isEmpty
  let level := if markerChar == '=' then 1 else 2
  return (level, subsliceClamped c.pos cAfterSequence.pos)

/-- Parses an opening code fence at `line`. -/
def parseFenceOpen? (line : IndentedLine s) : Option (FenceInfo s × s.Subslice) := do
  let { after := c, indent } := line
  guard (indent ≤ 3)
  let fenceChar ← c.front? >>= FenceChar.ofChar?
  let fenceStart := c.pos
  let (cAfterFence, count) := c.advanceWhile (· == fenceChar.toChar)
  guard (count ≥ 3)
  let openFence := subsliceClamped fenceStart cAfterFence.pos
  let (cAfterWs, _) := cAfterFence.advanceWhile fun ch => ch == ' ' || ch == '\t'
  let info := trimTrailingWs cAfterWs.toEol
  -- A backtick fence's info string may not contain backticks.
  if fenceChar == .backtick then
    for ch in info.toSlice do
      guard (ch != '`')
  let infoString? : Option s.Subslice := if info.toSlice.isEmpty then none else some info
  return ({ fenceChar, fenceLen := count, openIndent := indent, infoString? }, openFence)

/--
Parses a closing fence on a line whose container prefixes have already been consumed.

The closing fence must match `info`'s character, be at least as long as the opener, and be followed
only by spaces or tabs.
-/
def parseFenceClose? (line : IndentedLine s) (info : FenceInfo s) : Option s.Subslice := do
  let { after := cAtFence, indent } := line
  guard (indent ≤ 3)
  guard <| cAtFence.front? == some info.fenceChar.toChar
  let (cAfterFence, count) := cAtFence.advanceWhile (· == info.fenceChar.toChar)
  guard <| count ≥ info.fenceLen
  guard cAfterFence.isBlank
  return subsliceClamped cAtFence.pos cAfterFence.pos

/--
Parses a single blockquote marker (`>` plus optional space). Returns the marker and a cursor that is
positioned just past the consumed prefix (with column adjusted, possibly mid-tab per CommonMark
§2.2's partial tab rule).
-/
def parseBlockquoteMarker? (line : IndentedLine s) : Option (s.Subslice × Cursor s) := do
  let { after := c, indent } := line
  guard (indent ≤ 3)
  guard (c.front? == some '>')
  let afterMarker := c.next
  let marker := subsliceClamped c.pos afterMarker.pos
  -- The blockquote marker `>` is followed by an optional single space (or
  -- one column of a tab, per CommonMark §2.2's partial-tab rule).
  match afterMarker.front? with
  | some ' ' => return (marker, afterMarker.next)
  | some '\t' =>
    -- A tab that spans one column is crossed in full; otherwise one of its columns is consumed.
    if afterMarker.col.tabWidth == 1 then
      return (marker, afterMarker.next)
    else
      return (marker, afterMarker.intoTab 1)
  | _ => return (marker, afterMarker)

/--
A successful list marker match.
-/
structure ListMarkerMatch (s : String.Slice) where
  /-- The marker itself. -/
  marker : s.Subslice
  /-- A cursor that is positioned just past the marker and any consumed trailing whitespace. -/
  after : Cursor s
  /-- The marker's kind.-/
  kind : ListKind
  /--
  The column distance from the input cursor to `after`, which is the minimum indentation of
  subsequent continuation lines.
  -/
  contentColumn : Columns

/-- Parses a bullet or ordered list marker at `line`. -/
def parseListMarker? (line : IndentedLine s) : Option (ListMarkerMatch s) := do
  let { after := c, indent } := line
  guard (indent ≤ 3)
  -- The content column is measured from the column before the indentation.
  let initialCol := c.col - indent
  let ch ← c.front?
  -- After matching the marker, compute the listItem's content column. Per
  -- CommonMark §5.2: 1 ≤ N ≤ 4 cols of whitespace that follow the marker are
  -- absorbed into the listItem prefix; if the line is empty after the marker
  -- or has 5+ cols of whitespace (i.e., the content is itself indented
  -- code), the listItem absorbs only one col of whitespace. Tabs may be
  -- partially consumed (CommonMark §2.2).
  let determineContent (afterMarker : Cursor s) : Option (Cursor s) := do
    if afterMarker.isEmpty then
      return { afterMarker with col := afterMarker.col.space }
    let nextC ← afterMarker.front?
    guard <| nextC == ' ' || nextC == '\t'
    let (afterWsCursor, wsCols) := countIndentCols afterMarker
    let contentBlank := afterWsCursor.isEmpty
    let absorbCols : Columns :=
      if contentBlank || wsCols ≥ 5 then 1
      else wsCols
    let (cursorAfter, _) := consumeIndentCapped afterMarker absorbCols
    return cursorAfter
  -- Bullet markers
  if ch == '*' || ch == '-' || ch == '+' then
    let afterMarker := c.next
    let kind : BulletKind :=
      if ch == '*' then .star
      else if ch == '-' then .hyphen
      else .plus
    let cursorAfter ← determineContent afterMarker
    return {
      marker := subsliceClamped c.pos afterMarker.pos
      after := cursorAfter
      kind := .bullet kind
      contentColumn := cursorAfter.col - initialCol
    }
  -- Ordered markers
  if ch.isDigit then
    let mut rest := c
    let mut digits := 0
    let mut value : Nat := 0
    -- CommonMark §5.2: an ordered list marker has 1–9 digits. Up to 10 are counted, so sequences of
    -- 10 or more digits fall through the `digits ≤ 9` guard below.
    while digits < 10 do
      let some digit := rest.front? | break
      if !digit.isDigit then break
      value := value * 10 + (digit.toNat - '0'.toNat)
      digits := digits + 1
      rest := rest.next
    guard (digits != 0)
    guard (digits ≤ 9)
    let delim ← rest.front?
    guard (delim == '.' || delim == ')')
    let afterMarker := rest.next
    let orderedDelim : OrderedDelim := if delim == '.' then .dot else .rparen
    let cursorAfter ← determineContent afterMarker
    return {
      marker := subsliceClamped c.pos afterMarker.pos
      after := cursorAfter
      kind := .ordered value orderedDelim
      contentColumn := cursorAfter.col - initialCol
    }
  failure

/--
Parses the start of an HTML block at `line` (CommonMark §4.6): after up to three spaces of
indentation, a `<` that begins one of the seven start conditions. Returns the block's kind.
-/
def parseHtmlBlockStart? (line : IndentedLine s) : Option HtmlBlockKind := do
  let { after := c, indent } := line
  guard (indent ≤ 3)
  guard (c.front? == some '<')
  let afterLt := c.next
  match afterLt.front? with
  | some '!' =>
    let afterBang := afterLt.next
    if startsWithAscii afterBang.toEol "--" then return .comment
    if startsWithAscii afterBang.toEol "[CDATA[" then return .cdata
    guard (Option.any Char.isAlpha afterBang.front?)
    return .declaration
  | some '?' => return .processingInstruction
  | _ =>
    let isClosing := afterLt.front? == some '/'
    let nameStart := if isClosing then afterLt.next else afterLt
    guard (Option.any Char.isAlpha nameStart.front?)
    let (afterName, _) := nameStart.advanceWhile Char.isAlphanum
    let name := subsliceClamped nameStart.pos afterName.pos
    let delimited :=
      match afterName.front? with
      | none | some ' ' | some '\t' | some '>' => true
      | _ => false
    if !isClosing && delimited && isRawTextTagName name then return .rawText
    if isBlockTagName name && (delimited || startsWithAscii afterName.toEol "/>") then
      return .blockTag
    let src := InlineSource.ofLines (.singleton (subsliceClamped afterLt.pos c.stop))
    guard (parseCompleteTagLine? (src.cursor src.startPos src.stopPos)).isSome
    return .completeTag

/--
Whether a list marker that was matched at the current cursor is allowed to interrupt an open
paragraph (CommonMark §5.2):
 * An empty list item cannot interrupt a paragraph
 * An ordered list marker can interrupt only if its start number is `1`.

`after` is positioned just past the marker.
-/
def listMarkerInterruptsParagraph (after : Cursor s) (kind : ListKind) : Bool :=
  !after.isBlank
  && match kind with
     | .ordered start _ => start == 1
     | .bullet _ => true

/--
Whether `line` begins a block rather than paragraph text, which decides lazy continuation
(CommonMark §5.1): a paragraph inside a blockquote or list item continues onto a line without the
container's marker, as long as that line is paragraph text. A blank line, a blockquote or list
marker, an ATX heading, a code fence, a thematic break, or the start of an HTML block ends the
paragraph instead.

Indentation is paragraph text here, because an indented code block cannot interrupt a paragraph
(CommonMark §4.4). Any list marker begins a block here, since the §5.2 restrictions on which list
items may interrupt a paragraph apply only when the paragraph is the innermost open block.
-/
def isInterrupt (line : IndentedLine s) : Bool :=
  -- A line that interrupts is examined again by `openLeafBlock`, which repeats these checks. The
  -- repetition is cheap: it is paid once per interrupting line, and the HTML check, the only one
  -- that allocates, runs only for lines that begin with `<`.
  line.after.isEmpty ||
  (parseBlockquoteMarker? line).isSome ||
  (parseListMarker? line).isSome ||
  (parseAtxHeading? line).isSome ||
  (parseFenceOpen? line).isSome ||
  Option.any (·.interruptsParagraph) (parseHtmlBlockStart? line) ||
  isThematicBreak line

/-!
# Processing Lines

Lines are processed one at a time. A kind of rightward-only zipper is maintained, allowing blocks to
be added at the lower right of the syntax tree.

Each step of the pipeline is a `ProcessM Unit` that is named after its description in the CommonMark
spec. Steps that produce the line's final zipper end the pipeline with `finishLine`, while steps
that only mutate the in-flight state fall through to the next.
-/

/--
The state that flows through the late (post-close) steps of `processLine`.
-/
structure LineState (s : String.Slice) where
  /-- The in-progress document. -/
  zipper : BlockZipper s
  /-- The cursor that advances through the block-inducing prefixes of the line. -/
  cursor : Cursor s

/--
The state during the early container-continuation phase that tracks the length of the suffix of the
zipper's spine (that is, parent blocks) that are continued on this line.
-/
structure ContState (s : String.Slice) extends LineState s where
  /-- The number of inner spine frames that continued on this line. -/
  matched : Nat
  /-- The matched counter is always a valid prefix length of the spine. -/
  matched_le : matched ≤ zipper.spine.size

/--
The monad for line processing after containers that need closing have been closed.

The “exception” channel returns the line's final `BlockZipper` early.
-/
abbrev ProcessM (s : String.Slice) := EStateM (BlockZipper s) (LineState s)

/--
The monad for determining which containers should continue for a given line.
-/
abbrev ContainerM (s : String.Slice) := EStateM (BlockZipper s) (ContState s)

/-!
A state that is read with `get` is shared with the monad, so extending one of the zipper's arrays
would copy the array. The zipper should be changed only either inside `modify` or after `takeState`
has taken the state out of the monad.
-/

/--
Takes the state out of the monad, leaving behind one with an empty zipper, so that the zipper's
arrays can be extended in place. The caller puts a state back with `set`, or ends the line with
`finishLine`.
-/
@[inline] def takeState : ProcessM s (LineState s) :=
  modifyGet fun st => (st, { st with zipper := .empty })

@[inherit_doc Lean.Markdown.takeState, inline]
def ContainerM.takeState : ContainerM s (ContState s) :=
  modifyGet fun st => (st, { st with zipper := .empty, matched := 0, matched_le := Nat.zero_le _ })

/-- Ends the processing of the current line, with `z` as the document so far. -/
@[inline] def finishLine [MonadExcept (BlockZipper s) m] (z : BlockZipper s) : m α := throw z

/--
Ends the processing of the current line with the zipper that `f` produces from the current one.
-/
@[inline] def finishLineWith (f : BlockZipper s → BlockZipper s) : ProcessM s Unit := do
  let st ← takeState
  finishLine (f st.zipper)

@[inherit_doc Lean.Markdown.finishLineWith, inline]
def ContainerM.finishLineWith (f : BlockZipper s → BlockZipper s) : ContainerM s Unit := do
  let st ← ContainerM.takeState
  finishLine (f st.zipper)

/--
Lifts a `ContainerM` action to `ProcessM`.
-/
@[inline] def runContainerM (act : ContainerM s Unit) : ProcessM s Nat := do
  let st ← takeState
  let init : ContState s :=
    { st with matched := 0, matched_le := Nat.zero_le _ }
  match act.run init with
  | .ok _ st'   => set st'.toLineState; return st'.matched
  | .error z _ => finishLine z

/--
Traverses the spine, advancing the cursor past the markers of containers that continue. Updates the
zipper in place (e.g. pushing markers into blockquote frames) and writes `matched`, the number of
outermost spine frames that continued, so subsequent steps can close the rest. The document root
continues implicitly and is not counted.
-/
def continueContainers : ContainerM s Unit := do
  let mut st ← ContainerM.takeState
  repeat
    if h : st.matched < st.zipper.spine.size then
      match (st.zipper.spine[st.matched]).container with
      | .blockquote _ =>
        let some (markerRange, cAfter) := parseBlockquoteMarker? st.cursor.skipIndent | break
        st := { st with
          zipper := st.zipper.pushBlockquoteMarker st.matched markerRange
          cursor := cAfter
          matched := st.matched + 1
          matched_le := by rw [BlockZipper.spine_size_pushBlockquoteMarker]; exact h
        }
      | .listItem _ _ contentColumn =>
        -- A line that is indented to the item's content column continues the item. A blank line
        -- that is indented less also continues the item, and all of the blank line's whitespace is
        -- consumed.
        let (cAfter, consumed) := consumeIndentCapped st.cursor contentColumn
        if consumed ≥ contentColumn then
          st := { st with cursor := cAfter, matched := st.matched + 1, matched_le := h }
        else if st.cursor.isBlank then
          let (afterWhitespace, _) := countIndentCols st.cursor
          st := { st with cursor := afterWhitespace, matched := st.matched + 1, matched_le := h }
        else
          break
    else
      break
  set st

/--
Closes the open paragraph as a heading when the line is a setext underline (CommonMark §4.3).

Link reference definitions at the front of the paragraph become blocks before the heading, and the
remaining lines are the heading's text. When the paragraph contains only definitions, conversion to
a heading fails and the underline begins a new paragraph.
-/
@[inline] def trySetextHeading : ContainerM s Unit := do
  unless (← get).zipper.spine.size == (← get).matched do return
  let some (.paragraph lines) := (← get).zipper.openLeaf? | return
  let cursor := (← get).cursor
  let some (level, underline) := parseSetextUnderline? cursor.skipIndent | return
  let line := cursor.toEol
  let (defs, residual?) := extractRefDefs (InlineSource.ofLines lines)
  ContainerM.finishLineWith fun z =>
    let z := defs.foldl BlockZipper.addBlock { z with openLeaf? := none }
    match residual? with
    | none => z.openLeaf (.paragraph (.singleton line))
    | some residual => z.addBlock (.setextHeading level residual underline)

/--
Lazy paragraph continuation: if some containers failed to continue but we have an open paragraph and
the line is not an interrupt (i.e. doesn't open some other kind of block), the line lazily continues
the paragraph in its deepest open context.
-/
@[inline] def tryLazyContinuation : ContainerM s Unit := do
  unless (← get).zipper.spine.size > (← get).matched do return
  let some (.paragraph _) := (← get).zipper.openLeaf? | return
  let cursor := (← get).cursor
  if isInterrupt cursor.skipIndent then return
  ContainerM.finishLineWith (·.extendParagraph cursor.toEol)

/--
Closes the open containers that the current line is not part of.

A line is part of an open blockquote when it begins with the blockquote's `>` marker, and part of
an open list item when it is indented to the item's content column. `matched` is the number of open
containers, counted from the outermost inward, that the line is part of. The remaining containers
are closed here, innermost first, and the rest of the line is parsed inside the innermost container
that stays open (CommonMark's phase 1).

A line that lazily continues a paragraph, or that completes a setext heading, is finished before
this step runs.
-/
@[inline] def closeNonContinuingContainers (matched : Nat) : ProcessM s Unit :=
  modify fun st => { st with zipper := closeAbove st.zipper }
where
  /-- Closes containers until at most `matched` spine frames remain. -/
  closeAbove (z : BlockZipper s) : BlockZipper s := Id.run do
    let mut z := z
    while z.spine.size > matched do
      z := z.closeContainer
    return z

/--
Fenced code consumes lines until a matching closing fence appears. Each content line loses up to
the opening fence's indentation (CommonMark §4.5). Either way, this step finalizes the line.
-/
@[inline] def consumeFencedCode : ProcessM s Unit := do
  let some (.fencedCode info _ _) := (← get).zipper.openLeaf? | return
  let cursor := (← get).cursor
  match parseFenceClose? cursor.skipIndent info with
  | some closeFence => finishLineWith (·.closeFencedCode closeFence |>.recordContentLine)
  | none =>
    -- A blank line inside fenced code is content, so it is recorded as such.
    let (afterIndent, _) := consumeIndentCapped cursor info.openIndent
    finishLineWith fun z => (z.extendFencedCode afterIndent.verbatimLine).recordContentLine

/--
An HTML block consumes lines verbatim until its end condition is met (CommonMark §4.6). A line that
contains the kind's end marker is the block's last line. For the kinds that end before a blank
line, the blank line closes the block and falls through to the remaining steps.
-/
@[inline] def consumeHtmlBlock : ProcessM s Unit := do
  let some (.html kind _) := (← get).zipper.openLeaf? | return
  let cursor := (← get).cursor
  if kind.endsAtBlankLine then
    if cursor.isBlank then
      modify fun st => { st with zipper := st.zipper.closeLeaf }
    else
      finishLineWith fun z => (z.extendHtml cursor.verbatimLine).recordContentLine
  else
    let line := cursor.verbatimLine
    if kind.endConditionMet line.source then
      finishLineWith fun z => (z.extendHtml line).closeLeaf.recordContentLine
    else if cursor.isBlank then
      finishLineWith fun z => (z.extendHtml line).recordBlankLine
    else
      finishLineWith fun z => (z.extendHtml line).recordContentLine

/--
Indented code consumes 4+-indented lines verbatim and records blank lines provisionally. Any other
line closes the block and falls through to the remaining steps.
-/
@[inline] def consumeIndentedCode : ProcessM s Unit := do
  let some (.indentedCode _ _) := (← get).zipper.openLeaf? | return
  let cursor := (← get).cursor
  let line := cursor.skipIndent
  if line.after.isEmpty then
    finishLineWith fun z => (z.indentedCodeAddBlank (indentedCodeLine cursor)).recordBlankLine
  if line.indent ≥ 4 then
    finishLineWith fun z => (z.indentedCodeAddLine (indentedCodeLine cursor)).recordContentLine
  modify fun st => { st with zipper := st.zipper.closeLeaf }

/--
Opens as many container prefixes (blockquote, list-item) as the line provides, in order. Returns
whether a list item was opened on this line, because the blank line handler downstream needs that
information to distinguish an empty list item's body from a blank-line separator, together with the
rest of the line after the prefixes.

Thematic break has higher precedence than list markers (CommonMark §5.2: `* * *` is a thematic
break, not a one-item list), so each iteration short-circuits when a thematic break starts at the
current cursor.
-/
def openContainerPrefixes (line : IndentedLine s) : ProcessM s (Bool × IndentedLine s) := do
  let mut line := line
  let mut openedListItemThisLine := false
  -- Where the last thematic break scan failed. A scan that starts before that position fails at
  -- it too, so the line is not scanned again from every marker of a long `- - - …` prefix.
  let mut breakScanFailedAt? : Option s.Pos := none
  repeat
    unless Option.any (line.after.pos < ·) breakScanFailedAt? do
      match checkThematicBreak line with
      | .isBreak => break
      | .failsAt pos => breakScanFailedAt? := some pos
      | .notCandidate => pure ()
    if let some (markerRange, cAfter) := parseBlockquoteMarker? line then
      modify fun st =>
        { st with zipper := st.zipper.openBlockquote #[markerRange], cursor := cAfter }
      line := cAfter.skipIndent
    else if let some m := parseListMarker? line then
      -- An open paragraph here is the innermost block, since every container that did not continue
      -- has been closed, so the marker is on the line after the paragraph's text.
      let interruptingPara := match (← get).zipper.openLeaf? with
        | some (.paragraph _) => true
        | _ => false
      if interruptingPara && !listMarkerInterruptsParagraph m.after m.kind then
        break
      else
        modify fun st =>
          { st with
            zipper := st.zipper.openItem m.kind m.marker m.contentColumn, cursor := m.after }
        openedListItemThisLine := true
        line := m.after.skipIndent
    else
      break
  return (openedListItemThisLine, line)

/--
Adds a thematic break for the line and finishes it.
-/
@[inline] def finishThematicBreak : ProcessM s Unit := do
  let line := trimTrailingWs (← get).cursor.skipIndent.after.toEol
  finishLineWith (·.addBlock (.thematicBreak line))

/--
Finishes a blank line (CommonMark §4.9). A blank line is one that is blank _after_ the prefix of
block opener markers such as `>` or `*`.

Blank lines end the currently-open paragraph. They also end list items that have no content yet,
unless the item's marker is on the very blank line that's being finished. Blockquotes and lists
stay open, since whether they continue is decided by the next line that has content.
-/
@[inline] def finishBlankLine (openedListItemThisLine : Bool) : ProcessM s Unit := do
  finishLineWith fun z => Id.run do
    let mut z := z.closeLeaf
    if !openedListItemThisLine then
      let emptyItem :=
        if let some { container := .listItem .., children } := z.spine.back? then
          children.isEmpty
        else false
      if emptyItem then z := z.closeContainer
    -- An item may begin with one blank line (CommonMark §5.2). When the marker is alone on its
    -- line, this is that blank line. It precedes the item's first block instead of separating two
    -- blocks, so it is recorded like a content line and leaves the list tight.
    return if openedListItemThisLine then z.recordContentLine else z.recordBlankLine

/-- When `line` is an ATX heading (CommonMark §4.2), adds the heading and finishes the line. -/
@[inline] def tryAtxHeading (line : IndentedLine s) : ProcessM s Unit := do
  let some m := parseAtxHeading? line | return
  let content := InlineSource.ofLines (.singleton m.content)
  finishLineWith (·.addBlock (.atxHeading m.level m.hashes content m.closeHashes))

/--
When `line` is an opening code fence (CommonMark §4.5), opens the block and finishes the line.
-/
@[inline] def tryFencedCodeOpener (line : IndentedLine s) : ProcessM s Unit := do
  let some (info, openFence) := parseFenceOpen? line | return
  finishLineWith (·.openLeaf (.fencedCode info openFence #[]))

/--
Opens an HTML block (CommonMark §4.6). A block whose first line also meets its end condition is
complete at once. A complete HTML block cannot interrupt a paragraph.
-/
@[inline] def tryHtmlBlockOpener (line : IndentedLine s) : ProcessM s Unit := do
  let cursor := (← get).cursor
  let some kind := parseHtmlBlockStart? line | return
  if let some (.paragraph _) := (← get).zipper.openLeaf? then
    unless kind.interruptsParagraph do return
  let line := cursor.verbatimLine
  if kind.endConditionMet line.source then
    finishLineWith (·.addBlock (.html #[line]))
  else
    finishLineWith (·.openLeaf (.html kind #[line]))

/--
When `line` is indented four or more columns, opens an indented code block and finishes the line.
When a paragraph is open, the line is left for the paragraph instead, since indented code cannot
interrupt a paragraph (CommonMark §4.4).
-/
@[inline] def tryIndentedCodeOpener (line : IndentedLine s) : ProcessM s Unit := do
  unless line.indent ≥ 4 && (← get).zipper.openLeaf?.isNone do return
  let cursor := (← get).cursor
  finishLineWith (·.openLeaf (.indentedCode #[indentedCodeLine cursor] #[]))

/--
Starts a new paragraph, or extends the one that's open.

This is the default parser if no others apply.
-/
@[inline] def emitParagraph : ProcessM s Unit := do
  let line := (← get).cursor.toEol
  match (← get).zipper.openLeaf? with
  | some (.paragraph _) => finishLineWith (·.extendParagraph line)
  | _ => finishLineWith (·.openLeaf (.paragraph (.singleton line)))

/--
Finishes the line by opening the leaf block that `line` begins or, if it doesn't begin a block, by
adding the line to a paragraph.

The block to open is decided by the line's indentation and first character: a blank line; four or
more columns of indentation for indented code; and otherwise `#` for an ATX heading, a backtick or
tilde for a code fence, `<` for an HTML block, and `*`, `-`, or `_` for a thematic break. Other
lines are paragraph text.
-/
@[inline]
def openLeafBlock (openedListItemThisLine : Bool) (line : IndentedLine s) : ProcessM s Unit := do
  match line.after.front? with
  | none => finishBlankLine openedListItemThisLine
  | some c =>
    if line.indent ≥ 4 then
      tryIndentedCodeOpener line
    else if c == '#' then
      tryAtxHeading line
    else if c == '`' || c == '~' then
      tryFencedCodeOpener line
    else if c == '<' then
      tryHtmlBlockOpener line
    else if (c == '*' || c == '-' || c == '_') && isThematicBreak line then
      finishThematicBreak
    emitParagraph

/--
Processes a single source line, updating the zipper.
-/
def processLine (z : BlockZipper s) (line : s.Subslice) : BlockZipper s :=
  let init : LineState s := { zipper := z, cursor := Cursor.ofLine line }
  let pipeline : ProcessM s Unit := do
    let matched ← runContainerM do
      continueContainers
      trySetextHeading
      tryLazyContinuation
    closeNonContinuingContainers matched
    consumeFencedCode
    consumeHtmlBlock
    consumeIndentedCode
    let line := (← get).cursor.skipIndent
    let (openedListItemThisLine, line) ← openContainerPrefixes line
    openLeafBlock openedListItemThisLine line
  match pipeline.run init with
  | .ok _ st    => st.zipper
  | .error z _ => z

/--
Parses the block structure of `s`. Up to `indent` leading spaces of each line are skipped.
-/
def parseBlocksRaw (s : String.Slice) (indent : Nat := 0) : Array (Block.Raw s) := Id.run do
  let mut z := BlockZipper.empty
  for line in splitLines s.toSubslice do
    z := processLine z (dropIndent line indent)
  return z.finalize

/--
Traverses blocks, extracting link reference definitions off the front of each paragraph, and emits
a `linkRefDef` block in source order for each. Setext headings had their definitions extracted at
their underline.
-/
partial def postProcessRefDefs (blocks : Array (Block.Raw s)) : Array (Block.Raw s) := Id.run do
  let mut out : Array (Block.Raw s) := #[]
  let mut i := 0
  while h : i < blocks.size do
    let b := blocks[i]
    match b with
    | .paragraph content =>
      let (defs, residual?) := extractRefDefs content
      out := out ++ defs
      if let some residual := residual? then out := out.push (.paragraph residual)
    | .blockquote markers children =>
      let newChildren := postProcessRefDefs children
      out := out.push (.blockquote markers newChildren)
    | .list kind tight items =>
      let newItems := postProcessRefDefs items
      out := out.push (.list kind tight newItems)
    | .listItem marker children =>
      let newChildren := postProcessRefDefs children
      out := out.push (.listItem marker newChildren)
    | other => out := out.push other
    i := i + 1
  return out

/--
Builds the document's reference table from its link reference definitions and from `externalRefs`,
which maps labels to definitions that the caller supplies.

An earlier definition of a label in the document takes precedence over a later one. A definition in
the document takes precedence over an external one with the same label unless the external one has
`overrideDocument` set.

The labels of `externalRefs` are normalized like those in the document. When several of them
normalize to the same label, the definition of the lexicographically least of them is used.
-/
public partial def buildRefTable (blocks : Array (Block.Raw s))
    (externalRefs : Std.HashMap String ExternalRef := {}) : RefTable s :=
  let inDocument := go blocks |>.run {} |>.2
  let sorted := externalRefs.toArray.qsort (·.1 < ·.1)
  let external : Std.HashMap LinkLabel ExternalRef :=
    sorted.foldl (init := {}) fun m (label, ref) => m.insertIfNew (LinkLabel.ofString label) ref
  external.fold (init := inDocument) fun table normLabel ref =>
    if ref.overrideDocument then table.insert normLabel (.external ref)
    else table.insertIfNew normLabel (.external ref)
where
  go (bs : Array (Block.Raw s)) : StateM (RefTable s) Unit :=
    bs.forM fun
      | .linkRefDef m => modify (·.insertIfNew (normalizeLabel m.label) (.inDocument m))
      | .blockquote _ children => go children
      | .list _ _ items => go items
      | .listItem _ children => go children
      | _ => pure ()

/--
Identifies the complete block structure of `s`. Up to `indent` leading spaces of each line are
skipped.
-/
public def parseBlocks (s : String.Slice) (indent : Nat := 0) : Array (Block.Raw s) :=
  postProcessRefDefs (parseBlocksRaw s indent)
