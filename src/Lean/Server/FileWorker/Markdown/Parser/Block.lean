/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Thrane Christiansen
-/
module

prelude
public import Init.Data.Nat.Fold
public import Init.Data.String.TakeDrop
public import Lean.Server.FileWorker.Markdown.Basic
public import Lean.Server.FileWorker.Markdown.InlineSource
import Lean.Server.FileWorker.Markdown.Parser.Cursor
import Lean.Server.FileWorker.Markdown.Parser.BlockZipper

namespace Lean.Server.FileWorker.Markdown

/-!
# Pass 1: Block Parser

CommonMark is parsed in two passes:
1. The first pass identifies the block structure of the document and accumulates the definitions of
   ref-style links.
2. Within each block, the second pass finds the structure of inlines and applies fallback rules for
   poorly nested or mismatched delimiters.

This file contains the first pass. It is almost compliant with CommonMark; unlike CommonMark, it
does not support HTML blocks, and case folding of ref-style link definitions is only for ASCII
`a`-`z`.
-/

/--
Counts and skips leading ASCII spaces in `sub`. Returns the count and the new byte position.
-/
def countSpaces (sub : Substring.Raw) : Nat × String.Pos.Raw := Id.run do
  let mut sub := sub
  let mut n := 0
  while !sub.isEmpty && sub.front == ' ' do
    n := n + 1
    sub := sub.drop 1
  return (n, sub.startPos)

/--
Counts tab-aware leading whitespace (CommonMark §2.2): each tab advances to the next 4-column tab
stop, computed relative to the cursor's current column. Returns the advanced cursor and the total
number of columns consumed. Tabs are always crossed in full.
-/
def countIndentCols (c : Cursor) : Cursor × Nat := Id.run do
  let mut sub := c.rest
  let mut cols := 0
  while !sub.isEmpty do
    let ch := sub.front
    if ch == ' ' then
      cols := cols + 1
      sub := sub.drop 1
    else if ch == '\t' then
      let curCol := c.col + cols
      cols := cols + (4 - curCol % 4)
      sub := sub.drop 1
    else
      break
  return ({ rest := sub, col := c.col + cols }, cols)

/--
Builds a `String` of `n` ASCII spaces.
-/
def spaces (n : Nat) : String :=
  n.fold (init := "") fun _ _ s => s.push ' '

/--
Consumes up to `maxCols` columns of leading whitespace at `c`, with tab-aware column counting.
Returns the advanced cursor and the number of columns actually consumed.

Tabs may be split: if a tab would carry the cursor past `maxCols`, the byte position stays at the
tab and the column count advances by exactly the requested amount, leaving “leftover” tab columns
for subsequent consumers (CommonMark §2.2's partial-tab rule).
-/
def consumeIndentCapped (c : Cursor) (maxCols : Nat) : Cursor × Nat := Id.run do
  let mut sub := c.rest
  let mut cols := 0
  while !sub.isEmpty && cols < maxCols do
    let ch := sub.front
    if ch == ' ' then
      cols := cols + 1
      sub := sub.drop 1
    else if ch == '\t' then
      let curCol := c.col + cols
      let advance := 4 - curCol % 4
      if cols + advance > maxCols then
        -- Partial tab: byteIdx stays at the tab; cols advances by the
        -- requested amount only. The remaining tab cols are observable to
        -- the next consumer through the cursor's (byteIdx, col) pair.
        cols := maxCols
      else
        cols := cols + advance
        sub := sub.drop 1
    else
      break
  return ({ rest := sub, col := c.col + cols }, cols)

/--
Converts a line of an indented code block into the string that it denotes.

Renders a line of indented-code content: strips up to 4 columns of leading indentation (relative to
the cursor's current column) and materializes any partial-tab leftover as ASCII spaces (CommonMark
§2.2). The byte cursor may land mid-tab when the indentation doesn't fall on a tab-stop boundary; in
that case, the leftover columns of that tab become spaces in the rendered output.
-/
def indentedCodeLineToString (c : Cursor) : String := Id.run do
  let (c', _) := consumeIndentCapped c 4
  let p := c'.byteIdx
  let s := c.str
  let mut leftoverPrefix := ""
  let mut contentStart := p
  if !c'.rest.isEmpty && c'.rest.front == '\t' then
    if c'.col % 4 != 0 then
      leftoverPrefix := spaces (4 - c'.col % 4)
      contentStart := (c'.rest.drop 1).startPos
  return leftoverPrefix ++ String.Pos.Raw.extract s contentStart c.stopPos

/-- Whether `sub` is blank (only spaces or tabs). -/
def isBlankSlice (sub : Substring.Raw) : Bool :=
  sub.all fun c => c == ' ' || c == '\t'

/-- Drops trailing spaces and tabs from `sub` and returns the new end position. -/
def trimTrailingWs (sub : Substring.Raw) : String.Pos.Raw :=
  (sub.dropRightWhile fun c => c == ' ' || c == '\t').stopPos

/-- Splits `sub` into line ranges, each excluding the trailing `'\n'`. -/
def splitLines (sub : Substring.Raw) : Array Syntax.Range := Id.run do
  let mut lines : Array Syntax.Range := #[]
  let mut sub := sub
  let mut lineStart := sub.startPos
  while !sub.isEmpty do
    if sub.front == '\n' then
      lines := lines.push { start := lineStart, stop := sub.startPos }
      sub := sub.drop 1
      lineStart := sub.startPos
    else
      sub := sub.drop 1
  if lineStart < sub.startPos then
    lines := lines.push { start := lineStart, stop := sub.startPos }
  return lines

/--
A successful ATX heading match.
-/
structure AtxHeadingMatch where
  /-- The heading level (1-6). -/
  level : Nat
  /-- The source range of the opening `#`s. -/
  hashes : Syntax.Range
  /-- The trimmed inline content range. -/
  content : Syntax.Range
  /-- The optional closing hashes. -/
  closeHashes : Option Syntax.Range

/--
Tries to recognize an ATX heading at `c`. Trailing whitespace is trimmed from `content`.
-/
def matchAtxHeading (c : Cursor) : Option AtxHeadingMatch :=  do
  let (c, indent) := countIndentCols c
  guard (indent ≤ 3)
  let s := c.str
  let hashStart := c.byteIdx
  -- CommonMark §4.2 caps ATX heading levels at 6. We scan up to 7 hashes so
  -- runs of length ≥ 7 fall through the `count ≤ 6` guard below as non-headings.
  let mut rest := c.rest
  let mut count := 0
  while !rest.isEmpty && count < 7 do
    if rest.front != '#' then break
    count := count + 1
    rest := rest.drop 1
  guard (count > 0 && count ≤ 6)
  if !rest.isEmpty then
    let next := rest.front
    guard (next == ' ' || next == '\t')
  let q := rest.startPos
  let hashes : Syntax.Range := { start := hashStart, stop := q }
  -- Skip whitespace (spaces or tabs) between the hashes and the content.
  let (cAfterGap, _) := countIndentCols (c.moveTo q 0)
  let contentStart := cAfterGap.byteIdx
  let mut contentEnd := trimTrailingWs { c.rest with startPos := contentStart }
  -- Optional closing `#` sequence: a trailing run of `#` characters that
  -- is either preceded by a space/tab or extends to the start of content
  -- (CommonMark §4.2). Strip it from the content range.
  let mut closeStart := contentEnd
  while contentStart < closeStart
      && (String.Pos.Raw.prev s closeStart).get s == '#' do
    closeStart := String.Pos.Raw.prev s closeStart
  let closeLen := contentEnd.byteIdx - closeStart.byteIdx
  let mut closeHashes? : Option Syntax.Range := none
  if closeLen > 0 then
    if closeStart == contentStart then
      closeHashes? := some { start := closeStart, stop := contentEnd }
      contentEnd := closeStart
    else
      let beforeClose := String.Pos.Raw.prev s closeStart
      let cb := beforeClose.get s
      if cb == ' ' || cb == '\t' then
        closeHashes? := some { start := closeStart, stop := contentEnd }
        contentEnd := trimTrailingWs
          { str := s, startPos := contentStart, stopPos := closeStart }
  return {
    level := count
    hashes
    content := { start := contentStart, stop := contentEnd }
    closeHashes := closeHashes?
  }

/--
Whether the line at `c` is a thematic break: up to 3 leading spaces, followed by 3+ matching
`*`/`-`/`_` characters, with only spaces or tabs allowed between or after them (CommonMark §4.1).
-/
def matchThematicBreak (c : Cursor) : Bool := Id.run do
  let (c, indent) := countIndentCols c
  if indent > 3 then return false
  let some (markerChar, _) := c.peek? | return false
  if markerChar != '*' && markerChar != '-' && markerChar != '_' then
    return false
  let mut rest := c.rest
  let mut markerCount := 0
  while !rest.isEmpty do
    let ch := rest.front
    if ch == markerChar then
      markerCount := markerCount + 1
      rest := rest.drop 1
    else if ch == ' ' || ch == '\t' then
      rest := rest.drop 1
    else
      return false
  return markerCount >= 3

/--
Recognizes a setext heading underline (CommonMark §4.3): up to three leading spaces, then a run of
`=` (level 1) or `-` (level 2), then optional trailing whitespace. Returns the heading level on
success.

Note: a `---` underline overlaps with the thematic-break syntax. The caller must enforce the
precedence rule: setext header parsing applies only when an open paragraph immediately precedes the
underline; otherwise, the same line is interpreted as a thematic break.
-/
def matchSetextUnderline (c : Cursor) : Option Nat := do
  let (c, indent) := countIndentCols c
  guard (indent ≤ 3)
  let (markerChar, _) ← c.peek?
  guard (markerChar == '=' || markerChar == '-')
  let (cAfterRun, _) := c.advanceWhile (· == markerChar)
  -- After the run, only whitespace is permitted to end of line.
  let (cAfterWs, _) := cAfterRun.advanceWhile fun ch =>
    ch == ' ' || ch == '\t'
  guard (cAfterWs.byteIdx ≥ cAfterWs.stopPos)
  return if markerChar == '=' then 1 else 2

/-- Tries to recognize an opening code fence at `c`. -/
def matchFenceOpen (c : Cursor) : Option (FenceInfo × Syntax.Range) := do
  let (c, indent) := countIndentCols c
  guard (indent ≤ 3)
  let s := c.str
  let (fenceChar, _) ← c.peek?
  let fenceChar ← FenceChar.ofChar? fenceChar
  let fenceStart := c.byteIdx
  let (cAfterFence, count) := c.advanceWhile (· == fenceChar.toChar)
  guard (count ≥ 3)
  let q := cAfterFence.byteIdx
  let openFence : Syntax.Range := { start := fenceStart, stop := q }
  let (_, infoStart) := countSpaces { c.rest with startPos := q }
  let infoEnd := trimTrailingWs { c.rest with startPos := infoStart }
  -- A backtick fence's info string may not contain backticks.
  if fenceChar == .backtick then
    let mut eRest : Substring.Raw := { str := s, startPos := infoStart, stopPos := infoEnd }
    while !eRest.isEmpty do
      let ch := eRest.front
      guard (ch != '`')
      eRest := eRest.drop 1
  let infoString? : Option Syntax.Range :=
    if infoStart < infoEnd then some { start := infoStart, stop := infoEnd } else none
  return ({ fenceChar, fenceLen := count, openIndent := indent, infoString? },
    openFence)

/--
Tries to recognize a closing fence on a line whose container prefixes have already been consumed.
The closing fence must match `info`'s character, be at least as long as the opener, and contain only
trailing whitespace afterwards.
-/
def matchFenceClose (line : Substring.Raw) (info : FenceInfo) : Option Syntax.Range := do
  let stop := line.stopPos
  let (indent, p) := countSpaces line
  guard (indent ≤ 3)
  let pRest : Substring.Raw := { line with startPos := p }
  guard <| !pRest.isEmpty && pRest.front == info.fenceChar.toChar
  let cAtFence : Cursor := { rest := pRest, col := indent }
  let (cAfterFence, count) := cAtFence.advanceWhile (· == info.fenceChar.toChar)
  guard <| count ≥ info.fenceLen
  let q := cAfterFence.byteIdx
  let (_, after) := countSpaces { line with startPos := q }
  guard <| after ≥ stop
  return { start := p, stop := q }

/--
Tries to recognize a single blockquote marker (`>` plus optional space). Returns the marker's source
range and a cursor positioned just past the consumed prefix (with column adjusted, possibly mid-tab
per CommonMark §2.2's partial-tab rule).
-/
def matchBlockquoteMarker (c : Cursor) : Option (Syntax.Range × Cursor) := do
  let (c, indent) := countIndentCols c
  guard (indent ≤ 3)
  let p := c.byteIdx
  guard (!c.rest.isEmpty && c.rest.front == '>')
  let afterMarker := c.rest.drop 1
  let mEnd := afterMarker.startPos
  -- The blockquote marker `>` is followed by an optional single space (or
  -- one column of a tab — partial-tab consumption per CommonMark §2.2).
  -- `countIndentCols` already advanced `c.col` past the leading indent.
  let baseCol := c.col + 1  -- col just after the `>`
  if !afterMarker.isEmpty then
    let nextC := afterMarker.front
    let mEndNext := (afterMarker.drop 1).startPos
    if nextC == ' ' then
      return ({ start := p, stop := mEnd }, c.moveTo mEndNext (baseCol + 1))
    if nextC == '\t' then
      let tabStop := baseCol + (4 - baseCol % 4)
      if tabStop == baseCol + 1 then
        -- Tab equivalent to one column; cross it fully.
        return ({ start := p, stop := mEnd }, c.moveTo mEndNext (baseCol + 1))
      else
        -- Partial tab: leave the byte in place but advance the column.
        return ({ start := p, stop := mEnd }, c.moveTo mEnd (baseCol + 1))
  return ({ start := p, stop := mEnd }, c.moveTo mEnd baseCol)

/--
A successful list marker match.
-/
structure ListMarkerMatch where
  /-- The source range of the marker itself. -/
  marker : Syntax.Range
  /-- A cursor positioned just past the absorbed prefix. -/
  after : Cursor
  /-- The marker's kind.-/
  kind : ListKind
  /--
  The column distance from the input cursor to `after`, which is the minimum indentation of
  subsequent continuation lines.
  -/
  contentColumn : Nat

/-- Tries to recognize a bullet or ordered list marker at `c`. -/
def matchListMarker (c : Cursor) : Option ListMarkerMatch := do
  let initialCol := c.col
  let (c, indent) := countIndentCols c
  guard (indent ≤ 3)
  let stop := c.stopPos
  let p := c.byteIdx
  guard !c.rest.isEmpty
  let ch := c.rest.front
  let pNext := (c.rest.drop 1).startPos
  let preMarkerCol := c.col
  -- After matching the marker, compute the listItem's content column. Per
  -- CommonMark §5.2: 1 ≤ N ≤ 4 cols of whitespace following the marker are
  -- absorbed into the listItem prefix; if the line is empty after the marker
  -- or has 5+ cols of whitespace (i.e., the content is itself indented
  -- code), the listItem absorbs only one col of whitespace. Tabs may be
  -- partially consumed (CommonMark §2.2).
  let determineContent (markerEnd : String.Pos.Raw) (markerEndCol : Nat) : Option Cursor :=  do
    let baseCursor := c.moveTo markerEnd markerEndCol
    if markerEnd >= stop then
      return c.moveTo markerEnd (markerEndCol + 1)
    guard !baseCursor.rest.isEmpty
    let nextC := baseCursor.rest.front
    guard <| nextC == ' ' || nextC == '\t'
    let (afterWsCursor, wsCols) := countIndentCols baseCursor
    let contentBlank := afterWsCursor.byteIdx >= stop
    let absorbCols : Nat :=
      if contentBlank || wsCols >= 5 then 1
      else wsCols
    let (cursorAfter, _) := consumeIndentCapped baseCursor absorbCols
    return cursorAfter
  -- Bullet markers
  if ch == '*' || ch == '-' || ch == '+' then
    let markerEnd := pNext
    let markerEndCol := preMarkerCol + 1
    let kind : BulletKind :=
      if ch == '*' then .star
      else if ch == '-' then .hyphen
      else .plus
    let cursorAfter ← determineContent markerEnd markerEndCol
    return {
      marker := { start := p, stop := markerEnd }
      after := cursorAfter
      kind := .bullet kind
      contentColumn := cursorAfter.col - initialCol
    }
  -- Ordered markers
  if ch.isDigit then
    let mut rest := c.rest
    let mut digits := 0
    let mut value : Nat := 0
    -- CommonMark §5.2: an ordered-list marker has 1–9 digits. We scan up to
    -- 10 so runs of length ≥ 10 fall through the `digits ≤ 9` guard below.
    while !rest.isEmpty && digits < 10 do
      let digit := rest.front
      if !digit.isDigit then break
      value := value * 10 + (digit.toNat - '0'.toNat)
      digits := digits + 1
      rest := rest.drop 1
    guard (digits != 0)
    guard (digits ≤ 9)
    guard !rest.isEmpty
    let delim := rest.front
    guard (delim == '.' || delim == ')')
    let markerEnd := (rest.drop 1).startPos
    let markerEndCol := preMarkerCol + digits + 1
    let orderedDelim : OrderedDelim := if delim == '.' then .dot else .rparen
    let cursorAfter ← determineContent markerEnd markerEndCol
    return {
      marker := { start := p, stop := markerEnd }
      after := cursorAfter
      kind := .ordered value orderedDelim
      contentColumn := cursorAfter.col - initialCol
    }
  failure

/--
Whether a list marker matched at the current cursor is allowed to interrupt an open paragraph
(CommonMark §5.2):
 * An empty list item cannot interrupt a paragraph
 * An ordered list marker can interrupt only if its start number is `1`.

`after` is positioned just past the marker.
-/
def listMarkerInterruptsParagraph (after : Cursor) (kind : ListKind) : Bool :=
  !isBlankSlice after.rest
  && match kind with
     | .ordered start _ => start == 1
     | .bullet _ => true

/--
Whether `kind` is the same kind of list as one already open in a parent. A marker of the same kind
is always allowed to start a new sibling item, even when it would otherwise violate
`listMarkerInterruptsParagraph` (CommonMark §5.2's strict rules apply only when *opening* a list,
not when extending one).
-/
def hasSameKindListAncestor (z : BlockZipper) (kind : ListKind) : Bool :=
  z.spine.any fun frame =>
    match frame.container with
    | .list k => k.sameKind kind
    | _ => false

/--
Whether the deepest open list has a *different* kind than `kind`. A marker of a different kind
closes that list (and the listItem and any leaf inside it), so it effectively “interrupts” any
paragraph that was open. The strict §5.2 start-≠-1 rule does not block this, since after the list
closes the new list opens at the parent level, where there is no longer a paragraph to interrupt.
-/
def closesEnclosingList (z : BlockZipper) (kind : ListKind) : Bool :=
  z.spine.findSomeRev? differingListKind |>.getD false
where
  differingListKind (frame : ZipperFrame) : Option Bool :=
    match frame.container with
    | .list k => some (!k.sameKind kind)
    | _ => none

/--
Whether the line at `cursor` would *interrupt* a paragraph. In other words, it would open some other
kind of block such that lazy continuation rules cannot apply.

Indented code blocks are intentionally not interrupts (CommonMark §4.4: an indented code block
cannot interrupt a paragraph). List markers must additionally satisfy
`listMarkerInterruptsParagraph` unless they are a sibling of an already-open list with the same
marker kind.
-/
def isInterrupt (z : BlockZipper) (c : Cursor) : Bool :=
  isBlankSlice c.rest ||
  (matchBlockquoteMarker c).isSome ||
  (match matchListMarker c with
    | some m =>
      hasSameKindListAncestor z m.kind ||
      closesEnclosingList z m.kind ||
      listMarkerInterruptsParagraph m.after m.kind
    | none => false) ||
  (matchAtxHeading c).isSome ||
  (matchFenceOpen c).isSome ||
  matchThematicBreak c

/-!
# Processing Lines

Lines are processed one at a time. A kind of rightward-only zipper is maintained, allowing blocks to
be added at the lower right of the syntax tree.

Each step of the pipeline is a `ProcessM Unit` named after its description in the CommonMark spec.
Steps that produce the line's final zipper short-circuit the pipeline by `throw`-ing it, while steps
that only mutate the in-flight state fall through to the next.
-/

/--
The state that flows through the late (post-close) steps of `processLine`.
-/
private structure LineState where
  /-- The in-progress document. -/
  z : BlockZipper
  /-- The cursor that advances through the block-inducing prefixes of the line. -/
  c : Cursor
  /-- Whether the preceding line was blank.-/
  prevBlank : Bool

/--
The state during the early container-continuation phase that tracks the length of the suffix of the
zipper's spine (that is, parent blocks) that are continued on this line.
-/
private structure ContState extends LineState where
  /-- The number of inner spine frames that continued on this line. -/
  matched : Nat
  /-- The matched counter is always a valid prefix length of the spine. -/
  matched_le : matched ≤ z.spine.size

/--
The monad for line processing after containers that need closing have been closed.

The “exception” channel carries the line's final `BlockZipper`, and is used for early return.
-/
private abbrev ProcessM := EStateM BlockZipper LineState

/--
The monad for determining which containers should continue for a given line.
-/
private abbrev ContainerM := EStateM BlockZipper ContState

/--
Lifts a `ContainerM` action to `ProcessM`.
-/
private def runContainerM (act : ContainerM Unit) : ProcessM Nat := do
  let s ← get
  let init : ContState :=
    { s with matched := 0, matched_le := Nat.zero_le _ }
  match act.run init with
  | .ok _ s'   => set s'.toLineState; return s'.matched
  | .error z _ => throw z

/--
Walks the spine, advancing the cursor past the markers of containers that continue. Updates the
zipper in place (e.g. pushing markers into blockquote frames) and writes `matched` — the number of
inner spine frames that continued, so subsequent steps can close the rest. The document root
continues implicitly and is not counted.
-/
private def continueContainers : ContainerM Unit := do
  let mut s ← get
  let mut keepWalking := true
  while h : keepWalking ∧ s.matched < s.z.spine.size do
    let frame := s.z.spine[s.matched]'h.2
    match frame.container with
    | .blockquote markers =>
      match matchBlockquoteMarker s.c with
      | none => keepWalking := false
      | some (markerRange, cAfter) =>
        let frame' := { frame with container := .blockquote (markers.push markerRange) }
        s := { s with
          c := cAfter
          z := { s.z with spine := s.z.spine.set s.matched frame' h.2 }
          matched := s.matched + 1
          matched_le := by cases h; simpa
        }
    | .list _ =>
      -- Lists themselves carry no continuation marker; their listItem children do.
      s := { s with matched := s.matched + 1, matched_le := h.2 }
    | .listItem _ contentColumn =>
      -- Try to consume `contentColumn` cols of indent (in cols, tab-aware
      -- with partial-tab support).
      let (cAfter, consumed) := consumeIndentCapped s.c contentColumn
      if consumed ≥ contentColumn then
        s := { s with c := cAfter, matched := s.matched + 1, matched_le := h.2 }
      else if isBlankSlice s.c.rest then
        -- A blank line continues the listItem (cursor not advanced).
        s := { s with matched := s.matched + 1, matched_le := h.2 }
      else
        keepWalking := false
  set s

/--
Tightness (CommonMark §5.3): if the previous line was blank and the deepest open `listItem` in the
matched range is being extended on this line, mark the *innermost* enclosing list as loose. Outer
list items see the blank as part of their nested child's body, not as a separator between their own
direct children.
-/
private def markEnclosingListLoose : ContainerM Unit := do
  let s ← get
  unless s.prevBlank do return
  -- Indices within the matched range live in `Fin s.matched`, and combined
  -- with `s.matched_le` are valid spine indices. The walk goes from
  -- `s.matched - 1` down to `0`, breaking on the first listItem found.
  if h0 : 0 < s.matched then
    let mut i : Fin s.matched := ⟨s.matched - 1, Nat.sub_one_lt_of_lt h0⟩
    let mut keepGoing := true
    while keepGoing do
      have h_i : i.val < s.z.spine.size := Nat.lt_of_lt_of_le i.isLt s.matched_le
      if let .listItem _ _ := (s.z.spine[i]).container then
        if h_pos : 0 < i.val then
          have h_im1 : ↑i - 1 < s.z.spine.size := Nat.sub_lt_of_lt h_i
          if let .list _ := (s.z.spine[↑i - 1]).container then
            modify fun s' =>
              { s' with
                z :=
                  { s'.z with
                    spine := s'.z.spine.modify (i.val - 1) ({ · with loose := true }) }
                matched_le := by cases s'; simpa
              }
        keepGoing := false
      else if h_pos : 0 < i.val then
        i := ⟨i.val - 1,  Nat.sub_lt_of_lt i.isLt⟩
      else
        keepGoing := false

/--
Checks whether to upgrade the preceding block to a Setext header.
-/
private def trySetextHeading : ContainerM Unit := do
  let s ← get
  unless s.z.spine.size == s.matched do return
  let some (.paragraph lines) := s.z.openLeaf? | return
  let some level := matchSetextUnderline s.c | return
  let underline : Syntax.Range := s.c.toEol
  let z := { s.z with openLeaf? := none }
  throw (z.addBlock (.setextHeading level lines underline))

/--
Lazy paragraph continuation: if some containers failed to continue but we have an open paragraph and
the line is not an interrupt (i.e. doesn't open some other kind of block), the line lazily continues
the paragraph in its deepest open context.
-/
private def tryLazyContinuation : ContainerM Unit := do
  let s ← get
  unless s.z.spine.size > s.matched do return
  let some (.paragraph _) := s.z.openLeaf? | return
  if isInterrupt s.z s.c then return
  throw (s.z.extendParagraph s.c.toEol)

/--
Closes any spine containers that did not continue on this line. Takes the `matched` count produced
by the container continuation phase as an argument and closes the suffix of the parents that are
indicated.
-/
private def closeNonContinuingContainers (matched : Nat) : ProcessM Unit := do
  let s ← get
  let mut z := s.z
  while z.spine.size > matched do
    z := z.closeContainer
  set { s with z }

/--
Fenced code consumes lines verbatim until a matching closing fence appears. Either way, this step
finalizes the line.
-/
private def consumeFencedCode : ProcessM Unit := do
  let s ← get
  let some (.fencedCode info _ _) := s.z.openLeaf? | return
  match matchFenceClose s.c.rest info with
  | some closeFence => throw (s.z.closeFencedCode closeFence)
  | none => throw (s.z.extendFencedCode s.c.toEol)

/--
Indented code consumes 4+-indented lines verbatim and holds blank lines provisionally. Any other
line closes the block and falls through to the remaining steps.
-/
private def consumeIndentedCode : ProcessM Unit := do
  let s ← get
  let some (.indentedCode _ _) := s.z.openLeaf? | return
  if isBlankSlice s.c.rest then
    let (cAfter, _) := consumeIndentCapped s.c 4
    let range : Syntax.Range := { start := cAfter.byteIdx, stop := s.c.stopPos }
    throw (s.z.indentedCodeAddBlank range (indentedCodeLineToString s.c))
  let (_, indent) := countIndentCols s.c
  if indent ≥ 4 then
    let (cAfter, _) := consumeIndentCapped s.c 4
    let range : Syntax.Range := { start := cAfter.byteIdx, stop := s.c.stopPos }
    throw (s.z.indentedCodeAddLine range (indentedCodeLineToString s.c))
  modify fun s => { s with z := s.z.closeLeaf }

/--
If the deepest container is a list whose previous item just closed and this line is non-blank
without a sibling marker, close the list so subsequent content doesn't become a stray child.
-/
private def closeFinishedSiblingList : ProcessM Unit := do
  let s ← get
  let some (.list _) := s.z.top? | return
  if !isBlankSlice s.c.rest && (matchListMarker s.c).isNone then
    modify fun s => { s with z := s.z.closeContainer }

/--
Opens as many container prefixes (blockquote, list-item) as the line provides, in order. Returns
whether a list item was opened on this line, because the blank line handler downstream needs that
information to distinguish an empty list item's body from a blank-line separator.

Thematic break has higher precedence than list markers (CommonMark §5.2: `* * *` is a thematic
break, not a one-item list), so each iteration short-circuits when a thematic break starts at the
current cursor.
-/
private def openContainerPrefixes : ProcessM Bool := do
  let mut openedListItemThisLine := false
  let mut keepOpening := true
  while keepOpening do
    keepOpening := false
    let s ← get
    if matchThematicBreak s.c then break
    if let some (markerRange, cAfter) := matchBlockquoteMarker s.c then
      modify fun s =>
        { s with z := s.z.openContainer (.blockquote #[markerRange]), c := cAfter }
      keepOpening := true
    else if let some m := matchListMarker s.c then
      -- The strict §5.2 rules (non-empty content, start-1 for ordered) apply
      -- only when *opening* a new list. A same-kind marker that extends an
      -- already-open list as a new sibling item is always allowed.
      let interruptingPara := match s.z.openLeaf? with
        | some (.paragraph _) => true
        | _ => false
      if interruptingPara && !hasSameKindListAncestor s.z m.kind
          && !listMarkerInterruptsParagraph m.after m.kind then
        keepOpening := false
      else
        let z' :=
          match s.z.top? with
          | some (.list k) =>
            if k.sameKind m.kind then
              -- Blank-line-then-new-sibling-item makes the list loose.
              let z :=
                if s.prevBlank then
                  let lastIdx := s.z.spine.size - 1
                  { s.z with
                    spine := s.z.spine.modify lastIdx fun f => { f with loose := true } }
                else s.z
              z.openContainer (.listItem m.marker m.contentColumn)
            else
              s.z.closeContainer
                |>.openContainer (.list m.kind)
                |>.openContainer (.listItem m.marker m.contentColumn)
          | _ =>
            s.z.openContainer (.list m.kind)
              |>.openContainer (.listItem m.marker m.contentColumn)
        modify fun s => { s with z := z', c := m.after }
        openedListItemThisLine := true
        keepOpening := true
  return openedListItemThisLine

/--
Parses a thematic break after any container prefixes have been consumed.
-/
private def tryThematicBreak : ProcessM Unit := do
  let s ← get
  unless matchThematicBreak s.c do return
  let mut z := s.z
  while (match z.top? with | some (.list _) => true | _ => false) do
    z := z.closeContainer
  throw (z.addBlock (.thematicBreak s.c.toEol))

/--
A blank line closes any open paragraph; list/blockquote frames stay open and may close at the next
non-continuing line.
-/
private def tryBlankLine (openedListItemThisLine : Bool) : ProcessM Unit := do
  let s ← get
  unless isBlankSlice s.c.rest do return
  let mut z := s.z.closeLeaf
  if !openedListItemThisLine then
    if let some lastFrame := z.spine.back? then
      if let .listItem _ _ := lastFrame.container then
        if lastFrame.closedChildren.isEmpty then
          z := z.closeContainer
  -- Only propagate “previous line was blank” when the deepest open container is itself a list item
  -- (case A: blank inside an item's body) or a list (case B: my empty-item close just popped the
  -- list item). Blanks deeper than a list item (e.g. inside a blockquote nested inside a listItem)
  -- are *not* separators between siblings of the enclosing list and so don't make it loose.
  let topIsListLike :=
    match z.spine.back?.map (·.container) with
    | some (.listItem _ _) | some (.list _) => true
    | _ => false
  throw { z with lastWasBlank := topIsListLike && !openedListItemThisLine }

/-- Parses an ATX heading -/
private def tryAtxHeading : ProcessM Unit := do
  let s ← get
  let some m := matchAtxHeading s.c | return
  throw (s.z.addBlock (.atxHeading m.hashes m.content m.closeHashes))

/-- Parses an opening code fence. -/
private def tryFencedCodeOpener : ProcessM Unit := do
  let s ← get
  let some (info, openFence) := matchFenceOpen s.c | return
  throw (s.z.openLeaf (.fencedCode info openFence #[]))

/--
Parses the start of an indented code block.
-/
private def tryIndentedCodeOpener : ProcessM Unit := do
  let s ← get
  unless s.z.openLeaf?.isNone do return
  let (_, indent) := countIndentCols s.c
  unless indent ≥ 4 do return
  throw (s.z.openLeaf (.indentedCode #[(s.c.toEol, indentedCodeLineToString s.c)] #[]))

/--
Starts a new paragraph, or extends the one that's open.

This is the default parser if no others apply.
-/
private def emitParagraph : ProcessM Unit := do
  let s ← get
  let lineFromCursor : Syntax.Range := s.c.toEol
  match s.z.openLeaf? with
  | some (.paragraph _) => throw (s.z.extendParagraph lineFromCursor)
  | _ => throw (s.z.openLeaf (.paragraph #[lineFromCursor]))

/--
Processes a single source line, updating the zipper.
-/
def processLine (z : BlockZipper) (line : Substring.Raw) : BlockZipper :=
  -- Capture and clear `lastWasBlank` at line entry so it represents "the
  -- previous line was blank" for the duration of this call.
  let prevBlank := z.lastWasBlank
  let z : BlockZipper := { z with lastWasBlank := false }
  let init : LineState := { z, c := Cursor.ofLine line, prevBlank }
  let pipeline : ProcessM Unit := do
    let matched ← runContainerM do
      continueContainers
      markEnclosingListLoose
      trySetextHeading
      tryLazyContinuation
    closeNonContinuingContainers matched
    consumeFencedCode
    consumeIndentedCode
    closeFinishedSiblingList
    let openedListItemThisLine ← openContainerPrefixes
    tryThematicBreak
    tryBlankLine openedListItemThisLine
    tryAtxHeading
    tryFencedCodeOpener
    tryIndentedCodeOpener
    emitParagraph
  match pipeline.run init with
  | .ok _ s    => s.z
  | .error z _ => z

/--
Parses the block structure of a string, within the provided range.
-/
def parseBlocksRaw (s : String) (startPos endPos : String.Pos.Raw) :
    Array (Block Syntax.Range) := Id.run do
  let mut z := BlockZipper.empty
  for line in splitLines { str := s, startPos, stopPos := endPos } do
    z := processLine z (rangeToSubstring line s)
  return z.finalize
where
  rangeToSubstring (r : Syntax.Range) (s : String) : Substring.Raw :=
  { str := s, startPos := r.start, stopPos := r.stop }

/--
Scans a link-reference-definition label `[label]` content (between `[` and `]`). Newlines are
permitted inside the label so long as no blank line appears. The label must contain at least one
non-whitespace character. CommonMark §4.7 caps labels at 999 *characters* before the closing `]`; we
approximate this by capping at 1000 source bytes (counting backslash escapes as 2). Returns the
label range and the cursor positioned at the closing `]`.
-/
def scanRefDefLabel (r : InlineRange) : Option (Syntax.Range × InlineRange) := do
  let labelStart := r.startPos
  let mut r := r
  let mut len := 0
  let mut sawNonWs := false
  let mut sawNewline := false
  while len < 1000 do
    if r.isEmpty then break
    let c := r.front
    let rNext := r.drop1
    if c == '\\' && !rNext.isEmpty then
      let esc := rNext.front
      if esc != ' ' && esc != '\t' && esc != '\n' then sawNonWs := true
      sawNewline := false
      r := rNext.drop1
      len := len + 2
    else if c == ']' then
      guard sawNonWs
      return ({ start := labelStart, stop := r.startPos }, r)
    else if c == '[' then
      failure
    else if c == '\n' then
      guard !sawNewline  -- blank line in label
      sawNewline := true
      r := rNext
      len := len + 1
    else
      if c != ' ' && c != '\t' then
        sawNonWs := true
        sawNewline := false
      r := rNext
      len := len + 1
  none

/--
Scans the destination of a link reference definition at the head of `r`. Recognizes the bracketed
`<url>` and unbracketed forms. Returns the URL range (including any `<>` wrappers) and the cursor
positioned just past the destination. Fails on an unclosed `<`, an empty destination, unbalanced
parens, or an embedded `\n`.
-/
def scanRefDefUrl (r : InlineRange) : Option (Syntax.Range × InlineRange) := do
  guard !r.isEmpty
  let urlStart := r.startPos
  if r.front == '<' then
    -- Bracketed: scan until the next `>`; reject `<` and `\n`.
    let mut r := r.drop1
    let mut foundClose := false
    while !r.isEmpty && !foundClose do
      let c := r.front
      let rNext := r.drop1
      if c == '\\' && !rNext.isEmpty then
        r := rNext.drop1
      else if c == '>' then
        r := rNext
        foundClose := true
      else if c == '<' || c == '\n' then
        failure
      else
        r := rNext
    guard foundClose
    return ({ start := urlStart, stop := r.startPos }, r)
  else
    -- Unbracketed: stop at whitespace/control; balance parens.
    let mut r := r
    let mut parenDepth : Nat := 0
    let mut keepGoing := true
    while keepGoing && !r.isEmpty do
      let c := r.front
      let rNext := r.drop1
      if c == '\\' && !rNext.isEmpty then
        r := rNext.drop1
      else if c == ' ' || c == '\t' || c == '\n' then
        keepGoing := false
      else if c == '(' then
        parenDepth := parenDepth + 1
        r := rNext
      else if c == ')' then
        if parenDepth == 0 then keepGoing := false
        else
          parenDepth := parenDepth - 1
          r := rNext
      else if c.toNat < 0x20 then
        keepGoing := false
      else
        r := rNext
    guard <| r.startPos != urlStart  -- non-empty destination
    guard <| parenDepth == 0
    return ({ start := urlStart, stop := r.startPos }, r)

/--
Skips the whitespace gap between a link reference definition's `:` and its destination: spaces,
tabs, and at most one newline. Returns `none` if a blank line (two newlines) is encountered.
-/
def skipRefDefDestGap (r : InlineRange) : Option InlineRange := do
  let mut r := r
  let mut newlinesSeen := 0
  while !r.isEmpty do
    let c := r.front
    if c == ' ' || c == '\t' then r := r.drop1
    else if c == '\n' then
      newlinesSeen := newlinesSeen + 1
      if newlinesSeen ≥ 2 then failure
      r := r.drop1
    else break
  return r

/--
Consumes any same-line trailing whitespace from `r`, then an optional single `\n`. Returns the
cursor past the `\n` (or at end-of-buffer if the line was the last). Returns `none` if
non-whitespace content remains on the line.
-/
def consumeRefDefLineEnd (r : InlineRange) : Option InlineRange := do
  let mut r := r
  while !r.isEmpty && (r.front == ' ' || r.front == '\t') do
    r := r.drop1
  if r.isEmpty then return r
  if r.front == '\n' then return r.drop1
  none

/--
Tries to consume an optional title following the destination of a link reference definition, plus
any trailing whitespace and the line's `\n`. Returns the title content range and the cursor past the
trailing `\n` (or end-of-buffer).

The title may sit on the *same line* as the URL (separated by at least one space or tab and
delimited by `"…"`/`'…'`/`(…)`) or on the *next line*, after exactly one newline plus optional
indentation.

A blank line inside the title is forbidden, as is an unescaped `(` inside a `(…)` title. After the
closing delimiter, only same-line whitespace and an optional trailing newline are permitted;
otherwise the title attempt is abandoned (`none`) so the caller can fall back to a no-title
interpretation.
-/
def refDefTitle (r : InlineRange) : Option (Syntax.Range × InlineRange) := do
  -- Locate the title opener: either same-line after whitespace, or on the
  -- next line after a single newline plus optional leading whitespace.
  let mut sawWs := false
  let mut p := r
  while !p.isEmpty && (p.front == ' ' || p.front == '\t') do
    sawWs := true
    p := p.drop1
  guard !p.isEmpty
  let mut openerR : InlineRange := p
  if p.front == '\n' then
    openerR := p.drop1
    while !openerR.isEmpty && (openerR.front == ' ' || openerR.front == '\t') do
      openerR := openerR.drop1
  else
    guard sawWs
  guard !openerR.isEmpty
  let opener := openerR.front
  guard <| opener == '"' || opener == '\'' || opener == '('
  -- Parse content up to a matching closer; reject blank lines and unescaped
  -- `(` in `(...)` titles.
  let closer : Char := if opener == '(' then ')' else opener
  let afterOpener := openerR.drop1
  let titleContentStart := afterOpener.startPos
  let mut tt := afterOpener
  let mut titleContentEnd := titleContentStart
  let mut foundCloser := false
  let mut bail := false
  let mut lastWasNewline := false
  while !tt.isEmpty && !foundCloser && !bail do
    let c := tt.front
    let curPos := tt.startPos
    let ttNext := tt.drop1
    if c == '\\' && !ttNext.isEmpty then
      tt := ttNext.drop1
      lastWasNewline := false
    else if c == closer then
      titleContentEnd := curPos
      foundCloser := true
      tt := ttNext
    else if c == opener && opener == '(' then
      bail := true  -- unescaped `(` inside a `(...)` title is forbidden
    else if c == '\n' then
      if lastWasNewline then bail := true
      else
        lastWasNewline := true
        tt := ttNext
    else
      if c != ' ' && c != '\t' then lastWasNewline := false
      tt := ttNext
  guard (!bail && foundCloser)
  let afterEol ← consumeRefDefLineEnd tt
  return ({ start := titleContentStart, stop := titleContentEnd }, afterEol)

/--
Tries to parse a CommonMark link reference definition starting at `start` in `source`. Recognizes
both bracketed `<url>` and unbracketed link destinations, and optional `"…"`/`'…'`/`(…)` titles
(which may appear on the line following the URL). The label may span multiple lines, but no blank
line is permitted inside it.

Returns a `RefDefMatch` plus the position one past the last consumed character.
-/
public def linkRefDef (source : InlineSource) (start : String.Pos.Raw) :
    Option (RefDef × String.Pos.Raw) := do
  -- 0–3 leading spaces of indentation. Tabs are *not* allowed at this
  -- point — the source's per-line ranges have already been left-trimmed,
  -- so any tab at the start of a line is part of the content.
  let r0 : InlineRange := { source, startPos := start, stopPos := source.stopPos }
  let (r, indent) := InlineRange.matchRun ' ' r0
  guard (indent ≤ 3)
  -- `[label]`.
  let (openBracket, r) ← InlineRange.matchCharRange '[' r
  let (label, r) ← scanRefDefLabel r
  let (closeBracket, r) ← InlineRange.matchCharRange ']' r
  -- `:`.
  let (colon, r) ← InlineRange.matchCharRange ':' r
  -- Whitespace (including up to one newline) before the destination.
  let r ← skipRefDefDestGap r
  -- Destination.
  let (url, afterUrl) ← scanRefDefUrl r
  -- Optional title; on a syntactic failure or on trailing junk, fall back to
  -- a no-title interpretation, in which case the URL itself must end the
  -- line.
  let (title?, finalRest) ←
    (refDefTitle afterUrl |>.map fun (t, r) => (some t, r)) <|>
    (consumeRefDefLineEnd afterUrl |>.map fun r => (none, r))
  return ({ openBracket, label, closeBracket, colon, url, title? }, finalRest.startPos)

/--
Greedily consumes link ref definitions from the front of `source`.

Returns the extracted `linkRefDef` blocks and a residual `InlineSource`.
-/
public def extractRefDefs (source : InlineSource) :
    Array (Block Syntax.Range) × InlineSource := Id.run do
  let mut defs : Array (Block Syntax.Range) := #[]
  let mut p : String.Pos.Raw := source.startPos
  let mut keep := true
  while keep && p < source.stopPos do
    match linkRefDef source p with
    | none => keep := false
    | some (m, posAfter) =>
      defs := defs.push (.linkRefDef m)
      p := posAfter
  return (defs, source.dropUpTo p)

/--

Walks blocks, extracting link reference definitions off the front of each paragraph and setext-style
heading. Emits a `linkRefDef` block in source order for each successful extraction.

If a setext heading's *entire* content is consumed by extraction, the heading is canceled. The
underline line is reinterpreted as paragraph text and merged with the following paragraph (if any)
without a blank separator, since they were originally one paragraph in source. A setext heading
whose preceding “paragraph” is just link reference definitions is not a heading at all.
-/
partial def postProcessRefDefs (s : String) (blocks : Array (Block Syntax.Range)) :
    Array (Block Syntax.Range) := Id.run do
  let mut out : Array (Block Syntax.Range) := #[]
  let mut i := 0
  while h : i < blocks.size do
    let b := blocks[i]
    match b with
    | .paragraph lines =>
      let (defs, residual) := extractRefDefs (InlineSource.ofLines s lines)
      if defs.isEmpty then
        -- No ref-defs at the front: leave the paragraph untouched so its
        -- original `lines` survive for downstream consumers (e.g. the
        -- semantic-token highlighter).
        out := out.push (.paragraph lines)
      else
        for d in defs do out := out.push d
        unless residual.ranges.isEmpty do
          out := out.push (.paragraph residual.ranges)
    | .setextHeading level lines underline =>
      let (defs, residual) := extractRefDefs (InlineSource.ofLines s lines)
      if defs.isEmpty then
        out := out.push (.setextHeading level lines underline)
      else if !residual.ranges.isEmpty then
        for d in defs do out := out.push d
        out := out.push (.setextHeading level residual.ranges underline)
      else
        for d in defs do out := out.push d
        -- Heading canceled: treat the underline as a paragraph line and,
        -- if the next block is a paragraph (no blank separator existed in
        -- source), merge them so e.g. `[foo]: /url\n===\n[foo]` becomes
        -- a single paragraph `===\n[foo]` after the link ref def is taken.
        let mut combinedLines : Array Syntax.Range := #[underline]
        if h : i + 1 < blocks.size then
          if let .paragraph lines2 := blocks[i + 1] then
            combinedLines := combinedLines ++ lines2
            i := i + 1
        let (defs2, residual2) := extractRefDefs (InlineSource.ofLines s combinedLines)
        for d in defs2 do out := out.push d
        unless residual2.ranges.isEmpty do
          out := out.push (.paragraph residual2.ranges)
    | .blockquote markers children =>
      let newChildren := postProcessRefDefs s children
      out := out.push (.blockquote markers newChildren)
    | .list kind tight items =>
      let newItems := postProcessRefDefs s items
      out := out.push (.list kind tight newItems)
    | .listItem marker children =>
      let newChildren := postProcessRefDefs s children
      out := out.push (.listItem marker newChildren)
    | other => out := out.push other
    i := i + 1
  return out

/--
Builds the document's reference table. Earlier definitions of the same label take precedence.
-/
public partial def buildRefTable (s : String) (blocks : Array (Block Syntax.Range)) :
    RefTable :=
  go blocks |>.run {} |>.2
where
  go (bs : Array (Block Syntax.Range)) : StateM RefTable Unit :=
    bs.forM fun
      | .linkRefDef m => do
        let labelStr := String.Pos.Raw.extract s m.label.start m.label.stop
        let urlRaw := String.Pos.Raw.extract s m.url.start m.url.stop
        let urlStr :=
          if urlRaw.startsWith "<" && urlRaw.endsWith ">" then
            let stripped := urlRaw.rawEndPos
            String.Pos.Raw.extract urlRaw ⟨1⟩ ⟨stripped.byteIdx - 1⟩
          else urlRaw
        let titleStr? := m.title?.map fun r => String.Pos.Raw.extract s r.start r.stop
        let normLabel := normalizeLabel labelStr
        if (← get).contains normLabel then pure ()
        else modify (·.insert normLabel { url := urlStr, title? := titleStr? })
      | .blockquote _ children => go children
      | .list _ _ items => go items
      | .listItem _ children => go children
      | _ => pure ()

/--
Identifies the complete block structure of a Markdown document.
-/
public def parseBlocks (s : String) (startPos endPos : String.Pos.Raw) :
    Array (Block Syntax.Range) :=
  postProcessRefDefs s (parseBlocksRaw s startPos endPos)
