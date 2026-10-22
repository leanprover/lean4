/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Thrane Christiansen
-/
module

prelude
public import Init.Data.Nat.Fold
public import Init.Data.String.TakeDrop
public import Init.While
import Init.Data.Range.Polymorphic.Iterators
import Init.Data.Range.Polymorphic.Nat
public import Lean.Data.Markdown.Basic
public import Lean.Data.Markdown.InlineSource
import Lean.Data.Markdown.Parser.Cursor
import Lean.Data.Markdown.Parser.BlockZipper

namespace Lean.Markdown


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

variable {s : String.Slice}

/--
Skips ASCII spaces at `p`, stopping at `stop`. Returns the count and the position after them.
-/
def skipSpaces (p stop : s.Pos) : Nat × s.Pos := Id.run do
  let mut p := p
  let mut n := 0
  while h : p < stop do
    let h' := String.Slice.Pos.ne_endPos_of_lt h
    if p.get h' == ' ' then
      n := n + 1
      p := p.next h'
    else
      break
  return (n, p)

/--
Counts tab-aware leading whitespace (CommonMark §2.2): each tab advances to the next 4-column tab
stop, computed relative to the cursor's current column. Returns the advanced cursor and the total
number of columns consumed. Tabs are always crossed in full.
-/
def countIndentCols (c : Cursor s) : Cursor s × Nat := Id.run do
  let mut c := c
  let mut cols := 0
  while h : c.pos < c.stop do
    let h' := String.Slice.Pos.ne_endPos_of_lt h
    let ch := c.pos.get h'
    if ch == ' ' then
      cols := cols + 1
      c := { c with pos := c.pos.next h', col := c.col + 1 }
    else if ch == '\t' then
      let advance := 4 - c.col % 4
      cols := cols + advance
      c := { c with pos := c.pos.next h', col := c.col + advance }
    else
      break
  return (c, cols)

/--
Builds a `String` of `n` ASCII spaces.
-/
def spaces (n : Nat) : String :=
  n.fold (init := "") fun _ _ acc => acc.push ' '

/--
Consumes up to `maxCols` columns of leading whitespace at `c`, with tab-aware column counting.
Returns the advanced cursor and the number of columns actually consumed.

Tabs may be split: if a tab would move the cursor past `maxCols`, the position stays at the tab and
the column count advances by exactly the requested amount, leaving “leftover” tab columns for
subsequent consumers (CommonMark §2.2's partial-tab rule).
-/
def consumeIndentCapped (c : Cursor s) (maxCols : Nat) : Cursor s × Nat := Id.run do
  let mut c := c
  let mut cols := 0
  while h : c.pos < c.stop do
    if cols ≥ maxCols then break
    let h' := String.Slice.Pos.ne_endPos_of_lt h
    let ch := c.pos.get h'
    if ch == ' ' then
      cols := cols + 1
      c := { c with pos := c.pos.next h', col := c.col + 1 }
    else if ch == '\t' then
      let advance := 4 - c.col % 4
      if cols + advance > maxCols then
        -- Partial tab: the position stays at the tab; the column advances by the requested amount
        -- only. The remaining tab columns are observable to the next consumer through the cursor's
        -- position and column.
        c := { c with col := c.col + (maxCols - cols) }
        cols := maxCols
      else
        cols := cols + advance
        c := { c with pos := c.pos.next h', col := c.col + advance }
    else
      break
  return (c, cols)

/--
Converts a line of an indented code block into the string that it denotes.

Renders a line of indented-code content: strips up to 4 columns of leading indentation (relative to
the cursor's current column) and materializes any partial-tab leftover as ASCII spaces (CommonMark
§2.2). The cursor may land mid-tab when the indentation doesn't fall on a tab-stop boundary; in that
case, the leftover columns of that tab become spaces in the rendered output.
-/
def indentedCodeLineToString (c : Cursor s) : String := Id.run do
  let (c', _) := consumeIndentCapped c 4
  let mut leftoverPrefix := ""
  let mut contentStart := c'.pos
  if c'.front? == some '\t' && c'.col % 4 != 0 then
    leftoverPrefix := spaces (4 - c'.col % 4)
    contentStart := c'.next.pos
  return leftoverPrefix ++ (subsliceClamped contentStart c.stop).copy

/-- The position after the last character in `[start, stop)` that is not a space or tab. -/
def trimTrailingWs (start stop : s.Pos) : s.Pos := Id.run do
  let mut stop := stop
  while start < stop do
    match stop.prev? with
    | some q =>
      if q.get? == some ' ' || q.get? == some '\t' then stop := q else break
    | none => break
  return stop

/-- Splits `r` into lines, each excluding its trailing `'\n'`. -/
def splitLines (r : s.Subslice) : Array s.Subslice := Id.run do
  let mut lines : Array s.Subslice := #[]
  let mut p := r.startInclusive
  let mut lineStart := r.startInclusive
  while h : p < r.endExclusive do
    let h' := String.Slice.Pos.ne_endPos_of_lt h
    let q := p.next h'
    if p.get h' == '\n' then
      lines := lines.push (subsliceClamped lineStart p)
      lineStart := q
    p := q
  if lineStart < p then
    lines := lines.push (subsliceClamped lineStart p)
  return lines

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
Parses an ATX heading at `c`. Trailing whitespace is trimmed from `content`.
-/
def parseAtxHeading? (c : Cursor s) : Option (AtxHeadingMatch s) :=  do
  let (c, indent) := countIndentCols c
  guard (indent ≤ 3)
  let hashStart := c.pos
  -- CommonMark §4.2 caps ATX heading levels at 6. We scan up to 7 hashes so
  -- sequences of 7 or more fall through the `count ≤ 6` guard below as non-headings.
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
  let mut contentEnd := trimTrailingWs contentStart c.stop
  -- Optional closing `#` sequence: a trailing sequence of `#` characters that
  -- is either preceded by a space/tab or extends to the start of content
  -- (CommonMark §4.2). Strip it from the content range.
  let mut closeStart := contentEnd
  while contentStart < closeStart do
    match closeStart.prev? with
    | some q => if q.get? == some '#' then closeStart := q else break
    | none => break
  let mut closeHashes? : Option s.Subslice := none
  if closeStart < contentEnd then
    if closeStart == contentStart then
      closeHashes? := some (subsliceClamped closeStart contentEnd)
      contentEnd := closeStart
    else if let some beforeClose := closeStart.prev? then
      let cb := beforeClose.get?
      if cb == some ' ' || cb == some '\t' then
        closeHashes? := some (subsliceClamped closeStart contentEnd)
        contentEnd := trimTrailingWs contentStart closeStart
  return {
    level := count
    hashes
    content := subsliceClamped contentStart contentEnd
    closeHashes := closeHashes?
  }

/--
Whether the line at `c` is a thematic break: up to 3 leading spaces, followed by 3+ matching
`*`/`-`/`_` characters, with only spaces or tabs allowed between or after them (CommonMark §4.1).
-/
def isThematicBreak (c : Cursor s) : Bool := Id.run do
  let (c, indent) := countIndentCols c
  if indent > 3 then return false
  let some markerChar := c.front? | return false
  if markerChar != '*' && markerChar != '-' && markerChar != '_' then
    return false
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
      return false
  return markerCount >= 3

/--
Recognizes a setext heading underline (CommonMark §4.3): up to three leading spaces, then a sequence
of `=` (level 1) or `-` (level 2), then optional trailing whitespace. Returns the heading level on
success.

Note: a `---` underline overlaps with the thematic-break syntax. The caller must enforce the
precedence rule: setext header parsing applies only when an open paragraph immediately precedes the
underline; otherwise, the same line is interpreted as a thematic break.
-/
def parseSetextUnderline? (c : Cursor s) : Option Nat := do
  let (c, indent) := countIndentCols c
  guard (indent ≤ 3)
  let markerChar ← c.front?
  guard (markerChar == '=' || markerChar == '-')
  let (cAfterSequence, _) := c.advanceWhile (· == markerChar)
  -- After the sequence, only whitespace is permitted to end of line.
  let (cAfterWs, _) := cAfterSequence.advanceWhile fun ch =>
    ch == ' ' || ch == '\t'
  guard cAfterWs.isEmpty
  return if markerChar == '=' then 1 else 2

/-- Parses an opening code fence at `c`. -/
def parseFenceOpen? (c : Cursor s) : Option (FenceInfo s × s.Subslice) := do
  let (c, indent) := countIndentCols c
  guard (indent ≤ 3)
  let fenceChar ← c.front? >>= FenceChar.ofChar?
  let fenceStart := c.pos
  let (cAfterFence, count) := c.advanceWhile (· == fenceChar.toChar)
  guard (count ≥ 3)
  let openFence := subsliceClamped fenceStart cAfterFence.pos
  let (cAfterWs, _) := cAfterFence.advanceWhile fun ch => ch == ' ' || ch == '\t'
  let infoStart := cAfterWs.pos
  let infoEnd := trimTrailingWs infoStart c.stop
  -- A backtick fence's info string may not contain backticks.
  if fenceChar == .backtick then
    let mut p := infoStart
    while h : p < infoEnd do
      let h' := String.Slice.Pos.ne_endPos_of_lt h
      guard (p.get h' != '`')
      p := p.next h'
  let infoString? : Option s.Subslice :=
    if infoStart < infoEnd then some (subsliceClamped infoStart infoEnd) else none
  return ({ fenceChar, fenceLen := count, openIndent := indent, infoString? }, openFence)

/--
Parses a closing fence on a line whose container prefixes have already been consumed.
The closing fence must match `info`'s character, be at least as long as the opener, and be followed
only by spaces or tabs.
-/
def parseFenceClose? (c : Cursor s) (info : FenceInfo s) : Option s.Subslice := do
  let (indent, p) := skipSpaces c.pos c.stop
  guard (indent ≤ 3)
  let cAtFence := c.moveTo p indent
  guard <| cAtFence.front? == some info.fenceChar.toChar
  let (cAfterFence, count) := cAtFence.advanceWhile (· == info.fenceChar.toChar)
  guard <| count ≥ info.fenceLen
  guard cAfterFence.isBlank
  return subsliceClamped p cAfterFence.pos

/--
Parses a single blockquote marker (`>` plus optional space). Returns the marker and a
cursor positioned just past the consumed prefix (with column adjusted, possibly mid-tab per
CommonMark §2.2's partial-tab rule).
-/
def parseBlockquoteMarker? (c : Cursor s) : Option (s.Subslice × Cursor s) := do
  let (c, indent) := countIndentCols c
  guard (indent ≤ 3)
  guard (c.front? == some '>')
  let afterMarker := c.next
  let marker := subsliceClamped c.pos afterMarker.pos
  -- The blockquote marker `>` is followed by an optional single space (or
  -- one column of a tab, per CommonMark §2.2's partial-tab rule).
  let baseCol := afterMarker.col
  match afterMarker.front? with
  | some ' ' => return (marker, afterMarker.next)
  | some '\t' =>
    let tabStop := baseCol + (4 - baseCol % 4)
    if tabStop == baseCol + 1 then
      -- Tab equivalent to one column; cross it fully.
      return (marker, afterMarker.next)
    else
      -- Partial tab: leave the position in place but advance the column.
      return (marker, afterMarker.moveTo afterMarker.pos (baseCol + 1))
  | _ => return (marker, afterMarker)

/--
A successful list marker match.
-/
structure ListMarkerMatch (s : String.Slice) where
  /-- The marker itself. -/
  marker : s.Subslice
  /-- A cursor positioned just past the absorbed prefix. -/
  after : Cursor s
  /-- The marker's kind.-/
  kind : ListKind
  /--
  The column distance from the input cursor to `after`, which is the minimum indentation of
  subsequent continuation lines.
  -/
  contentColumn : Nat

/-- Parses a bullet or ordered list marker at `c`. -/
def parseListMarker? (c : Cursor s) : Option (ListMarkerMatch s) := do
  let initialCol := c.col
  let (c, indent) := countIndentCols c
  guard (indent ≤ 3)
  let ch ← c.front?
  -- After matching the marker, compute the listItem's content column. Per
  -- CommonMark §5.2: 1 ≤ N ≤ 4 cols of whitespace following the marker are
  -- absorbed into the listItem prefix; if the line is empty after the marker
  -- or has 5+ cols of whitespace (i.e., the content is itself indented
  -- code), the listItem absorbs only one col of whitespace. Tabs may be
  -- partially consumed (CommonMark §2.2).
  let determineContent (afterMarker : Cursor s) : Option (Cursor s) := do
    if afterMarker.isEmpty then
      return { afterMarker with col := afterMarker.col + 1 }
    let nextC ← afterMarker.front?
    guard <| nextC == ' ' || nextC == '\t'
    let (afterWsCursor, wsCols) := countIndentCols afterMarker
    let contentBlank := afterWsCursor.isEmpty
    let absorbCols : Nat :=
      if contentBlank || wsCols >= 5 then 1
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
    -- CommonMark §5.2: an ordered-list marker has 1–9 digits. We scan up to
    -- 10 so sequences of 10 or more digits fall through the `digits ≤ 9` guard below.
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
Whether a list marker matched at the current cursor is allowed to interrupt an open paragraph
(CommonMark §5.2):
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
Whether `kind` is the same kind of list as one already open in a parent. A marker of the same kind
is always allowed to start a new sibling item, even when it would otherwise violate
`listMarkerInterruptsParagraph` (CommonMark §5.2's strict rules apply only when *opening* a list,
not when extending one).
-/
def hasSameKindListAncestor (z : BlockZipper s) (kind : ListKind) : Bool :=
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
def closesEnclosingList (z : BlockZipper s) (kind : ListKind) : Bool :=
  z.spine.findSomeRev? differingListKind |>.getD false
where
  differingListKind (frame : ZipperFrame s) : Option Bool :=
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
def isInterrupt (z : BlockZipper s) (c : Cursor s) : Bool :=
  c.isBlank ||
  (parseBlockquoteMarker? c).isSome ||
  (match parseListMarker? c with
    | some m =>
      hasSameKindListAncestor z m.kind ||
      closesEnclosingList z m.kind ||
      listMarkerInterruptsParagraph m.after m.kind
    | none => false) ||
  (parseAtxHeading? c).isSome ||
  (parseFenceOpen? c).isSome ||
  isThematicBreak c

/-!
# Processing Lines

Lines are processed one at a time. A kind of rightward-only zipper is maintained, allowing blocks to
be added at the lower right of the syntax tree.

Each step of the pipeline is a `ProcessM Unit` named after its description in the CommonMark spec.
Steps that produce the line's final zipper end the pipeline with `finishLine`, while steps that only
mutate the in-flight state fall through to the next.
-/

/--
The state that flows through the late (post-close) steps of `processLine`.
-/
structure LineState (s : String.Slice) where
  /-- The in-progress document. -/
  zipper : BlockZipper s
  /-- The cursor that advances through the block-inducing prefixes of the line. -/
  cursor : Cursor s
  /-- Whether the preceding line was blank.-/
  prevBlank : Bool

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
A state read with `get` is shared with the monad, so extending one of the zipper's arrays would copy
the array. The zipper is changed either inside `modify`, or after `takeState` has taken the state out
of the monad.
-/

/--
Takes the state out of the monad, leaving behind one with an empty zipper, so that the zipper's
arrays can be extended in place. The caller puts a state back with `set`, or ends the line with
`finishLine`.
-/
def takeState : ProcessM s (LineState s) :=
  modifyGet fun st => (st, { st with zipper := .empty })

@[inherit_doc takeState]
def ContainerM.takeState : ContainerM s (ContState s) :=
  modifyGet fun st => (st, { st with zipper := .empty, matched := 0, matched_le := Nat.zero_le _ })

/-- Ends the processing of the current line, with `z` as the document so far. -/
@[inline] def finishLine [MonadExcept (BlockZipper s) m] (z : BlockZipper s) : m α := throw z

/--
Ends the processing of the current line with the zipper that `f` produces from the current one.
-/
def finishLineWith (f : BlockZipper s → BlockZipper s) : ProcessM s Unit := do
  let st ← takeState
  finishLine (f st.zipper)

@[inherit_doc finishLineWith]
def ContainerM.finishLineWith (f : BlockZipper s → BlockZipper s) : ContainerM s Unit := do
  let st ← ContainerM.takeState
  finishLine (f st.zipper)

/--
Lifts a `ContainerM` action to `ProcessM`.
-/
def runContainerM (act : ContainerM s Unit) : ProcessM s Nat := do
  let st ← takeState
  let init : ContState s :=
    { st with matched := 0, matched_le := Nat.zero_le _ }
  match act.run init with
  | .ok _ st'   => set st'.toLineState; return st'.matched
  | .error z _ => finishLine z

/--
Traverses the spine, advancing the cursor past the markers of containers that continue. Updates the
zipper in place (e.g. pushing markers into blockquote frames) and writes `matched`, the number of
inner spine frames that continued, so subsequent steps can close the rest. The document root
continues implicitly and is not counted.
-/
def continueContainers : ContainerM s Unit := do
  let mut st ← ContainerM.takeState
  repeat
    if h : st.matched < st.zipper.spine.size then
      match (st.zipper.spine[st.matched]).container with
      | .blockquote _ =>
        let some (markerRange, cAfter) := parseBlockquoteMarker? st.cursor | break
        st := { st with
          zipper := st.zipper.pushBlockquoteMarker st.matched markerRange
          cursor := cAfter
          matched := st.matched + 1
          matched_le := by rw [BlockZipper.spine_size_pushBlockquoteMarker]; exact h
        }
      | .list _ =>
        -- Lists themselves have no continuation marker; their listItem children do.
        st := { st with matched := st.matched + 1, matched_le := h }
      | .listItem _ contentColumn =>
        -- Try to consume `contentColumn` cols of indent (in cols, tab-aware
        -- with partial-tab support).
        let (cAfter, consumed) := consumeIndentCapped st.cursor contentColumn
        if consumed ≥ contentColumn then
          st := { st with cursor := cAfter, matched := st.matched + 1, matched_le := h }
        else if st.cursor.isBlank then
          -- A blank line continues the listItem (cursor not advanced).
          st := { st with matched := st.matched + 1, matched_le := h }
        else
          break
    else
      break
  set st

/--
Tightness (CommonMark §5.3): if the previous line was blank and the deepest open `listItem` in the
matched range is being extended on this line, mark the *innermost* enclosing list as loose. Outer
list items see the blank as part of their nested child's body, not as a separator between their own
direct children.
-/
def markEnclosingListLoose : ContainerM s Unit := do
  let st ← get
  unless st.prevBlank do return
  -- Indices within the matched range are kept valid using `Fin st.matched` combined with
  -- `st.matched_le`. The traversal goes from `st.matched - 1` down to `0`, breaking on the first
  -- listItem found.
  if h0 : 0 < st.matched then
    let mut i : Fin st.matched := ⟨st.matched - 1, Nat.sub_one_lt_of_lt h0⟩
    repeat
      have h_i : i.val < st.zipper.spine.size := Nat.lt_of_lt_of_le i.isLt st.matched_le
      if let .listItem _ _ := (st.zipper.spine[i]).container then
        if h_pos : 0 < i.val then
          have h_im1 : ↑i - 1 < st.zipper.spine.size := Nat.sub_lt_of_lt h_i
          if let .list _ := (st.zipper.spine[↑i - 1]).container then
            modify fun st' =>
              { st' with
                zipper :=
                  { st'.zipper with
                    spine := st'.zipper.spine.modify (i.val - 1) ({ · with loose := true }) }
                matched_le := by cases st'; simpa
              }
        break
      if h_pos : 0 < i.val then
        i := ⟨i.val - 1,  Nat.sub_lt_of_lt i.isLt⟩
      else
        break

/--
Checks whether to upgrade the preceding block to a Setext header.
-/
def trySetextHeading : ContainerM s Unit := do
  unless (← get).zipper.spine.size == (← get).matched do return
  let some (.paragraph lines) := (← get).zipper.openLeaf? | return
  let cursor := (← get).cursor
  let some level := parseSetextUnderline? cursor | return
  let underline := cursor.toEol
  ContainerM.finishLineWith fun z =>
    BlockZipper.addBlock { z with openLeaf? := none } (.setextHeading level lines underline)

/--
Lazy paragraph continuation: if some containers failed to continue but we have an open paragraph and
the line is not an interrupt (i.e. doesn't open some other kind of block), the line lazily continues
the paragraph in its deepest open context.
-/
def tryLazyContinuation : ContainerM s Unit := do
  unless (← get).zipper.spine.size > (← get).matched do return
  let some (.paragraph _) := (← get).zipper.openLeaf? | return
  let cursor := (← get).cursor
  if isInterrupt (← get).zipper cursor then return
  ContainerM.finishLineWith (·.extendParagraph cursor.toEol)

/--
Closes any spine containers that did not continue on this line. Takes the `matched` count produced
by the container continuation phase as an argument and closes the suffix of the parents that are
indicated.
-/
def closeNonContinuingContainers (matched : Nat) : ProcessM s Unit :=
  modify fun st => { st with zipper := closeAbove st.zipper }
where
  /-- Closes containers until at most `matched` spine frames remain. -/
  closeAbove (z : BlockZipper s) : BlockZipper s := Id.run do
    let mut z := z
    while z.spine.size > matched do
      z := z.closeContainer
    return z

/--
Fenced code consumes lines verbatim until a matching closing fence appears. Either way, this step
finalizes the line.
-/
def consumeFencedCode : ProcessM s Unit := do
  let some (.fencedCode info _ _) := (← get).zipper.openLeaf? | return
  let cursor := (← get).cursor
  match parseFenceClose? cursor info with
  | some closeFence => finishLineWith (·.closeFencedCode closeFence)
  | none => finishLineWith (·.extendFencedCode cursor.toEol)

/--
Indented code consumes 4+-indented lines verbatim and records blank lines provisionally. Any other
line closes the block and falls through to the remaining steps.
-/
def consumeIndentedCode : ProcessM s Unit := do
  let some (.indentedCode _ _) := (← get).zipper.openLeaf? | return
  let cursor := (← get).cursor
  let rendered := indentedCodeLineToString cursor
  if cursor.isBlank then
    let (cAfter, _) := consumeIndentCapped cursor 4
    let range := subsliceClamped cAfter.pos cursor.stop
    finishLineWith (·.indentedCodeAddBlank range rendered)
  let (_, indent) := countIndentCols cursor
  if indent ≥ 4 then
    let (cAfter, _) := consumeIndentCapped cursor 4
    let range := subsliceClamped cAfter.pos cursor.stop
    finishLineWith (·.indentedCodeAddLine range rendered)
  modify fun st => { st with zipper := st.zipper.closeLeaf }

/--
If the deepest container is a list whose previous item just closed and this line is non-blank
without a sibling marker, close the list so subsequent content doesn't become a stray child.
-/
def closeFinishedSiblingList : ProcessM s Unit := do
  let some (.list _) := (← get).zipper.top? | return
  let cursor := (← get).cursor
  if !cursor.isBlank && (parseListMarker? cursor).isNone then
    modify fun st => { st with zipper := st.zipper.closeContainer }

/--
Opens as many container prefixes (blockquote, list-item) as the line provides, in order. Returns
whether a list item was opened on this line, because the blank line handler downstream needs that
information to distinguish an empty list item's body from a blank-line separator.

Thematic break has higher precedence than list markers (CommonMark §5.2: `* * *` is a thematic
break, not a one-item list), so each iteration short-circuits when a thematic break starts at the
current cursor.
-/
def openContainerPrefixes : ProcessM s Bool := do
  let mut openedListItemThisLine := false
  repeat
    let cursor := (← get).cursor
    if isThematicBreak cursor then break
    if let some (markerRange, cAfter) := parseBlockquoteMarker? cursor then
      modify fun st =>
        { st with zipper := st.zipper.openContainer (.blockquote #[markerRange]), cursor := cAfter }
    else if let some m := parseListMarker? cursor then
      -- The strict §5.2 rules (non-empty content, start-1 for ordered) apply
      -- only when *opening* a new list. A same-kind marker that extends an
      -- already-open list as a new sibling item is always allowed.
      let interruptingPara := match (← get).zipper.openLeaf? with
        | some (.paragraph _) => true
        | _ => false
      if interruptingPara && !hasSameKindListAncestor (← get).zipper m.kind
          && !listMarkerInterruptsParagraph m.after m.kind then
        break
      else
        modify fun st =>
          let z := st.zipper
          let z :=
            match z.top? with
            | some (.list k) =>
              if k.sameKind m.kind then
                -- Blank-line-then-new-sibling-item makes the list loose.
                let z :=
                  if st.prevBlank then
                    let lastIdx := z.spine.size - 1
                    { z with spine := z.spine.modify lastIdx fun f => { f with loose := true } }
                  else z
                z.openContainer (.listItem m.marker m.contentColumn)
              else
                z.closeContainer
                  |>.openContainer (.list m.kind)
                  |>.openContainer (.listItem m.marker m.contentColumn)
            | _ =>
              z.openContainer (.list m.kind)
                |>.openContainer (.listItem m.marker m.contentColumn)
          { st with zipper := z, cursor := m.after }
        openedListItemThisLine := true
    else
      break
  return openedListItemThisLine

/--
Parses a thematic break after any container prefixes have been consumed.
-/
def tryThematicBreak : ProcessM s Unit := do
  let cursor := (← get).cursor
  unless isThematicBreak cursor do return
  let line := cursor.toEol
  finishLineWith fun z => Id.run do
    let mut z := z
    while (match z.top? with | some (.list _) => true | _ => false) do
      z := z.closeContainer
    return z.addBlock (.thematicBreak line)

/--
A blank line closes any open paragraph; list/blockquote frames stay open and may close at the next
non-continuing line.
-/
def tryBlankLine (openedListItemThisLine : Bool) : ProcessM s Unit := do
  unless (← get).cursor.isBlank do return
  finishLineWith fun z => Id.run do
    let mut z := z.closeLeaf
    if !openedListItemThisLine then
      if let some lastFrame := z.spine.back? then
        if let .listItem _ _ := lastFrame.container then
          if lastFrame.closedChildren.isEmpty then
            z := z.closeContainer
    -- Only propagate “previous line was blank” when the deepest open container is itself a list
    -- item (case A: blank inside an item's body) or a list (case B: my empty-item close just popped
    -- the list item). Blanks deeper than a list item (e.g. inside a blockquote nested inside a
    -- listItem) are *not* separators between siblings of the enclosing list and so don't make it
    -- loose.
    let topIsListLike :=
      match z.spine.back?.map (·.container) with
      | some (.listItem _ _) | some (.list _) => true
      | _ => false
    return { z with lastWasBlank := topIsListLike && !openedListItemThisLine }

/-- Parses an ATX heading -/
def tryAtxHeading : ProcessM s Unit := do
  let some m := parseAtxHeading? (← get).cursor | return
  finishLineWith (·.addBlock (.atxHeading m.level m.hashes m.content m.closeHashes))

/-- Parses an opening code fence. -/
def tryFencedCodeOpener : ProcessM s Unit := do
  let some (info, openFence) := parseFenceOpen? (← get).cursor | return
  finishLineWith (·.openLeaf (.fencedCode info openFence #[]))

/--
Parses the start of an indented code block.
-/
def tryIndentedCodeOpener : ProcessM s Unit := do
  unless (← get).zipper.openLeaf?.isNone do return
  let cursor := (← get).cursor
  let (_, indent) := countIndentCols cursor
  unless indent ≥ 4 do return
  let (cAfter, _) := consumeIndentCapped cursor 4
  let range := subsliceClamped cAfter.pos cursor.stop
  let rendered := indentedCodeLineToString cursor
  finishLineWith (·.openLeaf (.indentedCode #[(range, rendered)] #[]))

/--
Starts a new paragraph, or extends the one that's open.

This is the default parser if no others apply.
-/
def emitParagraph : ProcessM s Unit := do
  let line := (← get).cursor.toEol
  match (← get).zipper.openLeaf? with
  | some (.paragraph _) => finishLineWith (·.extendParagraph line)
  | _ => finishLineWith (·.openLeaf (.paragraph #[line]))

/--
Processes a single source line, updating the zipper.
-/
def processLine (z : BlockZipper s) (line : s.Subslice) : BlockZipper s :=
  -- Capture and clear `lastWasBlank` at line entry so it represents "the
  -- previous line was blank" for the duration of this call.
  let prevBlank := z.lastWasBlank
  let z : BlockZipper s := { z with lastWasBlank := false }
  let init : LineState s := { zipper := z, cursor := Cursor.ofLine line, prevBlank }
  let pipeline : ProcessM s Unit := do
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
  | .ok _ st    => st.zipper
  | .error z _ => z

/-- Moves the start of `line` past up to `indent` leading spaces. -/
def dropIndent (line : s.Subslice) (indent : Nat) : s.Subslice := Id.run do
  let mut p := line.startInclusive
  for _ in 0...indent do
    if h : p < line.endExclusive then
      let h' := String.Slice.Pos.ne_endPos_of_lt h
      if p.get h' == ' ' then p := p.next h' else break
    else break
  return subsliceClamped p line.endExclusive

/--
Parses the block structure of `s`. Up to `indent` leading spaces of each line are skipped.
-/
def parseBlocksRaw (s : String.Slice) (indent : Nat := 0) : Array (Block.Raw s) := Id.run do
  let mut z := BlockZipper.empty
  for line in splitLines s.toSubslice do
    z := processLine z (dropIndent line indent)
  return z.finalize

/--
Parses the content of a link label (CommonMark §6.3) at `cur`, which is positioned just
after the `[`.
Newlines are permitted inside the label so long as no blank line appears, and unescaped brackets are
not. The label must contain at least one non-whitespace character and at most 999 characters.
Returns the label's lines and the cursor positioned at the closing `]`.
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
    if c == '\\' && !curNext.isEmpty then
      let esc := curNext.front
      if esc != ' ' && esc != '\t' && esc != '\n' then sawNonWs := true
      sawNewline := false
      cur := curNext.drop1
      len := len + 2
    else if c == ']' then
      guard sawNonWs
      return (cur.source.linesBetween labelStart cur.startPos, cur)
    else if c == '[' then
      failure
    else if c == '\n' then
      guard !sawNewline  -- blank line in label
      sawNewline := true
      cur := curNext
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
bracketed `<url>` or unbracketed form. Returns the destination and the cursor positioned just past
it. Fails
on an unclosed `<`, an empty destination, unbalanced parens, or an embedded `\n`.
-/
def parseRefDefUrl? (cur : InlineCursor s) : Option (LinkDestination s × InlineCursor s) := do
  let urlStart := cur.startPos
  if cur.front? == some '<' then
    -- Bracketed: scan until the next `>`; reject `<` and `\n`.
    let openAngle ← cur.charSubslice?
    let mut cur := cur.drop1
    let urlContentStart := cur.startPos
    let mut closeAngle? : Option s.Subslice := none
    while !cur.isEmpty && closeAngle?.isNone do
      let c := cur.front
      let curNext := cur.drop1
      if c == '\\' && !curNext.isEmpty then
        cur := curNext.drop1
      else if c == '>' then
        closeAngle? := cur.charSubslice?
        cur := curNext
      else if c == '<' || c == '\n' then
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
      if c == '\\' && !curNext.isEmpty then
        cur := curNext.drop1
      else if c == ' ' || c == '\t' || c == '\n' then
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
tabs, and at most one newline. Returns `none` if a blank line (two newlines) is encountered.
-/
def skipRefDefDestGap (cur : InlineCursor s) : Option (InlineCursor s) := do
  let mut cur := cur
  let mut newlinesSeen := 0
  repeat
    let some c := cur.front? | break
    if c == ' ' || c == '\t' then cur := cur.drop1
    else if c == '\n' then
      newlinesSeen := newlinesSeen + 1
      if newlinesSeen ≥ 2 then failure
      cur := cur.drop1
    else break
  return cur

/--
Consumes any same-line trailing whitespace from `cur`, then an optional single `\n`. Returns the
cursor past the `\n` (or at end-of-buffer if the line was the last). Returns `none` if
non-whitespace content remains on the line.
-/
def consumeRefDefLineEnd (cur : InlineCursor s) : Option (InlineCursor s) := do
  let mut cur := cur
  while cur.front? == some ' ' || cur.front? == some '\t' do
    cur := cur.drop1
  if cur.isEmpty then return cur
  if cur.front? == some '\n' then return cur.drop1
  none

/--
Tries to consume an optional title following the destination of a link reference definition, plus
any trailing whitespace and the line's `\n`. Returns the title and the cursor past the trailing `\n`
(or end-of-buffer).

The title may sit on the *same line* as the URL (separated by at least one space or tab and
delimited by `"…"`/`'…'`/`(…)`) or on the *next line*, after exactly one newline plus optional
indentation.

A blank line inside the title is forbidden, as is an unescaped `(` inside a `(…)` title. After the
closing delimiter, only same-line whitespace and an optional trailing newline are permitted;
otherwise the title attempt is abandoned (`none`) so the caller can fall back to a no-title
interpretation.
-/
def parseRefDefTitle? (cur : InlineCursor s) : Option (LinkTitle s × InlineCursor s) := do
  -- Locate the title opener: either same-line after whitespace, or on the
  -- next line after a single newline plus optional leading whitespace.
  let mut sawWs := false
  let mut p := cur
  while p.front? == some ' ' || p.front? == some '\t' do
    sawWs := true
    p := p.drop1
  let mut openerR : InlineCursor s := p
  if p.front? == some '\n' then
    openerR := p.drop1
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
    if c == '\\' && !ttNext.isEmpty then
      tt := ttNext.drop1
      lastWasNewline := false
    else if c == closer then
      titleContentEnd := curPos
      closerRange? := tt.charSubslice?
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
  guard !bail
  let closerRange ← closerRange?
  let afterEol ← consumeRefDefLineEnd tt
  let title : LinkTitle s :=
    { opener := openerRange, content := cur.source.linesBetween titleContentStart titleContentEnd,
      closer := closerRange }
  return (title, afterEol)

/--
Tries to parse a CommonMark link reference definition starting at `start` in `source`. Recognizes
both bracketed `<url>` and unbracketed link destinations, and optional `"…"`/`'…'`/`(…)` titles
(which may appear on the line following the URL). The label may span multiple lines, but no blank
line is permitted inside it.

Returns the definition plus the position one past the last consumed character.
-/
public def parseLinkRefDef? (source : InlineSource s) (start : s.Pos) : Option (RefDef s × s.Pos) := do
  -- 0–3 spaces of indentation. `InlineSource.ofLines` has already removed each line's leading
  -- spaces and tabs.
  let cur0 := source.cursor start source.stopPos
  let (cur, indent) := cur0.takeSequence ' '
  guard (indent ≤ 3)
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

/--
Traverses blocks, extracting link reference definitions off the front of each paragraph and setext-style
heading. Emits a `linkRefDef` block in source order for each successful extraction.

If a setext heading's *entire* content is consumed by extraction, the heading is canceled. The
underline line is reinterpreted as paragraph text and merged with the following paragraph (if any)
without a blank separator, since they were originally one paragraph in source. A setext heading
whose preceding “paragraph” is just link reference definitions is not a heading at all.
-/
partial def postProcessRefDefs (blocks : Array (Block.Raw s)) : Array (Block.Raw s) := Id.run do
  let mut out : Array (Block.Raw s) := #[]
  let mut i := 0
  while h : i < blocks.size do
    let b := blocks[i]
    match b with
    | .paragraph lines =>
      let (defs, residual) := extractRefDefs (InlineSource.ofLines lines)
      if defs.isEmpty then
        -- No ref-defs at the front: keep the paragraph's original lines.
        out := out.push (.paragraph lines)
      else
        for d in defs do out := out.push d
        unless residual.lines.isEmpty do
          out := out.push (.paragraph residual.lines)
    | .setextHeading level lines underline =>
      let (defs, residual) := extractRefDefs (InlineSource.ofLines lines)
      if defs.isEmpty then
        out := out.push (.setextHeading level lines underline)
      else if !residual.lines.isEmpty then
        for d in defs do out := out.push d
        out := out.push (.setextHeading level residual.lines underline)
      else
        for d in defs do out := out.push d
        -- Heading canceled: treat the underline as a paragraph line and,
        -- if the next block is a paragraph (no blank separator existed in
        -- source), merge them so e.g. `[foo]: /url\n===\n[foo]` becomes
        -- a single paragraph `===\n[foo]` after the link ref def is taken.
        let mut combinedLines : Array s.Subslice := #[underline]
        if h : i + 1 < blocks.size then
          if let .paragraph lines2 := blocks[i + 1] then
            combinedLines := combinedLines ++ lines2
            i := i + 1
        let (defs2, residual2) := extractRefDefs (InlineSource.ofLines combinedLines)
        for d in defs2 do out := out.push d
        unless residual2.lines.isEmpty do
          out := out.push (.paragraph residual2.lines)
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
Builds the document's reference table. Earlier definitions of the same label take precedence.
-/
public partial def buildRefTable (blocks : Array (Block.Raw s)) : RefTable s :=
  go blocks |>.run {} |>.2
where
  go (bs : Array (Block.Raw s)) : StateM (RefTable s) Unit :=
    bs.forM fun
      | .linkRefDef m => do
        let normLabel := normalizeLabel m.label
        if (← get).contains normLabel then pure ()
        else modify (·.insert normLabel m)
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
