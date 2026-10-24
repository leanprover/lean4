/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Thrane Christiansen
-/
module

prelude
public import Init.While
public import Lean.Data.Markdown.Basic

namespace Lean.Markdown


/-!
## Line cursors

The block parser processes one line at a time, and within each line it is constantly asking “what's
at column N relative to the parent container's indent?”. Because CommonMark counts indentation in
*columns* but the underlying source is characters, and a single tab can advance the column by 1–4
(CommonMark §2.2's partial-tab rule), position and column are not in lockstep. The cursor is a
structure that tracks both.
-/

/--
A position within a single source line, together with the line's end and the visual column of the
position.

The pair `(pos, col)` is the parser's working position. They are kept in sync by the column-aware
advancement primitives below. Direct field updates should preserve the invariant that `col` is the
visual column of `pos`.
-/
public structure Cursor (s : String.Slice) where
  /-- The current position. -/
  pos : s.Pos
  /-- The end of the line. -/
  stop : s.Pos
  /--
  The visual column of `pos`. Computed under CommonMark §2.2 tab semantics: a tab advances `col` to
  the next multiple of 4.
  -/
  col : Nat
  /--
  Whether `pos` is at a tab of which some columns, up to `col`, belong to a container prefix or to
  a block's indentation. The remaining columns belong to the line's content.
  -/
  partialTab : Bool := false

namespace Cursor

variable {s : String.Slice}

/-- Constructs a cursor at the start of `line` (column 0). -/
@[inline] public def ofLine (line : s.Subslice) : Cursor s :=
  { pos := line.startInclusive, stop := line.endExclusive, col := 0 }

/-- Whether the cursor is at the end of the line. -/
@[inline] public def isEmpty (c : Cursor s) : Bool := c.stop ≤ c.pos

/-- The remaining text of the line, from the cursor to its end. -/
@[inline] public def toEol (c : Cursor s) : s.Subslice :=
  subsliceClamped c.pos c.stop

/--
Consumes `cols` columns of the tab at the cursor, leaving the position at the tab (CommonMark §2.2's
partial-tab rule). The caller is responsible for ensuring that the tab has that many columns left.
-/
@[inline] public def intoTab (c : Cursor s) (cols : Nat) : Cursor s :=
  { c with col := c.col + cols, partialTab := true }

/-- The character at the cursor, if the cursor is not at the end of the line. -/
@[inline] public def front? (c : Cursor s) : Option Char :=
  if c.pos < c.stop then c.pos.get? else none

/--
The cursor advanced by one character, or unchanged at the end of the line. The column advances by
one, which is correct for every character but a tab; for tabs use `countIndentCols` or
`consumeIndentCapped`.
-/
@[inline] public def next (c : Cursor s) : Cursor s :=
  if h : c.pos < c.stop then
    { c with
      pos := c.pos.next (String.Slice.Pos.ne_endPos_of_lt h)
      col := c.col + 1
      partialTab := false }
  else c

/--
Advances the cursor over the longest prefix of characters that satisfy `pred`, returning the
resulting cursor and the number of characters that it consumes.

The column is incremented by the consumed count, which is correct only when `pred` rejects the tab
character (each matched char then advances the column by exactly one). For tab-aware whitespace
skipping use `countIndentCols` or `consumeIndentCapped`.
-/
@[inline] public def advanceWhile (c : Cursor s) (pred : Char → Bool) : Cursor s × Nat := Id.run do
  let mut c := c
  let mut count := 0
  while h : c.pos < c.stop do
    let h' := String.Slice.Pos.ne_endPos_of_lt h
    if !pred (c.pos.get h') then break
    count := count + 1
    c := { c with pos := c.pos.next h', col := c.col + 1, partialTab := false }
  return (c, count)

/-- Whether the rest of the line is blank (only spaces or tabs). -/
public def isBlank (c : Cursor s) : Bool :=
  let (cAfterWs, _) := c.advanceWhile fun ch => ch == ' ' || ch == '\t'
  cAfterWs.isEmpty

/--
The rest of the line as a line of verbatim block content. A partly consumed tab at the cursor is
excluded from the source, and its remaining columns become the line's leading spaces.
-/
public def verbatimLine (c : Cursor s) : VerbatimLine s :=
  if c.partialTab then
    { source := subsliceClamped c.next.pos c.stop, leadingSpaces := 4 - c.col % 4 }
  else
    { source := c.toEol }

end Cursor
