/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Thrane Christiansen
-/
module

prelude
public import Init.Prelude
public import Init.While
public import Lean.Syntax

public section

namespace Lean.Server.FileWorker.Markdown

/-!
## Line cursors

The block parser walks one line at a time, and within each line it is constantly asking “what's at
column N relative to the parent container's indent?”. Because CommonMark counts indentation in
*columns* but the underlying source is bytes, and a single tab can advance the column by 1–4
(CommonMark §2.2's partial-tab rule), byte position and column are not in lockstep. The cursor is a
structure that tracks both.
-/

/--
A position within a single source line: an unconsumed slice plus the visual column its first byte
sits at.

The pair `(rest.startPos, col)` is the parser's working position. They are kept in sync by the
column-aware advancement primitives below. Direct field updates should preserve the invariant that
`col` is the visual column of `rest.startPos`.
-/
structure Cursor where
  /-- The unconsumed suffix of the current line. -/
  rest : Substring.Raw
  /--
  The visual column of `rest.startPos`. Computed under CommonMark §2.2 tab semantics: a tab advances
  `col` to the next multiple of 4.
  -/
  col : Nat

namespace Cursor

/-- Constructs a cursor at the start of `line` (column 0). -/
@[inline] def ofLine (line : Substring.Raw) : Cursor :=
  { rest := line, col := 0 }

/-- The byte position of the cursor. -/
@[inline] def byteIdx (c : Cursor) : String.Pos.Raw := c.rest.startPos

/-- The end-of-line byte position. -/
@[inline] def stopPos (c : Cursor) : String.Pos.Raw := c.rest.stopPos

/-- The source string. -/
@[inline] def str (c : Cursor) : String := c.rest.str

/-- The `Syntax.Range` from the cursor to end-of-line. -/
@[inline] def toEol (c : Cursor) : Syntax.Range :=
  { start := c.rest.startPos, stop := c.rest.stopPos }

/--
Advances the cursor to byte position `p` and column `newCol`. The caller is responsible for ensuring
`c.byteIdx ≤ p ≤ c.stopPos` and that `newCol` matches the actual column at `p`.
-/
@[inline] def moveTo (c : Cursor) (p : String.Pos.Raw) (newCol : Nat) : Cursor :=
  { rest := { c.rest with startPos := p }, col := newCol }

/--
Peeks the character at the cursor, returning it together with the byte position of the *next*
character. Returns `none` when the cursor is at or past `stopPos` (i.e., at end-of-line for a line
cursor).

For tab-aware advancement use `countIndentCols` or `consumeIndentCapped`.
-/
@[inline] def peek? (c : Cursor) : Option (Char × String.Pos.Raw) :=
  if c.rest.isEmpty then none else some (c.rest.front, (c.rest.drop 1).startPos)

/--
Advances the cursor over a maximal run of characters satisfying `pred`, returning the post-run
cursor and the number of characters consumed.

The column is incremented by the consumed count, which is correct only when `pred` rejects the tab
character (each matched char then advances the column by exactly one). For tab-aware whitespace
skipping use `countIndentCols` or `consumeIndentCapped`.
-/
@[inline] def advanceWhile (c : Cursor) (pred : Char → Bool) : Cursor × Nat := Id.run do
  let mut rest := c.rest
  let mut count := 0
  while !rest.isEmpty do
    let ch := rest.front
    if !pred ch then break
    count := count + 1
    rest := rest.drop 1
  return ({ rest, col := c.col + count }, count)
