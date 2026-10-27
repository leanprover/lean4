/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Thrane Christiansen
-/
module

prelude
public import Init.Data.Array.Basic
public import Init.While
import Init.Omega
import Init.Data.String.OrderInstances
public import Lean.Data.Markdown.Inline
public import Lean.Data.Markdown.InlineSource

namespace Lean.Markdown

/-!
# Inline Cursor

`InlineCursor` steps through the lines of an `InlineSource` with `drop1`, skipping the gaps between
lines that contain block markers and removed indentation. `InlineContext` is the reader state of the
inline parser.
-/

variable {s : String.Slice}

/--
A cursor into an `InlineSource`, analogous to a slice of a `String`: the current position, the end
of the input, and the index of the line that contains the current position. A parser that is given a
cursor reads the text from the current position to the end of the input and nothing else.
-/
public structure InlineCursor (s : String.Slice) where
  /-- The source that is being tokenized. -/
  source : InlineSource s
  /--
  The index in `source.lines` of the line that contains `startPos`, or `source.lines.size` if it is
  not contained in any line.
  -/
  line : Nat
  /-- The position of the next character to read. -/
  startPos : s.Pos
  /--
  The position after the last character that the cursor may read.

  It is at most the end of the last line of `source`. It is before the end of the last line when the
  cursor is limited to a part of the source, such as the text between a pair of brackets.
  -/
  stopPos : s.Pos
deriving Inhabited

/-- A cursor at `startPos` whose input ends at `stopPos`. -/
public def InlineSource.cursor (src : InlineSource s) (startPos stopPos : s.Pos) : InlineCursor s :=
  { source := src, line := src.lineIndex startPos, startPos, stopPos }

namespace InlineCursor

variable {s : String.Slice}

/-- Whether the input has been fully consumed. -/
public def isEmpty (cur : InlineCursor s) : Bool :=
  cur.stopPos ≤ cur.startPos

/-- The character at the cursor, if input remains. -/
public def front? (cur : InlineCursor s) : Option Char :=
  if cur.startPos < cur.stopPos then cur.startPos.get? else none

/-- The character at the cursor, or the default character if no input remains. -/
public def front (cur : InlineCursor s) : Char :=
  cur.front?.getD default

/-- The input after the cursor, as a subslice. -/
public def toSubslice (cur : InlineCursor s) : s.Subslice :=
  subsliceClamped cur.startPos cur.stopPos

/-- The character at the cursor as a subslice, if input remains. -/
public def charSubslice? (cur : InlineCursor s) : Option s.Subslice :=
  if h : cur.startPos < cur.stopPos then
    let h' := String.Slice.Pos.ne_endPos_of_lt h
    some (s.subslice cur.startPos (cur.startPos.next h') String.Slice.Pos.le_next)
  else none

/--
Advances the cursor by one character. At the end of a line, the cursor moves to the start of the
next line, skipping the gap between them.
-/
public def drop1 (cur : InlineCursor s) : InlineCursor s :=
  if h : cur.startPos < cur.stopPos then
    let q := cur.startPos.next (String.Slice.Pos.ne_endPos_of_lt h)
    match cur.source.lines[cur.line]? with
    | some lineRange =>
      if q < lineRange.endExclusive then { cur with startPos := q }
      else
        match cur.source.lines[cur.line + 1]? with
        | some nextLine => { cur with line := cur.line + 1, startPos := nextLine.startInclusive }
        | none => { cur with line := cur.line + 1, startPos := q }
    | none => { cur with startPos := q }
  else cur

/--
Parses a line ending at `cur`: `\r\n`, `\r`, or `\n` (CommonMark §2.1). Returns the ending as a
subslice together with the cursor after it. The ending stops at the end of the input, so a `\r`
just before it is a line ending by itself.
-/
public def parseLineEnding? (cur : InlineCursor s) : Option (s.Subslice × InlineCursor s) := do
  let stop ← Lean.Markdown.parseLineEnding? cur.toSubslice cur.startPos
  let mut after := cur.drop1
  if after.startPos < stop then after := after.drop1
  return (subsliceClamped cur.startPos stop, after)

/--
Advances past the characters at the start of `cur` that satisfy `p`.
-/
@[specialize] public partial def skipWhile (cur : InlineCursor s) (p : Char → Bool) :
    InlineCursor s :=
  let lineEnd :=
    match cur.source.lines[cur.line]? with
    | some line => if line.endExclusive < cur.stopPos then line.endExclusive else cur.stopPos
    | none => cur.stopPos
  let pos := go cur.startPos lineEnd
  if pos < lineEnd || lineEnd == cur.stopPos then
    { cur with startPos := pos }
  else
    match lineEnd.prev? with
    | some last => ({ cur with startPos := last }).drop1.skipWhile p
    | none => cur
where
  /-- The first position in `[q, lineEnd)` whose character does not satisfy `p`, or `lineEnd`. -/
  @[specialize] go (q lineEnd : s.Pos) : s.Pos :=
    if h : q < lineEnd then
      let h' := String.Slice.Pos.ne_endPos_of_lt h
      if p (q.get h') then go (q.next h') lineEnd else q
    else q

/--
If `cur` begins with `c`, returns that character as a subslice together with `cur` advanced past it.
-/
public def parseChar? (c : Char) (cur : InlineCursor s) :
    Option (s.Subslice × InlineCursor s) := do
  guard (cur.front? == some c)
  let sub ← cur.charSubslice?
  return (sub, cur.drop1)

/--
Advances past a sequence of `c`s at the start of `cur`. Returns the cursor after the sequence and
its length.
-/
public partial def takeSequence (c : Char) (cur : InlineCursor s) : InlineCursor s × Nat :=
  go cur 0
where
  go (cur : InlineCursor s) (n : Nat) : InlineCursor s × Nat :=
    if cur.front? == some c then go cur.drop1 (n + 1) else (cur, n)

end InlineCursor

/--
Information needed during parsing the inline contents of a block.
-/
public structure InlineContext (s : String.Slice) where
  /-- The link reference definitions of the entire document. -/
  refs : RefTable s
  /-- The content to be parsed. -/
  src : InlineSource s
  /-- The non-standard Markdown extensions that are enabled. -/
  extensions : Extensions

@[inherit_doc InlineContext.refs, inline]
public def refTable [Monad m] : ReaderT (InlineContext s) m (RefTable s) :=
  return (← read).refs

@[inherit_doc InlineContext.src, inline]
public def inlineSource [Monad m] : ReaderT (InlineContext s) m (InlineSource s) :=
  return (← read).src

@[inherit_doc InlineContext.extensions, inline]
public def extensions [Monad m] : ReaderT (InlineContext s) m Extensions :=
  return (← read).extensions
