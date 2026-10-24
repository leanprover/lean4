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
import Init.Data.Range.Polymorphic.Iterators
import Init.Data.Range.Polymorphic.Nat
import Init.Data.String.OrderInstances
public import Lean.Data.Markdown.Basic

namespace Lean.Markdown


/-!
# Inline Source

The block parser carves a paragraph (or heading) into a sequence of source lines, with leading
container prefixes already removed. The inline parser then needs to read that content as if it were
a single contiguous string, while still producing subslices of `s`.
`InlineSource` bundles the per-line subslices, and `InlineCursor` steps through the lines with
`drop1`, skipping the inter-line gaps that contain block markers and removed indentation.
-/

/--
The lines of a paragraph-like block, each as a subslice of the source. A line starts after its
leading spaces and tabs, and the line ending of each non-final line is its last character, so the
inline parser sees a real line ending at each line boundary.

The lines are in source order and do not overlap.
-/
public structure InlineSource (s : String.Slice) where
  /-- The lines, in source order. -/
  lines : Array s.Subslice
deriving Inhabited

namespace InlineSource

variable {s : String.Slice}

/-- The empty source. -/
public def empty : InlineSource s := ⟨#[]⟩

/-- The first source position of `src`, or the start of the string if there are no lines. -/
public def startPos (src : InlineSource s) : s.Pos :=
  match src.lines[0]? with
  | some r => r.startInclusive
  | none => s.startPos

/-- One past the last source position of `src`, or the start of the string if there are no lines. -/
public def stopPos (src : InlineSource s) : s.Pos :=
  match src.lines.back? with
  | some r => r.endExclusive
  | none => s.startPos

/--
The index of the first line that ends after `p`, which is the line that contains `p` when some line
does. This is `src.lines.size` when every line ends at or before `p`.
-/
public def lineIndex (src : InlineSource s) (p : s.Pos) : Nat :=
  go 0 src.lines.size (Nat.le_refl _)
where
  /-- Binary search for the first index in `[lo, hi)` whose line ends after `p`. -/
  go (lo hi : Nat) (h : hi ≤ src.lines.size) : Nat :=
    if hlt : lo < hi then
      have : (lo + hi) / 2 < src.lines.size := by omega
      if p < src.lines[(lo + hi) / 2].endExclusive then go lo ((lo + hi) / 2) (by omega)
      else go ((lo + hi) / 2 + 1) hi h
    else lo
  termination_by hi - lo
  decreasing_by all_goals omega

/--
The part of each line that is within `[p1, p2)`. A line whose part is empty is included when
`[p1, p2)` reaches it, so there is one part per source line that the content spans. If `p1` is past
every line, the result is the single subslice from `p1` to `p2`.
-/
public def linesBetween (src : InlineSource s) (p1 p2 : s.Pos) : Lines s := Id.run do
  let i0 := src.lineIndex p1
  if h : i0 < src.lines.size then
    let mut out := Lines.singleton (clip src.lines[i0])
    for h : i in (i0 + 1)...src.lines.size do
      let r := src.lines[i]
      if p2 < r.startInclusive then break
      out := out.push (clip r)
    return out
  else
    return .singleton (subsliceClamped p1 p2)
where
  /-- The part of `line` that is within `[p1, p2)`, without its line ending. -/
  clip (line : s.Subslice) : s.Subslice :=
    subsliceClamped (max p1 line.startInclusive) (min (textEnd line) p2)
  /-- The end of the text of `line`, before its line ending if it has one. -/
  textEnd (line : s.Subslice) : s.Pos :=
    back line (back line line.endExclusive '\n') '\r'
  /--
  Steps `p` back over one `c`: when the character before `p` is `c` and is within `line`, the
  position of that character; otherwise `p`.
  -/
  back (line : s.Subslice) (p : s.Pos) (c : Char) : s.Pos :=
    match p.prev? with
    | some q => if line.startInclusive ≤ q && q.get? == some c then q else p
    | none => p

/-- The first position at or after `p` in `input` that is not a space or tab. -/
def skipSpaces (input : s.Subslice) (p : s.Pos) : s.Pos := Id.run do
  let mut p := p
  while h : p < input.endExclusive do
    let c := p.get (String.Slice.Pos.ne_endPos_of_lt h)
    if c == ' ' || c == '\t' then
      p := p.next (String.Slice.Pos.ne_endPos_of_lt h)
    else
      break
  return p

/--
Constructs an `InlineSource` from the lines of a paragraph block. This implements the
CommonMark §4.8 paragraph-content normalization:

- Leading spaces and tabs are removed from each line.
- Each non-final line ends with the line ending that follows it in the source.
- Trailing whitespace is removed from the final line.
-/
public def ofLines (lines : Array s.Subslice) : InlineSource s := Id.run do
  let mut out : Array s.Subslice := Array.emptyWithCapacity lines.size
  for h : idx in 0...lines.size do
    let line := lines[idx]
    let start := skipSpaces line line.startInclusive
    let stop :=
      if idx + 1 < lines.size then
        (parseLineEnding? s.toSubslice line.endExclusive).getD line.endExclusive
      else line.endExclusive
    out := out.push (subsliceClamped start stop)
  if h : out.size > 0 then
    let lastIdx := out.size - 1
    have hlt : lastIdx < out.size := Nat.sub_one_lt_of_lt h
    out := out.set lastIdx (trimTrailing out[lastIdx] Char.isWhitespace) hlt
  return ⟨out⟩

/--
A single-line `InlineSource` over `sub`. Used for content that is naturally a single contiguous
source span (e.g. an ATX heading's content).
-/
public def ofSubslice (sub : s.Subslice) : InlineSource s := ⟨#[sub]⟩

/--
Returns an `InlineSource` whose lines represent the suffix of `src` that starts at position `p`.
Lines fully before `p` are dropped and the line that contains `p` (if any) is trimmed to start at
`p`.
-/
public def dropUpTo (src : InlineSource s) (p : s.Pos) : InlineSource s := Id.run do
  let mut out : Array s.Subslice := #[]
  for r in src.lines do
    if r.endExclusive ≤ p then continue
    if r.startInclusive < p then
      out := out.push (subsliceClamped p r.endExclusive)
    else
      out := out.push r
  return ⟨out⟩

end InlineSource

/--
A cursor into an `InlineSource`, analogous to a slice of a `String`: the current position, the end
of the input, and the index of the line that contains the current position. A parser that is given a
cursor reads the text from the current position to the end of the input and nothing else.
-/
public structure InlineCursor (s : String.Slice) where
  /-- The source that is being tokenized. -/
  source : InlineSource s
  /--
  The index in `source.lines` of the line that contains `startPos`, or `source.lines.size` if no
  line does.
  -/
  line : Nat
  /-- The current position. -/
  startPos : s.Pos
  /-- The end of the input. -/
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
If `cur` begins with `c`, returns that character as a subslice together with `cur` advanced past it.
-/
public def parseChar? (c : Char) (cur : InlineCursor s) : Option (s.Subslice × InlineCursor s) := do
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
