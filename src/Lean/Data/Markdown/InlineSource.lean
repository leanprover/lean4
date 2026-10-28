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
import Init.Data.Array.MapIdx
import Init.Data.Range.Polymorphic.Iterators
import Init.Data.Range.Polymorphic.Nat
import Init.Data.String.OrderInstances
public import Lean.Data.Markdown.Lines

namespace Lean.Markdown

/-!
# Inline Sources

The block parser carves a paragraph or heading into a sequence of source lines with the prefixes of
enclosing containers already removed. The inline parser then reads that content as if it were a
single contiguous string, while still producing subslices of `s`. `InlineSource` bundles the
per-line subslices. Its constructor is private to prevent missing or double normalization.

`ofLines` normalizes a block's lines as CommonMark §4.8 requires, and it is the only way to build an
`InlineSource`.
-/

/--
The lines of a paragraph or setext heading, each as a subslice of the source. These lines form the
input to the inline parser.

Container prefixes such as `>` and leading spaces and tabs are not included in the lines. Each line
except the last line of the block ends with its line ending, so the inline parser sees a line ending
at each line boundary. The last line does not include its trailing whitespace.

The lines are in source order and do not overlap.
-/
public structure InlineSource (s : String.Slice) where
  private mk ::
  /-- The lines, in source order. -/
  lines : Array s.Subslice
  /-- There is at least one line. -/
  nonempty : 0 < lines.size

namespace InlineSource

variable {s : String.Slice}

/-- The first source position of `src`. -/
public def startPos (src : InlineSource s) : s.Pos :=
  (src.lines[0]'src.nonempty).startInclusive

/-- One past the last source position of `src`. -/
public def stopPos (src : InlineSource s) : s.Pos :=
  (src.lines.back src.nonempty).endExclusive

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
Constructs an `InlineSource` from the source lines of a paragraph. This implements the
CommonMark §4.8 paragraph content normalization:

- Leading spaces and tabs are removed from each line.
- Each line except the last ends with the line ending that follows it in the source.
- Trailing whitespace is removed from the last line.
-/
public def ofLines (lines : Lines s) : InlineSource s :=
  let count := lines.toArray.size
  let out := lines.toArray.mapIdx fun idx line =>
    let start := skipSpaces line line.startInclusive
    let stop :=
      if idx + 1 < count then
        (parseLineEnding? s.toSubslice line.endExclusive).getD line.endExclusive
      else line.endExclusive
    subsliceClamped start stop
  have h : 0 < out.size := by simpa [out, Array.size_mapIdx] using lines.nonempty
  let lastIdx := out.size - 1
  have hlt : lastIdx < out.size := Nat.sub_one_lt_of_lt h
  { lines := out.set lastIdx (trimTrailing out[lastIdx] Char.isWhitespace) hlt
    nonempty := by simpa using h }

public instance : Inhabited (InlineSource s) := ⟨ofLines (.singleton default)⟩
