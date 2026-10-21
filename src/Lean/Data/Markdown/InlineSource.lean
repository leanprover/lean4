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
public import Lean.Data.Markdown.Basic

namespace Lean.Markdown


/-!
# Inline Source View

The block parser carves a paragraph (or heading) into a sequence of source lines, with leading
container prefixes already removed. The inline parser then needs to read that content as if it were
a single contiguous string, while still producing subslices of `s`.
`InlineSource` bundles the per-line ranges, and `InlineRange` is a cursor over it whose `drop1`
steps through the lines while skipping the inter-line gaps that contain block markers and removed
indentation.
-/

/--
The lines of a paragraph-like block, each as a range of the source string. A line's range starts
after its leading spaces and tabs, and the `\n` that ends each non-final line is the range's last
character, so the inline parser sees a real `\n` at each line boundary.

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
Concatenates the text of each line intersected with `[p1, p2)`, in source order. This is the text
that the inline parser reads between `p1` and `p2`, without the inter-line gaps.
-/
public def extract (src : InlineSource s) (p1 p2 : s.Pos) : String :=
  src.lines.foldl (init := "") fun acc r =>
    let lo := if p1 ≤ r.startInclusive then r.startInclusive else p1
    let hi := if r.endExclusive ≤ p2 then r.endExclusive else p2
    if lo < hi then acc ++ (subsliceClamped lo hi).copy else acc

/-- The first position at or after `p` and before `stop` that is not a space or tab. -/
def skipSpaces (p stop : s.Pos) : s.Pos := Id.run do
  let mut p := p
  while h : p < stop do
    let c := p.get (String.Slice.Pos.ne_endPos_of_lt h)
    if c == ' ' || c == '\t' then
      p := p.next (String.Slice.Pos.ne_endPos_of_lt h)
    else
      break
  return p

/--
Constructs an `InlineSource` from the line ranges of a paragraph block. This implements the
CommonMark §4.8 paragraph-content normalization:

- Leading spaces and tabs are removed from each line.
- Each non-final line ends with the `\n` that follows it in the source.
- Trailing whitespace is removed from the final line.
-/
public def ofLines (lines : Array s.Subslice) : InlineSource s := Id.run do
  let mut out : Array s.Subslice := Array.emptyWithCapacity lines.size
  for h : idx in [0 : lines.size] do
    let line := lines[idx]
    let start := skipSpaces line.startInclusive line.endExclusive
    let stop :=
      if idx + 1 < lines.size then
        if h : line.endExclusive ≠ s.endPos then
          if line.endExclusive.get h == '\n' then line.endExclusive.next h else line.endExclusive
        else line.endExclusive
      else line.endExclusive
    out := out.push (subsliceClamped start stop)
  if h : out.size > 0 then
    let lastIdx := out.size - 1
    have hlt : lastIdx < out.size := Nat.sub_one_lt_of_lt h
    let r := out[lastIdx]
    let mut stop := r.endExclusive
    while r.startInclusive < stop do
      match stop.prev? with
      | some q =>
        if r.startInclusive ≤ q && (q.get? matches some ' ' | some '\t' | some '\n' | some '\r') then
          stop := q
        else break
      | none => break
    out := out.set lastIdx (subsliceClamped r.startInclusive stop) hlt
  return ⟨out⟩

/--
A single-line `InlineSource` over `range`. Used for content that is naturally a single contiguous
source span (e.g. an ATX heading's content).
-/
public def ofRange (range : s.Subslice) : InlineSource s := ⟨#[range]⟩

/--
Returns an `InlineSource` whose lines represent the suffix of `src` that starts at position `p`.
Lines fully before `p` are dropped and the line containing `p` (if any) is trimmed to start at `p`.
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
A cursor over an `InlineSource`, analogous to a `String.Slice` over a `String`: the current position,
the position at which the view ends, and the index of the line that contains the current position.
-/
public structure InlineRange (s : String.Slice) where
  /-- The source being tokenized. -/
  source : InlineSource s
  /--
  The index in `source.lines` of the line that contains `startPos`, or `source.lines.size` if no
  line does.
  -/
  line : Nat
  /-- The current position. -/
  startPos : s.Pos
  /-- One past the last position of this view. -/
  stopPos : s.Pos
deriving Inhabited

/-- A cursor at `startPos` whose view ends at `stopPos`. -/
public def InlineSource.range (src : InlineSource s) (startPos stopPos : s.Pos) : InlineRange s :=
  { source := src, line := src.lineIndex startPos, startPos, stopPos }

namespace InlineRange

variable {s : String.Slice}

/-- Whether the view has been fully consumed. -/
public def isEmpty (r : InlineRange s) : Bool :=
  r.stopPos ≤ r.startPos

/-- The character at the cursor, if the view is not empty. -/
public def front? (r : InlineRange s) : Option Char :=
  if r.startPos < r.stopPos then r.startPos.get? else none

/-- The character at the cursor, or the default character if the view is empty. -/
public def front (r : InlineRange s) : Char :=
  r.front?.getD default

/-- The range of the character at the cursor, if the view is not empty. -/
public def charRange? (r : InlineRange s) : Option s.Subslice :=
  if h : r.startPos < r.stopPos then
    some (s.subslice r.startPos (r.startPos.next (String.Slice.Pos.ne_endPos_of_lt h)) String.Slice.Pos.le_next)
  else none

/--
Advances the cursor by one character. At the end of a line, the cursor moves to the start of the
next line, skipping the gap between them.
-/
public def drop1 (r : InlineRange s) : InlineRange s :=
  if h : r.startPos < r.stopPos then
    let q := r.startPos.next (String.Slice.Pos.ne_endPos_of_lt h)
    match r.source.lines[r.line]? with
    | some lineRange =>
      if q < lineRange.endExclusive then { r with startPos := q }
      else
        match r.source.lines[r.line + 1]? with
        | some nextLine => { r with line := r.line + 1, startPos := nextLine.startInclusive }
        | none => { r with line := r.line + 1, startPos := q }
    | none => { r with startPos := q }
  else r

/-- If `r` begins with `c`, returns the range of that character together with `r` advanced past it. -/
public def matchCharRange (c : Char) (r : InlineRange s) : Option (s.Subslice × InlineRange s) := do
  guard (r.front? == some c)
  let range ← r.charRange?
  return (range, r.drop1)

/-- Advances past a sequence of `c`s at the start of `r`. Returns the cursor after the sequence and its length. -/
public partial def matchSequence (c : Char) (r : InlineRange s) : InlineRange s × Nat :=
  go r 0
where
  go (r : InlineRange s) (n : Nat) : InlineRange s × Nat :=
    if r.front? == some c then go r.drop1 (n + 1) else (r, n)

end InlineRange
