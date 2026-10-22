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
`InlineSource` bundles the per-line subslices, and `InlineCursor` steps through the lines with
`drop1`, skipping the inter-line gaps that contain block markers and removed indentation.
-/

/--
The lines of a paragraph-like block, each as a subslice of the source. A line starts after its
leading spaces and tabs, and the `\n` that ends each non-final line is its last character, so the
inline parser sees a real `\n` at each line boundary.

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

/--
The part of each line that is within `[p1, p2)`, in source order and without the line endings. A
line whose part is empty is included when `[p1, p2)` reaches it, so there is one part per source
line that the content spans.
-/
public def linesBetween (src : InlineSource s) (p1 p2 : s.Pos) : Array s.Subslice :=
  src.lines.foldl (init := #[]) fun acc r =>
    if p1 < r.endExclusive && r.startInclusive ≤ p2 then
      let stop := textEnd r
      let lo := if p1 ≤ r.startInclusive then r.startInclusive else p1
      let hi := if stop ≤ p2 then stop else p2
      acc.push (subsliceClamped lo hi)
    else acc
where
  /-- The end of the line's text, before its `\n` if it has one. -/
  textEnd (r : s.Subslice) : s.Pos :=
    match r.endExclusive.prev? with
    | some q => if r.startInclusive ≤ q && q.get? == some '\n' then q else r.endExclusive
    | none => r.endExclusive

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
Constructs an `InlineSource` from the lines of a paragraph block. This implements the
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
A single-line `InlineSource` over `sub`. Used for content that is naturally a single contiguous
source span (e.g. an ATX heading's content).
-/
public def ofSubslice (sub : s.Subslice) : InlineSource s := ⟨#[sub]⟩

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
public structure InlineCursor (s : String.Slice) where
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
public def InlineSource.cursor (src : InlineSource s) (startPos stopPos : s.Pos) : InlineCursor s :=
  { source := src, line := src.lineIndex startPos, startPos, stopPos }

namespace InlineCursor

variable {s : String.Slice}

/-- Whether the view has been fully consumed. -/
public def isEmpty (r : InlineCursor s) : Bool :=
  r.stopPos ≤ r.startPos

/-- The character at the cursor, if the view is not empty. -/
public def front? (r : InlineCursor s) : Option Char :=
  if r.startPos < r.stopPos then r.startPos.get? else none

/-- The character at the cursor, or the default character if the view is empty. -/
public def front (r : InlineCursor s) : Char :=
  r.front?.getD default

/-- The character at the cursor as a subslice, if the view is not empty. -/
public def charSubslice? (r : InlineCursor s) : Option s.Subslice :=
  if h : r.startPos < r.stopPos then
    some (s.subslice r.startPos (r.startPos.next (String.Slice.Pos.ne_endPos_of_lt h)) String.Slice.Pos.le_next)
  else none

/--
Advances the cursor by one character. At the end of a line, the cursor moves to the start of the
next line, skipping the gap between them.
-/
public def drop1 (r : InlineCursor s) : InlineCursor s :=
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

/-- If `r` begins with `c`, returns that character as a subslice together with `r` advanced past it. -/
public def matchChar (c : Char) (r : InlineCursor s) : Option (s.Subslice × InlineCursor s) := do
  guard (r.front? == some c)
  let sub ← r.charSubslice?
  return (sub, r.drop1)

/-- Advances past a sequence of `c`s at the start of `r`. Returns the cursor after the sequence and its length. -/
public partial def matchSequence (c : Char) (r : InlineCursor s) : InlineCursor s × Nat :=
  go r 0
where
  go (r : InlineCursor s) (n : Nat) : InlineCursor s × Nat :=
    if r.front? == some c then go r.drop1 (n + 1) else (r, n)

end InlineCursor
