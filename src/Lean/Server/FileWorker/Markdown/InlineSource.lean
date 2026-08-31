/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Thrane Christiansen
-/
module

prelude
public import Init.Data.String.PosRaw
public import Init.Data.Array.Basic
public import Init.While
public import Lean.Syntax

public section

namespace Lean.Server.FileWorker.Markdown

/-!
# Inline Source View

The block parser carves a paragraph (or heading) into a sequence of source ranges. There is one per
line, with leading container prefixes already stripped. The inline parser then needs to walk that
content as if it were a single contiguous string, while still emitting `Syntax.Range`s anchored in
the *original* file. `InlineSource` it bundles the underlying file string with the per-line ranges,
and exposes `get`/`next` operations that step through the lines while skipping the inter-line gaps
that contain block markers and stripped indentation.
-/

/--
A view onto a `String` source that exposes a logical concatenation of sub-ranges. Each range is one
paragraph line (or analogous content unit) with block markers such as `>` and leading whitespace
stripped from its `start`. The `\n` after each non-final line is the range's last byte (`stop
- 1`), so walking via `get`/`next` sees real `\n` characters at line boundaries.

Ranges should be non-overlapping.

Positions returned by walking are file offsets in `str`, so inlines produced over an `InlineSource`
are file-anchored without a separate mapping pass.
-/
structure InlineSource where
  /-- The underlying source string. -/
  str : String
  /--
  Per-line ranges in source order. Each `range.start` points past the leading spaces/tabs of its
  line, and each `range.stop` points one past the line's terminating `'\n'`, so the `'\n'` is the
  range's last byte. The trailing range, if its line had no `'\n'`, ends at the document's EOF.
  -/
  ranges : Array Syntax.Range
deriving Inhabited

namespace InlineSource

/-- The empty source. -/
def empty : InlineSource := { str := "", ranges := #[] }

/-- The first source position covered by `s` (or `0` if empty). -/
def startPos (s : InlineSource) : String.Pos.Raw :=
  match s.ranges[0]? with
  | some r => r.start
  | none => 0

/-- One past the last source position covered by `s` (or `0` if empty). -/
def stopPos (s : InlineSource) : String.Pos.Raw :=
  match s.ranges.back? with
  | some r => r.stop
  | none => 0

/-- Whether `p` is at or past the end of the last range. -/
def atEnd (s : InlineSource) (p : String.Pos.Raw) : Bool :=
  p ≥ s.stopPos

/--
Returns the index of the range that contains `p`, or `none` if `p` falls outside every range.
-/
private def findRangeIdx? (s : InlineSource) (p : String.Pos.Raw) : Option Nat :=
  s.ranges.findIdx? fun r =>
    r.start ≤ p && p < r.stop

/--
Returns the character at `p`.

Inside a valid range of `s`, this is simply the character; outside the ranges, it returns
`(default : Char)`.
-/
def get (s : InlineSource) (p : String.Pos.Raw) : Char :=
  match s.findRangeIdx? p with
  | some _ => p.get s.str
  | none => default

/--
Returns the next logical position after `p`. Within a range, advances by the UTF-8 width of the
character at `p`. When that advance would land at the end of `p`'s range, it jumps to the start of a
next range if one exists, or to the end of the current range if not. If `p` is not in any range, it
returns `s.stopPos`.
-/
def next (s : InlineSource) (p : String.Pos.Raw) : String.Pos.Raw :=
  match s.findRangeIdx? p with
  | none => s.stopPos
  | some i =>
    let r := s.ranges[i]!
    let next := p + (p.get s.str)
    if next < r.stop then next
    else if h : i + 1 < s.ranges.size then s.ranges[i + 1].start
    else r.stop

/--
Concatenates the slices of `s.str` covered by each range intersected with `[p1, p2)`, in source
order. This is equivalent to walking via `get`/`next` from `p1` to `p2` (skipping inter-range gaps),
but it can be more efficient.
-/
def extract (s : InlineSource) (p1 p2 : String.Pos.Raw) : String :=
  s.ranges.foldl (init := "") fun acc r =>
    let lo : String.Pos.Raw := ⟨max p1.byteIdx r.start.byteIdx⟩
    let hi : String.Pos.Raw := ⟨min r.stop.byteIdx p2.byteIdx⟩
    if lo < hi then acc ++ String.Pos.Raw.extract s.str lo hi
    else acc

/--
Constructs an `InlineSource` from a source string and the line ranges of a paragraph block. This is
typically the output of `splitLines` plus container- prefix consumption.

It implements the CommonMark §4.8 paragraph-content normalisation directly on file positions:

- Leading spaces and tabs are stripped from each line's start.
- Each non-final line's stop position is extended by one byte when the source has a `'\n'` there.
- Trailing spaces/tabs/`\n`/`\r` are stripped from the *final* line's end, so trailing whitespace
  cannot leak into the rendered output.
-/
def ofLines (str : String) (lines : Array Syntax.Range) : InlineSource := Id.run do
  let mut ranges : Array Syntax.Range := Array.emptyWithCapacity lines.size
  for h : idx in [0 : lines.size] do
    let line := lines[idx]
    let lineSub : Substring.Raw := { str, startPos := line.start, stopPos := line.stop }
    let start := lineSub.trimLeft.startPos
    let stop : String.Pos.Raw :=
      let isNonLastNewline :=
        idx + 1 < lines.size &&
        line.stop < str.rawEndPos &&
        line.stop.get str == '\n'
      if isNonLastNewline then
        line.stop + '\n'
      else line.stop
    ranges := ranges.push { start, stop }
  -- Trim trailing whitespace from the last range (CommonMark §4.8 final-WS removal).
  if h : ranges.size > 0 then
    let lastIdx := ranges.size - 1
    have : ranges.size - 1 < ranges.size := Nat.sub_one_lt_of_lt h
    let r := ranges[lastIdx]
    let lastSub : Substring.Raw := { str, startPos := r.start, stopPos := r.stop }
    ranges := ranges.set lastIdx { r with stop := lastSub.trimRight.stopPos }
  return { str, ranges }

/--
A single-range `InlineSource` over `range` of `str`. Used for content that is naturally a single
contiguous source span (e.g. an ATX heading's content slice).
-/
def ofRange (str : String) (range : Syntax.Range) : InlineSource :=
  { str, ranges := #[range] }

/--
Returns an `InlineSource` whose ranges represent the suffix of `s` that starts at position `p`.
Ranges fully before `p` are dropped and the range containing `p` (if any) is trimmed to start at
`p`.
-/
def dropUpTo (s : InlineSource) (p : String.Pos.Raw) : InlineSource := Id.run do
  let mut out : Array Syntax.Range := #[]
  for r in s.ranges do
    if r.stop ≤ p then continue
    if r.start < p then
      out := out.push { start := p, stop := r.stop }
    else
      out := out.push r
  return { str := s.str, ranges := out }

end InlineSource

/--
A bounded sub-view of an `InlineSource`, analogous to `Substring.Raw`
over a `String`: it carries the parent source plus an explicit
`startPos` / `stopPos` range.
-/
structure InlineRange where
  /-- The parent source. -/
  source : InlineSource
  /-- The current logical position within `source`. -/
  startPos : String.Pos.Raw
  /-- One past the last logical position covered by this view. -/
  stopPos : String.Pos.Raw
deriving Inhabited

/--
Builds an `InlineRange` viewing `[startPos, stopPos)` of `s`.
-/
@[inline] def InlineSource.range (s : InlineSource) (startPos stopPos : String.Pos.Raw) :
    InlineRange :=
  { source := s, startPos, stopPos }

namespace InlineRange

/-- Returns `r` with its `startPos` replaced by `p` (and the same source/stop). -/
@[inline] def withStart (r : InlineRange) (p : String.Pos.Raw) : InlineRange :=
  { r with startPos := p }

/-- Whether this range has been fully consumed. -/
@[inline] def isEmpty (r : InlineRange) : Bool :=
  r.startPos ≥ r.stopPos

/-- The character at the range's `startPos`. -/
@[inline] def front (r : InlineRange) : Char :=
  r.source.get r.startPos

/--
Advances `startPos` by one logical character.
-/
@[inline] def drop1 (r : InlineRange) : InlineRange :=
  { r with startPos := r.source.next r.startPos }

/--
If `r` begins with `c`, returns the range advanced past it. Otherwise returns `none`.
-/
@[inline] def expectChar (c : Char) (r : InlineRange) : Option InlineRange :=
  if !r.isEmpty && r.front == c then some r.drop1 else none

/--
If `r` begins with `c`, returns the source range that covers the character together with `r`
advanced past `c`. Otherwise returns `none`.
-/
@[inline] def matchCharRange (c : Char) (r : InlineRange) : Option (Syntax.Range × InlineRange) :=
  if !r.isEmpty && r.front == c then
    let r' := r.drop1
    some ({ start := r.startPos, stop := r'.startPos }, r')
  else none

/--
Advances past a run of `c`s at the start of `r`. Returns the post-run range and the run length.
-/
partial def matchRun (c : Char) (r : InlineRange) : InlineRange × Nat :=
  go r 0
where
  go (r : InlineRange) (n : Nat) : InlineRange × Nat :=
    if !r.isEmpty && r.front == c then go r.drop1 (n + 1) else (r, n)
