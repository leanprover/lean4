/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Init.Data.String.Decode
public import Std.Internal.Parsec.String

public section

/-!
# Path.Glob

Internal glob pattern representation and matching for `Path.matchGlob`.

## Supported combinators

| Pattern   | Matches |
|-----------|---------|
| `*`       | any run of characters within a single path segment (never crosses `/`) |
| `?`       | any single character within a segment (never `/`) |
| `[abc]`   | any one of the listed characters |
| `[a-z]`   | any character in the given range |
| `[!abc]`  | negated class: any character *not* listed |
| `[]abc]`  | a `]` in the leading position is an ordinary member, so `[]` and `[!]` are unterminated |
| `**`      | whole path segments, as its own segment: zero or more before a further segment, one or more at the end of the pattern |
| `/`       | separates segments; every one counts, so `a//b` and `a/b/` are not `a/b` |

## Example

`src/**/*.lean` matches every path that starts with `src/`, ends with a segment matching
`*.lean`, and has any number of segments (including none) in between, e.g. `src/Foo.lean` and
`src/Std/Path/Internal/Glob.lean`, but not `src/Foo.txt` or `other/Foo.lean`.

A trailing `**` is the one that needs a segment to eat: `src/**` names everything below `src`, not
`src` itself, because the `/` before the `**` still has to be there.

## Matching

Matching walks the pattern and the path in step, at two levels: `matchSegments` over whole segments,
and `matchParts` over the bytes of one segment. Both match `**` and `*` greedily against a single
backtracking point, so matching is linear in the input per wildcard rather than exponential in the
number of wildcards.

The path is never decoded: a segment's bytes are matched as they are, and a byte that begins no
well-formed UTF-8 encoding counts as one `U+FFFD` character — exactly what the segment would have
decoded to.
-/

namespace Std.Path.Internal

/--
A single token inside a glob segment pattern.
-/
inductive GlobPart where
  | lit (c : Char)
  | star
  | question
  | charClass (negated : Bool) (elems : Array (Char ⊕ Char × Char))
deriving Inhabited

/--
A single segment of a compiled glob pattern.
-/
inductive GlobSegment where
  | doublestar
  | pattern (parts : Array GlobPart)
deriving Inhabited

/--
A compiled glob pattern: a sequence of segments separated by `/`.
-/
abbrev Glob := Array GlobSegment

open Std.Internal Parsec String

/--
Parse the body of a `[...]` character class, after the opening `[`.
-/
private partial def globClassBody (acc : Array (Char ⊕ Char × Char)) :
    Parser (Array (Char ⊕ Char × Char)) := do
  -- A `]` closes the class everywhere but the leading position, where it is an ordinary member:
  -- `[]]` is the class of `]`, and `[]` and `[!]` are unterminated rather than empty classes.
  if !acc.isEmpty then
    if ← «matches» (pchar ']') then return acc
  let c ← any
  let elem ← attempt (do
      let _ ← pchar '-'
      let d ← satisfy (· != ']')
      return Sum.inr (c, d))
    <|> pure (Sum.inl c)
  globClassBody (acc.push elem)

/-- Parse one `GlobPart` token within a single path segment (stops at `/`). -/
private def globPart : Parser GlobPart :=
  attempt do
    let c ← satisfy (· != '/')
    match c with
    | '*' => return .star
    | '?' => return .question
    | '[' =>
      let negated ← «matches» (pchar '!')
      return .charClass negated (← globClassBody #[])
    | c => return .lit c

/--
Whether two `*` tokens sit next to each other, which is exactly a `**` written inside a segment.
-/
private def hasAdjacentStars (parts : Array GlobPart) : Bool :=
  (parts.foldl (init := (false, false)) fun (found, prevStar) part =>
    let isStar := part matches .star
    (found || (prevStar && isStar), isStar)).1

/-- Parse one glob segment: `**` (doublestar) or a sequence of `GlobPart`s. -/
private def globSegment : Parser GlobSegment :=
  attempt (pstring "**" *> notFollowedBy (satisfy (· != '/')) *> pure .doublestar) <|> do
    let parts ← many (attempt globPart)
    -- `**` is a segment of its own or nothing at all. Reading `src/**Main.lean` as `src/*Main.lean`
    -- would hand back a pattern weaker than the one that was written, so it is rejected instead.
    if hasAdjacentStars parts then fail "`**` must form a whole segment"
    return .pattern parts

/-- Whether `s` is the empty pattern, which a repeated or trailing `/` leaves behind. -/
private def GlobSegment.isEmptyPattern : GlobSegment → Bool
  | .pattern parts => parts.isEmpty
  | .doublestar => false

/--
Drop the empty segment a `/` directly after a `**` leaves behind: the `**` takes that separator with
it, so `a/**/` is `a/**` and `**/` is `**`. Every other separator stands on its own.
-/
private def absorbSeparatorAfterDoublestar (g : Glob) : Glob :=
  (g.foldl (init := (#[], false)) fun (out, afterDoublestar) seg =>
    if seg.isEmptyPattern && afterDoublestar then (out, false)
    else (out.push seg, seg matches .doublestar)).1

/-- Parse a full glob pattern into a `Glob`. -/
private def globPatternParser : Parser Glob := do
  if ← isEof then return #[]
  let g ← sepBy1 (pchar '/') globSegment
  -- Require the whole pattern to be consumed; otherwise an unterminated `[...]` class (which leaves
  -- the `[` and its tail unparsed) would silently succeed as a partial pattern instead of failing.
  eof
  return absorbSeparatorAfterDoublestar g

/--
Parse `pattern` into a `Glob`, or `none` if it is syntactically invalid (e.g. an unterminated
`[...]` character class).
-/
def parseGlob (pattern : String) : Option Glob :=
  match Parser.run globPatternParser pattern with
  | .ok g => some g
  | .error _ => none

/--
The character encoded at byte offset `i` of `b`, with the number of bytes it occupies.

A byte that begins no well-formed encoding decodes to a single `U+FFFD`, exactly as
`String.fromUTF8Lossy` renders it, so matching the raw bytes agrees with matching the decoded
segment without having to decode it first.
-/
private def charAt (b : ByteArray) (i : Nat) : Char × Nat :=
  match b.utf8DecodeChar? i with
  | some c => (c, c.utf8Size)
  | none => (Char.ofNat 0xfffd, 1)

/--
Whether the single character `c` matches `part`. `.star` is handled by `matchParts`.

Under `caseInsensitive` a range is tested against `c` in both ASCII cases rather than against folded
endpoints: folding the endpoints of a range that spans non-letters, such as `[@-B]`, would move it
somewhere it was never written to be.
-/
private def matchPart (part : GlobPart) (c : Char) (caseInsensitive : Bool) : Bool :=
  let eq (a b : Char) := if caseInsensitive then a.toLower == b.toLower else a == b
  let inRange (lo hi : Char) (x : Char) := lo ≤ x && x ≤ hi
  match part with
  | .lit c' => eq c c'
  | .question => true
  | .star => true
  | .charClass negated elems =>
    let hit := elems.any fun
      | .inl c' => eq c c'
      | .inr (lo, hi) =>
        inRange lo hi c
          || (caseInsensitive && (inRange lo hi c.toLower || inRange lo hi c.toUpper))
    negated != hit

/--
Whether every token from `pi` onward is `*`, so the pattern can still match having run out of input.
-/
private def onlyStarsFrom (parts : Array GlobPart) (pi : Nat) : Bool :=
  parts.all (· matches .star) (start := pi)

/--
Match `parts` from token `pi` against the bytes of one path segment, from byte offset `i`.

`star` records the most recent `*`: the token index it sits at, and the byte offset it currently
consumes up to. On a mismatch the search resumes just past that offset, giving the `*` one more
character. Only the most recent `*` needs remembering, because any earlier one can always hand its
work to a later one, so a pattern with `k` stars costs `O(k · n)` rather than the `O(n^k)` of trying
every split — enough to keep `*-*-*-*.log` from hanging on an attacker-chosen file name.
-/
private partial def matchPartsFrom (parts : Array GlobPart) (b : ByteArray) (caseInsensitive : Bool)
    (pi i : Nat) (star : Option (Nat × Nat)) : Bool :=
  -- A thunk, not a `let`-bound `Bool`: evaluating it eagerly would recurse forever.
  let retry : Unit → Bool := fun _ =>
    match star with
    | some (spi, si) =>
      -- Out of input, so widening the `*` cannot help and nothing else can consume the rest.
      if si < b.size then
        let w := (charAt b si).2
        matchPartsFrom parts b caseInsensitive (spi + 1) (si + w) (some (spi, si + w))
      else false
    | none => false

  if i < b.size then
    match parts[pi]? with
    | some .star => matchPartsFrom parts b caseInsensitive (pi + 1) i (some (pi, i))
    | some part =>
      let (c, w) := charAt b i
      if matchPart part c caseInsensitive then
        matchPartsFrom parts b caseInsensitive (pi + 1) (i + w) star
      else retry ()
    | none => retry ()
  else
    onlyStarsFrom parts pi

/--
Match `parts` against the bytes of one path segment.
-/
private def matchParts (parts : Array GlobPart) (b : ByteArray) (caseInsensitive : Bool) : Bool :=
  matchPartsFrom parts b caseInsensitive 0 0 none

/--
Match `glob` from segment `gi` against `segs` from segment `ci`, with `star` recording the most
recent `**` exactly as `matchPartsFrom` records the most recent `*`.
-/
private partial def matchSegmentsFrom (glob : Glob) (segs : Array ByteArray)
    (caseInsensitive : Bool) (gi ci : Nat) (star : Option (Nat × Nat)) : Bool :=
  let retry : Unit → Bool := fun _ =>
    match star with
    | some (sgi, sci) =>
      if sci < segs.size then
        matchSegmentsFrom glob segs caseInsensitive (sgi + 1) (sci + 1) (some (sgi, sci + 1))
      else false
    | none => false

  if h : ci < segs.size then
    match glob[gi]? with
    | some .doublestar =>
      -- A `**` that ends the pattern takes every segment that is left, and one is left here.
      gi + 1 == glob.size
        || matchSegmentsFrom glob segs caseInsensitive (gi + 1) ci (some (gi, ci))
    | some (.pattern parts) =>
      if matchParts parts segs[ci] caseInsensitive then
        matchSegmentsFrom glob segs caseInsensitive (gi + 1) (ci + 1) star
      else retry ()
    | none => retry ()
  else
    -- Out of path. A `**` still standing here is the trailing one, which needs a segment of its own,
    -- so only a pattern that is itself used up matches.
    gi == glob.size

/--
Match `glob` from segment `gi` against `segs` from segment `ci`.

`segs` holds the raw bytes of the path's glob-visible segments, one per element: `?` and a character
class each match one character of a segment, and every byte that is not part of a well-formed UTF-8
encoding matches as a single `U+FFFD`.

`caseInsensitive` folds ASCII letters in literals and character classes; `?`, `*` and `**` are
unaffected, and the segmentation is fixed before matching, so folding can never make a wildcard
cross a `/`.
-/
def matchSegments (glob : Glob) (segs : Array ByteArray) (caseInsensitive : Bool)
    (gi ci : Nat) : Bool :=
  matchSegmentsFrom glob segs caseInsensitive gi ci none

end Std.Path.Internal
