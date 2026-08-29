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
| `**`      | any number of whole path segments, including zero, as its own segment |
| `/`       | separates segments |

## Example

`src/**/*.lean` matches every path that starts with `src/`, ends with a segment matching
`*.lean`, and has any number of segments (including none) in between, e.g. `src/Foo.lean` and
`src/Std/Path/Internal/Glob.lean`, but not `src/Foo.txt` or `other/Foo.lean`.

## Matching

Matching walks the pattern and the path in step, at two levels: `matchSegments` over whole segments,
and `matchParts` over the bytes of one segment. `**` and `*` each try every split of what is left.

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
  if ← «matches» (pchar ']') then return acc
  let c ← satisfy (· != ']')
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

/-- Parse one glob segment: `**` (doublestar) or a sequence of `GlobPart`s. -/
private def globSegment : Parser GlobSegment :=
  attempt (pstring "**" *> notFollowedBy (satisfy (· != '/')) *> pure .doublestar) <|>
  (.pattern <$> many (attempt globPart))

/-- Parse a full glob pattern into a `Glob`. -/
private def globPatternParser : Parser Glob := do
  if ← isEof then return #[]
  let g ← sepBy1 (pchar '/') globSegment
  -- Require the whole pattern to be consumed; otherwise an unterminated `[...]` class (which leaves
  -- the `[` and its tail unparsed) would silently succeed as a partial pattern instead of failing.
  eof
  return g

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

/-- Whether the single character `c` matches `part`. `.star` is handled by `matchParts`. -/
private def matchPart (part : GlobPart) (c : Char) : Bool :=
  match part with
  | .lit c' => c == c'
  | .question => true
  | .star => true
  | .charClass negated elems =>
    let hit := elems.any fun | .inl c' => c == c' | .inr (lo, hi) => lo ≤ c && c ≤ hi
    negated != hit

/--
Match `parts` from token `pi` against the bytes of one path segment, from byte offset `i`.
-/
private partial def matchParts (parts : Array GlobPart) (b : ByteArray) (pi i : Nat) : Bool :=
  if h : pi ≥ parts.size then
    i ≥ b.size
  else
    match parts[pi]'(Nat.lt_of_not_le h) with
    | .star =>
      let rec tryFrom (i' : Nat) : Bool :=
        matchParts parts b (pi + 1) i' ||
        (i' < b.size && tryFrom (i' + (charAt b i').2))
      tryFrom i

    | part =>
      i < b.size &&
        (let (c, w) := charAt b i
         matchPart part c && matchParts parts b (pi + 1) (i + w))

/--
Match `glob` from segment `gi` against `segs` from segment `ci`.

`segs` holds the raw bytes of the path's glob-visible segments, one per element: `?` and a character
class each match one character of a segment, and every byte that is not part of a well-formed UTF-8
encoding matches as a single `U+FFFD`.
-/
partial def matchSegments (glob : Glob) (segs : Array ByteArray) (gi ci : Nat) : Bool :=
  if h : gi ≥ glob.size then
    ci ≥ segs.size
  else
    match glob[gi]'(Nat.lt_of_not_le h) with
    | .doublestar =>
      let rec tryFrom (ci' : Nat) : Bool :=
        matchSegments glob segs (gi + 1) ci' ||
        (ci' < segs.size && tryFrom (ci' + 1))
      tryFrom ci

    | .pattern parts =>
      ci < segs.size &&
      matchParts parts segs[ci]! 0 0 &&
      matchSegments glob segs (gi + 1) (ci + 1)

end Std.Path.Internal
