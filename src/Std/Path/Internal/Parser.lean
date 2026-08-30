/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Path.Component
import Init.Omega

public section

/-!
# Path.Parser

POSIX and Windows path parsers for `Std.Path`.

Both parsers work on raw bytes. Every character they give meaning to (`/`, `\`, `:`, `?`) is ASCII,
and no byte below `0x80` appears inside a multi-byte UTF-8 or WTF-8 sequence, so a byte-level scan
splits such input exactly where a character-level one would while still accepting input that is not
valid UTF-8 at all. This holds only for those encodings: the same scan over UTF-16 code units would
read a separator out of the middle of a character.

Segments are sliced out of the input rather than accumulated byte by byte.

Neither parser can fail: any byte string the caller does not reject outright (empty, or containing a
null byte) denotes some path.
-/

namespace Std.Path.Internal

/--
The index of the first byte at or after `i` that satisfies `p`, or `b.size` if there is none.
-/
private def findFrom (b : ByteArray) (p : UInt8 → Bool) (i : Nat) : Nat :=
  (b.findIdx? p (start := i)).getD b.size

/--
Every segment of `b` from `start` on, classified by `classify`, with the runs of separators between
them dropped, so that leading, repeated, and trailing separators contribute no empty segments.
-/
private def scanSegments (classify : ByteArray → Path.Segment) (isSep : UInt8 → Bool)
    (b : ByteArray) (start : Nat) : Array Path.Segment :=
  go start start #[]
where
  go (from_ i : Nat) (acc : Array Path.Segment) : Array Path.Segment :=
    if h : i < b.size then
      if isSep b[i] then
        go (i + 1) (i + 1) (if from_ < i then acc.push (classify (b.extract from_ i)) else acc)
      else
        go from_ (i + 1) acc
    else if from_ < b.size then
      acc.push (classify (b.extract from_ b.size))
    else
      acc
  termination_by b.size - i

/--
Whether `b` holds `pat` starting at index `i`, ignoring the case of ASCII letters.

Case-insensitive because the one caller matches the `UNC` tag of a verbatim path, which Windows
resolves through the object manager and so reads in any case.
-/
private def matchesAt (b pat : ByteArray) (i : Nat) : Bool :=
  i + pat.size ≤ b.size && go pat.size
where
  go : Nat → Bool
    | 0 => true
    | k + 1 => toUpperByte b[i + k]! == toUpperByte pat[k]! && go k

/--
The prefix of a verbatim path — the literal `\\?\` marker plus the segment behind it, which names
the volume the rest of the path is read against — together with the index just past it, or `none` if
`b` does not carry the marker.

Only `\` ends the volume segment. Inside a verbatim path Windows gives `/` no meaning, so `\\?\a/b`
names one volume called `a/b` rather than an `a` holding a `b`.

`\\?\UNC\server\share` names a network share, and its two segments belong to the prefix just as they
do in the non-verbatim `\\server\share`; the separator runs between them are written back as a
single `\`. A `\\?\UNC` with no share behind it is an ordinary volume segment instead.

The `UNC` tag is recognized in any case, since Windows resolves it through the object manager: were
only the uppercase spelling a prefix, `\\?\unc\server\share` would put the server and share in
ordinary segments below the root, and the share would stop being the floor that `parent?` and
`dropPrefix?` cannot walk past. The tag is kept in the case it was written in, so rendering the
path writes it back as it came.

The marker itself must be spelled with backslashes, since Windows normalizes `//?/x` like any other
path. `\\?\` with nothing behind it names no volume, so it is not a prefix at all.
-/
private def scanVerbatimPrefix (b : ByteArray) : Option (ByteArray × Nat) :=
  if !startsWithBytes b verbatimMarker then none else
  let n := verbatimMarker.size
  let unc :=
    if matchesAt b uncTag n then
      let i := n + uncTag.size
      let serverStart := findFrom b (· != backslash) i
      let serverEnd := findFrom b (· == backslash) serverStart
      if i < serverStart && serverStart < serverEnd then
        let server := b.extract n i ++ backslashBytes ++ b.extract serverStart serverEnd
        let shareStart := findFrom b (· != backslash) serverEnd
        let shareEnd := findFrom b (· == backslash) shareStart
        if serverEnd < shareStart && shareStart < shareEnd then
          some (server ++ backslashBytes ++ b.extract shareStart shareEnd, shareEnd)
        else
          some (server, serverEnd)
      else none
    else none
  match unc with
  | some (body, e) => some (verbatimMarker ++ body, e)
  | none =>
    let e := findFrom b (· == backslash) n
    if e == n then none else some (verbatimMarker ++ b.extract n e, e)

/--
The prefix at the front of a non-verbatim Windows path, with its separators canonicalized to `\`,
together with the index just past it.

Only two shapes are a prefix: a UNC share or device path (`\\` followed by up to two segments), and
a drive letter with its colon. A leading segment with neither a `:` nor a `\\` ahead of it is an
ordinary name, so `foo\bar` is anchored to nothing. `?` is refused as a server name, since
canonicalizing it would spell the verbatim marker.
-/
private def scanWindowsPrefix (b : ByteArray) : Option ByteArray × Nat :=
  let unc :=
    if 2 ≤ b.size && isWinSep b[0]! && isWinSep b[1]! then
      let serverEnd := findFrom b isWinSep 2
      let server := b.extract 2 serverEnd
      if 2 < serverEnd && server != questionBytes then
        let shareStart := findFrom b (!isWinSep ·) serverEnd
        let shareEnd := findFrom b isWinSep shareStart
        if serverEnd < shareStart && shareStart < shareEnd then
          some (uncMarker ++ server ++ backslashBytes ++ b.extract shareStart shareEnd, shareEnd)
        else
          some (uncMarker ++ server, serverEnd)
      else none
    else none
  match unc with
  | some (pre, e) => (some pre, e)
  | none =>
    if 2 ≤ b.size && isDriveLetter b[0]! && b[1]! == colon then (some (b.extract 0 2), 2)
    else (none, 0)

/--
Parse a POSIX path, in which `/` is the only separator and a leading one is the root.
-/
def parsePosix (b : ByteArray) : Path.Anchor × Array Path.Segment :=
  (if startsWithByte b slash then .posix else .neutral,
    scanSegments Path.Segment.ofBytes (· == slash) b 0)

/--
Parse a Windows path, in which both `\` and `/` separate, an optional prefix comes first, and a
separator behind that prefix is the root.

A verbatim path is read under different rules, because Windows hands one to the filesystem without
normalizing it: only `\` separates, and `.` and `..` are ordinary names rather than the special
segments `normalize` rewrites.
-/
def parseWindows (b : ByteArray) : Path.Anchor × Array Path.Segment :=
  match scanVerbatimPrefix b with
  | some (pre, i) =>
    (.ofWindows (some pre) (i < b.size && b[i]! == backslash),
      scanSegments Path.Segment.normal (· == backslash) b i)
  | none =>
    let (pre, i) := scanWindowsPrefix b
    (.ofWindows pre (i < b.size && isWinSep b[i]!),
      scanSegments Path.Segment.ofBytes isWinSep b i)

end Std.Path.Internal
