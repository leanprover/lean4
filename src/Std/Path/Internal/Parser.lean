/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Path.Component
public import Std.Internal.Parsec.ByteArray

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

Every alternative below is wrapped in `attempt`, since `orElse` backtracks only when the failing
branch consumed nothing.
-/

namespace Std.Path.Internal

open Std.Internal.Parsec Std.Internal.Parsec.ByteArray

/-!
The `limit` threaded through these parsers is the size of the whole input. The `AtMost` combinators
are the ones that succeed at end of input rather than failing with `.eof`, and they take a bound; no
run of bytes within the input can exceed its size, so the bound never truncates.
-/

/--
The longest run of bytes that are not separators, which must be non-empty, read as a segment by
`classify`.
-/
private def segment (classify : ByteArray → Path.Segment) (isSep : UInt8 → Bool) (limit : Nat) :
    Parser Path.Segment :=
  (classify ·.toByteArray) <$> takeWhile1AtMost (!isSep ·) limit

/--
Skip a run of separators, of any length including none.
-/
private def skipSeps (isSep : UInt8 → Bool) (limit : Nat) : Parser Unit :=
  discard <| takeWhileAtMost isSep limit

/--
Every segment of the remaining input, with the runs of separators between them dropped, so that
leading, repeated, and trailing separators contribute no empty segments.
-/
private def segments (classify : ByteArray → Path.Segment) (isSep : UInt8 → Bool) (limit : Nat) :
    Parser (Array Path.Segment) := do
  skipSeps isSep limit
  many (attempt (segment classify isSep limit <* skipSeps isSep limit))

/--
A verbatim path prefix: the literal `\\?\` marker plus the first segment behind it, which names the
volume the rest of the path is read against.

Only `\` ends that segment. Inside a verbatim path Windows gives `/` no meaning, so `\\?\a/b` names
one volume called `a/b` rather than an `a` holding a `b`.

`\\?\UNC\server\share` names a network share, and its two segments belong to the prefix just as
they do in the non-verbatim `\\server\share`.

The marker must be spelled with backslashes, since Windows normalizes `//?/x` like any other path.
-/
private def verbatimPrefix (limit : Nat) : Parser ByteArray := attempt do
  skipBytes verbatimMarker
  let body ←
    (attempt do
        skipBytes uncTag
        discard <| takeWhile1AtMost (· == backslash) limit
        let server ← takeWhile1AtMost (· != backslash) limit
        let share ← attempt (do
            discard <| takeWhile1AtMost (· == backslash) limit
            let share ← takeWhile1AtMost (· != backslash) limit
            return backslashBytes ++ share.toByteArray)
          <|> pure .empty
        return uncTag ++ backslashBytes ++ server.toByteArray ++ share)
      <|> ((·.toByteArray) <$> takeWhileAtMost (· != backslash) limit)
  return verbatimMarker ++ body

/--
A UNC share (`\\server\share`) or a device path (`\\.\COM42`) — one shape: `\\` followed by up to
two segments, returned with its separators canonicalized to `\`.
-/
private def uncPrefix (limit : Nat) : Parser ByteArray := attempt do
  discard <| satisfy isWinSep
  discard <| satisfy isWinSep
  let server ← takeWhile1AtMost (!isWinSep ·) limit
  if server.toByteArray == questionBytes then fail "`?` is not a server name"
  let share ← attempt (do
      discard <| takeWhile1AtMost isWinSep limit
      let share ← takeWhile1AtMost (!isWinSep ·) limit
      return backslashBytes ++ share.toByteArray)
    <|> pure .empty
  return uncMarker ++ server.toByteArray ++ share

/--
A drive letter with its colon, e.g. `C:`.
-/
private def drivePrefix : Parser ByteArray := attempt do
  let drive := (← take 2).toByteArray
  if isDrivePrefix drive then return drive else fail "expected a drive letter"

/--
The prefix at the front of a non-verbatim Windows path, if there is one.

Only these two shapes are a prefix; a leading segment with neither a `:` nor a `\\` ahead of it is
an ordinary name, so `foo\bar` is anchored to nothing.
-/
private def windowsPrefix (limit : Nat) : Parser (Option ByteArray) :=
  (some <$> uncPrefix limit) <|>
  (some <$> drivePrefix) <|>
  pure none

/--
Parse a POSIX path, in which `/` is the only separator and a leading one is the root.
-/
def parsePosix (b : ByteArray) : Path.Anchor × Array Path.Segment :=
  let parser : Parser _ := do
    let rooted ← «matches» (pbyte slash)
    return (if rooted then .posix else .neutral,
      ← segments Path.Segment.ofBytes (· == slash) b.size)
  parser.run b |>.toOption.getD (.neutral, #[])

/--
Parse a Windows path, in which both `\` and `/` separate, an optional prefix comes first, and a
separator behind that prefix is the root.

A verbatim path is read under different rules, because Windows hands one to the filesystem without
normalizing it: only `\` separates, and `.` and `..` are ordinary names rather than the special
segments `normalize` rewrites.
-/
def parseWindows (b : ByteArray) : Path.Anchor × Array Path.Segment :=
  let verbatim : Parser _ := attempt do
    let pre ← verbatimPrefix b.size
    let rooted ← «matches» (pbyte backslash)
    return (.ofWindows (some pre) rooted,
      ← segments Path.Segment.normal (· == backslash) b.size)
  let ordinary : Parser _ := do
    let pre ← windowsPrefix b.size
    let rooted ← «matches» (satisfy isWinSep)
    return (.ofWindows pre rooted, ← segments Path.Segment.ofBytes isWinSep b.size)
  (verbatim <|> ordinary).run b |>.toOption.getD (.neutral, #[])

end Std.Path.Internal
