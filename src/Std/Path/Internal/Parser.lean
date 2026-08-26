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
and UTF-8 is self-synchronizing, so a byte-level scan splits UTF-8 input exactly where a
character-level one would while still accepting input that is not valid UTF-8 at all. Segments are
sliced out of the input rather than accumulated byte by byte.

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
The longest run of bytes that are not separators, which must be non-empty.
-/
private def segment (isSep : UInt8 → Bool) (limit : Nat) : Parser Path.Segment :=
  (.ofBytes ·.toByteArray) <$> takeWhile1AtMost (!isSep ·) limit

/--
Skip a run of separators, of any length including none.
-/
private def skipSeps (isSep : UInt8 → Bool) (limit : Nat) : Parser Unit :=
  discard <| takeWhileAtMost isSep limit

/--
Every segment of the remaining input, with the runs of separators between them dropped, so that
leading, repeated, and trailing separators contribute no empty segments.
-/
private def segments (isSep : UInt8 → Bool) (limit : Nat) : Parser (Array Path.Segment) := do
  skipSeps isSep limit
  many (attempt (segment isSep limit <* skipSeps isSep limit))

/--
A verbatim path: the literal `\\?\` marker and the whole rest of the input behind it, which Windows
hands to the filesystem exactly as written. All of it is the prefix, so nothing is left to split
into segments and `normalize` has nothing to rewrite.

The marker must be spelled with backslashes, since Windows normalizes `//?/x` like any other path.
-/
private def verbatimPrefix (limit : Nat) : Parser ByteArray := attempt do
  skipBytes verbatimMarker
  let rest ← takeWhileAtMost (fun _ => true) limit
  return verbatimMarker ++ rest.toByteArray

/--
A UNC share (`\\server\share`) or a device path (`\\.\COM42`) — one shape: `\\` followed by up to
two segments, returned with its separators canonicalized to `\`.

A bare `\\` is not a prefix but a root, keeping `\\` and `\` equivalent as they are on Windows
itself. The share is optional too, so the separator in `\\server\` stays behind as the root.
-/
private def uncPrefix (limit : Nat) : Parser ByteArray := attempt do
  discard <| satisfy isWinSep
  discard <| satisfy isWinSep
  let server ← takeWhile1AtMost (!isWinSep ·) limit
  let share ← attempt (do
      discard <| satisfy isWinSep
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
The Windows prefix at the front of the input, if there is one.

Only these three shapes are a prefix; a leading segment with neither a `:` nor a `\\` ahead of it is
an ordinary name, so `foo\bar` is anchored to nothing.
-/
private def winPrefix (limit : Nat) : Parser (Option ByteArray) :=
  (some <$> verbatimPrefix limit) <|>
  (some <$> uncPrefix limit) <|>
  (some <$> drivePrefix) <|>
  pure none

/--
Parse a POSIX path, in which `/` is the only separator and a leading one is the root.
-/
def parsePosix (b : ByteArray) : Path.Anchor × Array Path.Segment :=
  let parser : Parser _ := do
    let rooted ← «matches» (pbyte slash)
    return (if rooted then .posix else .neutral, ← segments (· == slash) b.size)
  parser.run b |>.toOption.getD (.neutral, #[])

/--
Parse a Windows path, in which both `\` and `/` separate, an optional prefix comes first, and a
separator behind that prefix is the root.
-/
def parseWindows (b : ByteArray) : Path.Anchor × Array Path.Segment :=
  let parser : Parser _ := do
    let pre ← winPrefix b.size
    let rooted ← «matches» (satisfy isWinSep)
    return (.ofWindows pre rooted, ← segments isWinSep b.size)
  parser.run b |>.toOption.getD (.neutral, #[])

end Std.Path.Internal
