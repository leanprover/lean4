/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Init.Data.String
public import Init.Data.Array.Basic
public import Init.Data.Option.Basic
public import Init.Data.BEq
public import Init.Data.Hashable
public import Init.Data.Ord.Basic
public import Init.Data.Repr
public import Init.Data.ToString.Basic
public import Std.Path.Internal.Bytes

public section

/-!
# Path.Anchor and Path.Segment

The two pieces a `Std.Path` is built from: `Path.Anchor`, what the path is anchored to and the sole
carrier of its POSIX/Windows flavour, and `Path.Segment`, one `.`, `..`, or ordinary name. The
`Path` structure itself is defined in `Std.Path.Basic`.
-/

namespace Std

open Path.Internal

/--
What a path is anchored to.

This is the only place a path's platform flavour lives: `posix` and `windows` fix the syntax the
path was parsed with and will be rendered in, while `neutral` fixes neither. Every other part of a
`Path` — its segments — means the same thing on both platforms.
-/
inductive Path.Anchor where

  /--
  Nothing: the path is relative to the working directory, such as `src/Main.lean`.
  -/
  | neutral

  /--
  The POSIX root `/`. Always absolute.
  -/
  | posix

  /--
  A Windows anchor: an optional prefix and whether a root separator follows it, e.g. `C:\`, `C:`,
  `\`, or `\\server\share`.

  `pre` holds the prefix as written, without a trailing separator. Only a bare drive letter leaves
  the anchor relative, so `Internal.isDrivePrefix` is all the structure it needs.

  Build this with `Anchor.ofWindows`, which maps the prefixless, rootless combination — which
  anchors the path to nothing at all — onto `neutral`.
  -/
  | windows (pre : Option ByteArray) (rooted : Bool)
deriving Inhabited, DecidableEq

namespace Path.Anchor

/--
Two anchors are equal when they name the same location. The case of a Windows drive letter is
folded, since Windows treats `c:` and `C:` as the same drive; every other prefix — a UNC share, a
device path, a verbatim path — is compared byte for byte.

This is deliberately coarser than the propositional equality `DecidableEq` decides, which stays byte
identity, so `LawfulBEq Anchor` does not hold: `c:\foo == C:\foo` while the two paths still render
differently. Use `==` to ask whether two paths name the same thing and `=` to ask whether they were
written the same way.
-/
instance : BEq Anchor where
  beq
    | .neutral, .neutral => true
    | .posix, .posix => true
    | .windows p₁ r₁, .windows p₂ r₂ =>
        r₁ == r₂ && p₁.map normalizeDrivePrefix == p₂.map normalizeDrivePrefix
    | _, _ => false

/--
The order agrees with `BEq`, so a drive letter is folded to one case before comparing and the
anchors of `c:\` and `C:\` compare `.eq`. Like `BEq`, that makes it coarser than the propositional
equality `DecidableEq` decides.

Anchors sort by kind — `neutral`, then `posix`, then `windows` — and two Windows anchors by prefix,
then by whether a root follows.
-/
instance : Ord Anchor where
  compare
    | .neutral, .neutral => .eq
    | .posix, .posix => .eq
    | .windows p₁ r₁, .windows p₂ r₂ =>
        compare (p₁.map normalizeDrivePrefix) (p₂.map normalizeDrivePrefix) |>.then (compare r₁ r₂)
    | .neutral, _ => .lt
    | _, .neutral => .gt
    | .posix, _ => .lt
    | _, .posix => .gt

instance : LT Anchor := ltOfOrd
instance : LE Anchor := leOfOrd

/--
An anchor as the term that rebuilds it. A Windows prefix is shown as it is stored, in the case it
was written in, since that is what rendering the path writes back.
-/
instance : Repr Anchor where
  reprPrec a prec :=
    match a with
    | .neutral => "Std.Path.Anchor.neutral"
    | .posix => "Std.Path.Anchor.posix"
    | .windows pre rooted =>
      let prefixRepr := match pre with
        | none => ("none" : Std.Format)
        | some b => "(some " ++ reprBytes b ++ ")"
      Repr.addAppParen ("Std.Path.Anchor.windows " ++ prefixRepr ++ " " ++ repr rooted) prec

/--
Hashes agree with `BEq`: a drive letter is folded to one case before hashing, so `c:` and `C:` land
in the same bucket.
-/
instance : Hashable Anchor where
  hash
    | .neutral => 3
    | .posix => 5
    | .windows pre rooted =>
        mixHash 7 (mixHash (hash rooted) (hash (pre.map normalizeDrivePrefix)))

/--
A Windows anchor with prefix `pre` and a root separator if `rooted`.

A Windows path with neither is anchored to nothing, so it is `neutral`: `a\b` and `a/b` parse to the
same value as the POSIX `a/b`.

The prefix is kept exactly as written, so rendering a parsed path reproduces it byte for byte. The
case of a drive letter is folded by `==` rather than at construction — see the `BEq` instance.
-/
def ofWindows (pre : Option ByteArray) (rooted : Bool) : Anchor :=
  if pre.isNone && !rooted then .neutral else .windows pre rooted

/--
The anchor with the root separator it needs before a segment can follow it.

Every Windows prefix but a bare drive letter names a location in its own right, so a segment under
one is written behind a separator, and reading that separator back is what makes the anchor rooted.
No parse therefore produces a rootless anchor of that shape with segments beneath it; `join` has to
restore the root when it puts segments under a prefix that was standing alone.
-/
def rootedForSegments : Anchor → Anchor
  | .windows (some pre) false => .windows (some pre) (!isDrivePrefix pre)
  | a => a

/--
The Windows prefix this anchor carries, as raw bytes and without a trailing separator, if any.
-/
def prefix? : Anchor → Option ByteArray
  | .windows pre _ => pre
  | _ => none

/--
The drive-letter prefix with its trailing colon (e.g. the bytes of `"C:"`), for the one prefix that
names a drive, in the case it was written in.

Returns `none` on POSIX anchors, on Windows anchors with no prefix, and on prefixes that name no
drive (`\\server\share`, `\\.\COM42`); a verbatim prefix carries its `\\?\` marker, so this returns
`none` even for `\\?\C:\foo`.
-/
def drive? (a : Anchor) : Option ByteArray :=
  a.prefix?.filter isDrivePrefix

/--
The root separator the anchor writes out (`/` or `\`), or `none` if it writes none.

An anchor can start at a root without writing a separator, when its prefix supplies one (e.g.
`\\server\share`); `hasRoot` accounts for that, this does not.
-/
def root? : Anchor → Option ByteArray
  | .posix => some slashBytes
  | .windows _ true => some backslashBytes
  | _ => none

/--
Whether the anchor starts at a root: it writes a root separator, or carries a prefix that supplies
one (any prefix but a bare drive letter, e.g. `\\server\share`).

Weaker than `isAbsolute`: a Windows path can start at a root and still be relative, since `\foo`
names the root of whichever drive is current.
-/
def hasRoot (a : Anchor) : Bool :=
  a.root?.isSome || a.prefix?.any (!isDrivePrefix ·)

/--
Whether the anchor introduces a verbatim path, i.e. carries the `\\?\` marker.

Windows hands a verbatim path to the file system exactly as written, so `.` and `..` name
directories called `.` and `..` below it rather than the current and parent directory, and
`Path.normalize` leaves such a path alone.

Only the literal `\\?\` spelling marks a path verbatim, which is why the parser refuses `?` as a
UNC server name: `//?/x` is a device path that Windows normalizes like any other, and letting it
canonicalize into these bytes would leave a path whose `.` and `..` were read as the current and
parent directory carrying an anchor that says they are ordinary names.
-/
def isVerbatim (a : Anchor) : Bool :=
  a.prefix?.any (startsWithBytes · verbatimMarker)

/--
Whether the anchor names a location that depends on no current directory.

`posix` always does. A Windows anchor needs a prefix, plus either a root of its own or one implied
by that prefix: `C:\foo` and `\\server\share` are absolute, while `C:foo` is relative to the working
directory of drive `C:` and `\foo` to whichever drive is current.
-/
def isAbsolute : Anchor → Bool
  | .neutral => false
  | .posix => true
  | .windows pre rooted => pre.any fun b => rooted || !isDrivePrefix b

end Path.Anchor

/--
A single segment of a file system path: one name, or one `.` or `..`.

Segments carry no platform information — that lives entirely in `Path.Anchor` — so the segment array
of a `Path` means the same thing whichever syntax the path is rendered in.
-/
inductive Path.Segment where

  /--
  The special `.` segment, meaning "current directory".

  Preserved during parsing so that round-trips are lossless; `Path.normalize` removes these.
  -/
  | current

  /--
  The special `..` segment, meaning "parent directory".

  Preserved during parsing; `Path.normalize` resolves these where possible.
  -/
  | parent

  /--
  An ordinary path segment — a file or directory name with no separators.

  The `value` is the raw segment (e.g. the bytes of `"src"` or `"Main.lean"`).
  -/
  | normal (value : ByteArray)
deriving Inhabited, BEq, DecidableEq, Hashable, Ord

namespace Path.Segment

/-!
Segments sort by kind first, so the two special names come ahead of every ordinary one, and
ordinary names sort by their bytes with a proper prefix ahead of what extends it. `.` and `..` are
distinct from the ordinary names spelled the same way, which only a verbatim Windows path produces.
-/

instance : LT Segment := ltOfOrd
instance : LE Segment := leOfOrd

/--
A segment as the term that rebuilds it.
-/
instance : Repr Segment where
  reprPrec s prec :=
    match s with
    | .current => "Std.Path.Segment.current"
    | .parent => "Std.Path.Segment.parent"
    | .normal value => Repr.addAppParen ("Std.Path.Segment.normal " ++ reprBytes value) prec

/--
Classify the raw bytes of one segment, recognizing the two special names.
-/
def ofBytes (b : ByteArray) : Segment :=
  if isDotSegment b then
    if b.size == 1 then .current else .parent
  else
    .normal b

/--
The segment as raw bytes, as it is written in a path.
-/
def toBytes : Segment → ByteArray
  | .current => dotBytes
  | .parent => dotDotBytes
  | .normal value => value

/--
The segment decoded as UTF-8, with every byte that is not part of a well-formed encoding replaced by
`U+FFFD`. Use `toBytes` to get the segment back exactly as it was parsed.
-/
protected def toString (s : Segment) : String :=
  String.fromUTF8Lossy s.toBytes

instance : ToString Segment := ⟨Segment.toString⟩

end Path.Segment
end Std
