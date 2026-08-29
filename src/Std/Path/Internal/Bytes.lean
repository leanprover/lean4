/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Init.Data.ByteArray
public import Init.Data.String
public import Init.Data.Ord.Array
public import Init.Data.Ord.UInt
public import Init.Data.Repr
import Init.Omega

-- Exposed so that `Path.ValidFilename` and `Path.ValidExtension`, which are built from the
-- definitions below, stay decidable by `decide` in modules that import `Std.Path`.
@[expose] public section

/-!
# Path bytes

`Std.Path` stores every component as raw bytes rather than as a `String`: a path is an arbitrary
byte string on POSIX and a possibly ill-formed UTF-16 string on Windows, so on neither platform is
it guaranteed to be valid UTF-8, which every `String` is.

The Windows bytes are WTF-8, the extension of UTF-8 that gives an unpaired surrogate — which a
Windows path may legally hold and a `Char` may not — a three-byte encoding of its own. Both
encodings put the high bit on every byte of a multi-byte sequence, so the ASCII bytes the parsers
give meaning to never occur inside a character.

This module holds the byte-level operations the path API needs. Wherever the API hands a component
back as a `String` it decodes with `String.fromUTF8Lossy`.
-/

namespace Std.Path.Internal

/--
The byte `/`.
-/
def slash : UInt8 := 0x2f

/--
The byte `\`.
-/
def backslash : UInt8 := 0x5c

/--
The byte `.`.
-/
def dot : UInt8 := 0x2e

/--
The byte `:`.
-/
def colon : UInt8 := 0x3a

/--
The byte `?`.
-/
def question : UInt8 := 0x3f

/--
The null byte, which no platform permits in a path.
-/
def nul : UInt8 := 0x00

/--
The bytes of `\\`, which introduce a UNC share or device path.
-/
def uncMarker : ByteArray := ⟨#[backslash, backslash]⟩

/--
The bytes of `\\?\`, which introduce a verbatim path.
-/
def verbatimMarker : ByteArray := ⟨#[backslash, backslash, question, backslash]⟩

/--
The bytes of `UNC`, which mark a verbatim path as naming a network share.
-/
def uncTag : ByteArray := "UNC".toByteArray

/--
The bytes of `.`, the current-directory segment.
-/
def dotBytes : ByteArray := ⟨#[dot]⟩

/--
The bytes of `..`, the parent-directory segment.
-/
def dotDotBytes : ByteArray := ⟨#[dot, dot]⟩

/--
The bytes of `?`, the server name a UNC prefix may not have: canonicalizing it would spell the
verbatim marker.
-/
def questionBytes : ByteArray := ⟨#[question]⟩

/--
The bytes of `/`, the POSIX root separator.
-/
def slashBytes : ByteArray := ⟨#[slash]⟩

/--
The bytes of `\`, the Windows root separator.
-/
def backslashBytes : ByteArray := ⟨#[backslash]⟩

/--
Whether `b` is an ASCII letter, the only drive letters Windows accepts.
-/
def isDriveLetter (b : UInt8) : Bool :=
  ('A'.toUInt8 ≤ b && b ≤ 'Z'.toUInt8) || ('a'.toUInt8 ≤ b && b ≤ 'z'.toUInt8)

/--
Whether `b` is a bare drive-letter prefix such as `C:`.

This is the one Windows prefix that names no location on its own: `C:foo` is relative to the working
directory of drive `C:`, whereas every other prefix (`\\server\share`, `\\.\COM42`, `\\?\x`) is
absolute as it stands.
-/
def isDrivePrefix (b : ByteArray) : Bool :=
  b.size == 2 && isDriveLetter b[0]! && b[1]! == colon

/--
The uppercase form of `b` if it is an ASCII lowercase letter, and `b` itself otherwise.
-/
def toUpperByte (b : UInt8) : UInt8 :=
  if 'a'.toUInt8 ≤ b && b ≤ 'z'.toUInt8 then b - 0x20 else b

/--
A drive-letter prefix with its letter uppercased; any other prefix is returned unchanged.

Used to compare and hash anchors, not to build them: Windows treats `c:` and `C:` as the same drive,
but a parsed path keeps the case it was written in so that rendering it is lossless.
-/
def normalizeDrivePrefix (b : ByteArray) : ByteArray :=
  if isDrivePrefix b then ⟨#[toUpperByte b[0]!, colon]⟩ else b

/--
Whether `b` is a separator in Windows syntax, which accepts both `\` and `/`.
-/
def isWinSep (b : UInt8) : Bool :=
  b == backslash || b == slash

/--
Whether every byte of `b` satisfies `p`.

Written as a scan down the index rather than with `ByteArray.findIdx?` because well-founded
recursion does not reduce in the kernel, and `ValidFilename` has to stay decidable by `decide`.
-/
def allBytes (b : ByteArray) (p : UInt8 → Bool) : Bool :=
  go b.size
where
  go : Nat → Bool
    | 0 => true
    | i + 1 => p b[i]! && go i

/--
Whether `b` is the `.` or `..` segment.
-/
def isDotSegment (b : ByteArray) : Bool :=
  0 < b.size && b.size ≤ 2 && allBytes b (· == dot)

/--
Whether `b` may appear in a file name: not a separator on either platform, and not the null byte,
which no platform permits.
-/
def isFilenameByte (b : UInt8) : Bool :=
  b != slash && b != backslash && b != nul

/--
Whether `b` may appear in a file extension: valid in a file name, and not the `.` that separates one
extension from the next.
-/
def isExtensionByte (b : UInt8) : Bool :=
  isFilenameByte b && b != dot

/--
Whether `b` begins with the byte `x`.
-/
def startsWithByte (b : ByteArray) (x : UInt8) : Bool :=
  if h : 0 < b.size then b[0] == x else false

/--
Whether `b` begins with `pre`.
-/
def startsWithBytes (b pre : ByteArray) : Bool :=
  pre.size ≤ b.size && go pre.size
where
  go : Nat → Bool
    | 0 => true
    | i + 1 => b[i]! == pre[i]! && go i

/--
Whether `b` contains the byte `x` anywhere.
-/
def containsByte (b : ByteArray) (x : UInt8) : Bool :=
  (b.findIdx? (· == x)).isSome

/--
The index of the last occurrence of `x` in `b`.
-/
def revFindByte? (b : ByteArray) (x : UInt8) : Option Nat :=
  go b.size
where
  go : Nat → Option Nat
    | 0 => none
    | i + 1 => if b[i]! == x then some i else go i

/--
Compare two byte strings lexicographically, so that a proper prefix sorts ahead of what extends it.
-/
def compareBytes (a b : ByteArray) : Ordering :=
  compare a.data b.data

/--
The order `Std.Path` puts on the raw bytes of a prefix, a segment, or a file name.

Scoped rather than global: core provides no `Ord ByteArray`, and the one this module needs should
not become the ambient choice for every other user of the type.
-/
scoped instance : Ord ByteArray := ⟨compareBytes⟩

/--
Raw bytes as a term that rebuilds them: a string literal encoded back with `toByteArray` when they
are valid UTF-8, and the underlying byte array otherwise.

Windows bytes are WTF-8, so a path holding an unpaired surrogate takes the second form even though
it is a perfectly ordinary path there. The result is parenthesized where it needs to be, so it can
be dropped straight into argument position.
-/
def reprBytes (b : ByteArray) : Std.Format :=
  match String.fromUTF8? b with
  | some s => repr s ++ ".toByteArray"
  | none => "(ByteArray.mk " ++ repr b.data ++ ")"

/--
Splits the bytes of `b` from `start` onwards at every occurrence of `x`, dropping the separators and
keeping empty pieces. The result always has at least one element.
-/
def splitOnByteFrom (b : ByteArray) (x : UInt8) (start : Nat) : Array ByteArray :=
  go start start #[]
where
  go (from_ i : Nat) (acc : Array ByteArray) : Array ByteArray :=
    if h : i < b.size then
      if b[i] == x then go (i + 1) (i + 1) (acc.push (b.extract from_ i))
      else go from_ (i + 1) acc
    else
      acc.push (b.extract from_ b.size)
  termination_by b.size - i

end Std.Path.Internal
