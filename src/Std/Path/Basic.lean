/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Init.Data.String
public import Init.Data.BEq
import Init.Data.Array.Lemmas
public import Init.Data.Hashable
public import Init.Data.Ord.Array
public import Init.Data.Repr
public import Init.Data.Iterators.Producers
public import Init.System.IO
public import Init.System.Platform
public import Std.Path.Component
public import Std.Path.Internal.Bytes
public import Std.Path.Internal.Parser
public import Std.Path.Internal.Glob
public import Std.Internal.UV.System

public section

/-!
# Path.Basic

The `Path` structure and its full pure/`IO` API. See `Std.Path` for the module overview and quick
start.
-/

namespace Std

/--
A parsed file system path: what it is anchored to, plus the segments below that anchor.

Splitting a path this way keeps every platform-specific decision in the `anchor` — it alone says
whether the path is POSIX or Windows, absolute or relative — and leaves `segments` platform-neutral.
All structural operations (`join`, `parent?`, `normalize`, etc.) work directly on these two fields,
so they are pure and require no OS calls.

Use `Path.ofPosixString?` or `Path.ofWindowsString?` for pure construction from strings when the
platform format is known at compile time.
-/
structure Path where
  private mk ::

  /--
  What the path is anchored to: nothing (`src/Main.lean`), the POSIX root (`/usr`), or a Windows
  prefix and/or root (`C:\Users`, `C:foo`, `\foo`, `\\server\share`).
  -/
  anchor : Path.Anchor

  /--
  The segments below the anchor, in order (e.g. `#[.normal "usr".toByteArray, .current]`).
  -/
  segments : Array Path.Segment
deriving Inhabited, DecidableEq

namespace Path

/--
The segments of `p` with every `.` dropped, i.e. one entry per component of the path.

`.` names the directory it stands in rather than one below it, so `a/./b` and `a/b` have the same
components. `..` is a component of its own and is left in place: a symbolic link makes `a/..` and
`.` different directories, so dropping it would change what the path names.
-/
def components (p : Path) : Array Segment :=
  if p.segments.any (· matches .current) then p.segments.filter (· != .current) else p.segments

/-!
Paths compare by anchor first and then component by component, so an unanchored path comes ahead of
every POSIX one and `a` ahead of `a/b`.

`compare`, `==`, and `hash` all agree with one another, and all three read `components`, so a `.`
is ignored wherever it stands: `a/./b == a/b`, and `Path.empty == .` since neither has a component.
All three also inherit the drive-letter case folding of `Anchor`, so `c:\foo == C:\foo`.

The propositional equality `DecidableEq` decides stays byte identity, and so separates every pair
above; `LawfulBEq Path` therefore does not hold. Use `==` and `compare` to ask whether two paths
name the same thing, and `=` to ask whether they were written the same way.
-/

instance : BEq Path where
  beq p q := p.anchor == q.anchor && p.components == q.components

instance : Hashable Path where
  hash p := mixHash (hash p.anchor) (hash p.components)

instance : Ord Path where
  compare p q := (compare p.anchor q.anchor).then (compare p.components q.components)

instance : LT Path := ltOfOrd
instance : LE Path := leOfOrd

/--
Whether `name` begins with a `.` that marks a dotfile rather than an extension, i.e. one with at
least one more byte after it.
-/
private def hasLeadingDot (name : ByteArray) : Bool :=
  Internal.startsWithByte name Internal.dot && name.size > 1

/--
Where the stem of `name` starts: past a leading dotfile `.`, which introduces no extension.
-/
private def stemStart (name : ByteArray) : Nat :=
  if hasLeadingDot name then 1 else 0

/--
Where the stem of `name` ends: at the first `.` that introduces an extension, or at the end of the
name when there is none.
-/
private def stemEnd (name : ByteArray) : Nat :=
  (name.findIdx? (· == Internal.dot) (start := stemStart name)).getD name.size

/--
Where the `.` that introduces the last extension of `name` sits, if it has one.

Index `0` does not count: a name that is nothing but a leading dot and a stem, like `.gitignore`,
has no extension.
-/
private def extensionDot? (name : ByteArray) : Option Nat :=
  (Internal.revFindByte? name Internal.dot).filter (· != 0)

/--
A valid file name: non-empty, not `.` or `..`, and contains no separator (`/`, `\`) or null byte.
Satisfied by `by decide` for the UTF-8 encoding of a string literal.
-/
abbrev ValidFilename (x : ByteArray) : Prop :=
  ¬x.isEmpty ∧ ¬Internal.isDotSegment x ∧ Internal.allBytes x Internal.isFilenameByte

/--
A valid file extension: non-empty and contains no separator (`/`, `\`), dot (`.`), or null byte.
Pass without the leading `.` — the dot is added by the caller. Satisfied by `by decide` for the
UTF-8 encoding of a string literal.
-/
abbrev ValidExtension (x : ByteArray) : Prop :=
  ¬x.isEmpty ∧ Internal.allBytes x Internal.isExtensionByte

/--
A validated file name: a byte string known, by construction, to satisfy `ValidFilename`.
-/
structure Filename where
  /--
  The underlying file name, as raw bytes.
  -/
  value : ByteArray

  /--
  Proof that `value` satisfies `ValidFilename`.

  The default proof scans `value` a byte at a time, so a literal of more than about a hundred bytes
  needs a raised `maxRecDepth` to elaborate.
  -/
  proof : ValidFilename value := by decide

namespace Filename

instance : Inhabited Filename := ⟨⟨"_".toByteArray, by decide⟩⟩

-- The equality instances are written out rather than derived: the `proof` field's type depends on
-- `value`, so `deriving` would need `LawfulBEq ByteArray`, which core does not provide.
instance : BEq Filename := ⟨(·.value == ·.value)⟩

instance : Hashable Filename := ⟨(hash ·.value)⟩

instance : DecidableEq Filename := fun ⟨a, _⟩ ⟨b, _⟩ =>
  if h : a = b then isTrue (by subst h; rfl)
  else isFalse (h <| congrArg Filename.value ·)

/--
File names sort by their bytes, with a proper prefix ahead of what extends it.
-/
instance : Ord Filename := ⟨(Internal.compareBytes ·.value ·.value)⟩

instance : LT Filename := ltOfOrd
instance : LE Filename := leOfOrd

/--
A file name as the term that rebuilds it, which is `ofString!` unless its bytes are not valid UTF-8
and no string literal can hold them.
-/
instance : Repr Filename where
  reprPrec f prec :=
    match String.fromUTF8? f.value with
    | some s => Repr.addAppParen ("Std.Path.Filename.ofString! " ++ repr s) prec
    | none => Repr.addAppParen ("Std.Path.Filename.mk " ++ Internal.reprBytes f.value) prec



/--
Validate `b` as a `Filename`, returning `none` if it fails `ValidFilename`.
-/
def ofBytes? (b : ByteArray) : Option Filename :=
  if h : ValidFilename b then some ⟨b, h⟩ else none

/--
Validate the UTF-8 encoding of `s` as a `Filename`, returning `none` if it fails `ValidFilename`.
-/
def ofString? (s : String) : Option Filename :=
  ofBytes? s.toByteArray

/--
Validate the UTF-8 encoding of `s` as a `Filename`, panicking with an error message if it fails
`ValidFilename`.

For a literal written in the source. A panic returns the `Inhabited` default rather than stopping
the program, so on rejected input this yields the file name `_` and the caller goes on to read or
write the wrong file: `dir / Filename.ofString! "../../etc/passwd"` is `dir/_`. Validate anything
that came from outside the source with `ofString?` and handle the `none`.
-/
def ofString! (s : String) : Filename :=
  match ofString? s with
  | some name => name
  | none => panic! s!"invalid file name: {s.quote}"

/--
The file name decoded as UTF-8, with every byte that is not part of a well-formed encoding replaced
by `U+FFFD`. Use `value` to get the name back exactly as it was parsed.
-/
protected def toString (f : Filename) : String :=
  String.fromUTF8Lossy f.value

instance : Coe Filename ByteArray := ⟨Filename.value⟩

instance : ToString Filename := ⟨Filename.toString⟩

/--
True if the file name starts with `.` (a Unix-style hidden file, e.g. `.gitignore`).
-/
def isHidden (f : Filename) : Bool :=
  Internal.startsWithByte f.value Internal.dot

end Filename

/--
A validated file extension (without the leading `.`): a byte string known, by construction, to
satisfy `ValidExtension`.
-/
structure Extension where
  /--
  The underlying extension, without the leading `.`, as raw bytes.
  -/
  value : ByteArray

  /--
  Proof that `value` satisfies `ValidExtension`.

  The default proof scans `value` a byte at a time, so a literal of more than about a hundred bytes
  needs a raised `maxRecDepth` to elaborate.
  -/
  proof : ValidExtension value := by decide

namespace Extension

instance : Inhabited Extension := ⟨⟨"_".toByteArray, by decide⟩⟩
instance : BEq Extension := ⟨(·.value == ·.value)⟩
instance : Hashable Extension := ⟨(hash ·.value)⟩
instance : DecidableEq Extension := fun ⟨a, _⟩ ⟨b, _⟩ =>
  if h : a = b then isTrue (by subst h; rfl)
  else isFalse (h <| congrArg Extension.value ·)

/--
Extensions sort by their bytes, with a proper prefix ahead of what extends it.
-/
instance : Ord Extension := ⟨(Internal.compareBytes ·.value ·.value)⟩

instance : LT Extension := ltOfOrd
instance : LE Extension := leOfOrd

/--
An extension as the term that rebuilds it. See `Repr Filename` for the non-UTF-8 case.
-/
instance : Repr Extension where
  reprPrec e prec :=
    match String.fromUTF8? e.value with
    | some s => Repr.addAppParen ("Std.Path.Extension.ofString! " ++ repr s) prec
    | none => Repr.addAppParen ("Std.Path.Extension.mk " ++ Internal.reprBytes e.value) prec



/--
Validate `b` as an `Extension`, returning `none` if it fails `ValidExtension`.
-/
def ofBytes? (b : ByteArray) : Option Extension :=
  if h : ValidExtension b then some ⟨b, h⟩ else none

/--
Validate the UTF-8 encoding of `s` as an `Extension`, returning `none` if it fails
`ValidExtension`.
-/
def ofString? (s : String) : Option Extension :=
  ofBytes? s.toByteArray

/--
Validate the UTF-8 encoding of `s` as an `Extension`, panicking with an error message if it fails
`ValidExtension`.

For a literal written in the source. A panic returns the `Inhabited` default rather than stopping
the program, so on rejected input this yields the extension `_` and the caller goes on to name the
wrong file. Validate anything that came from outside the source with `ofString?`.
-/
def ofString! (s : String) : Extension :=
  match ofString? s with
  | some ext => ext
  | none => panic! s!"invalid extension: {s.quote}"

/--
The extension decoded as UTF-8, with every byte that is not part of a well-formed encoding replaced
by `U+FFFD`. Use `value` to get the extension back exactly as it was parsed.
-/
protected def toString (e : Extension) : String :=
  String.fromUTF8Lossy e.value

instance : Coe Extension ByteArray := ⟨Extension.value⟩

instance : ToString Extension := ⟨Extension.toString⟩

end Extension

/--
The empty path: no anchor and no segments. Joining any path with `empty` yields that path
unchanged.
-/
def empty : Path := { anchor := .neutral, segments := #[] }

/--
A single-segment, unanchored path built from the validated `name`.
-/
def ofFilename (name : Filename) : Path :=
  { anchor := .neutral, segments := #[.normal name.value] }

/--
True if `p` names the working directory itself: it is unanchored and has no component, so every
segment it has is a `.`.

Holds for `"."`, for `"./."`, and for `Path.empty`, which all render as `.`. This is the one
relative path with no parent.
-/
def isCurrentDir (p : Path) : Bool :=
  p.anchor matches .neutral && p.components.isEmpty

/--
True if `p` has no anchor and no segments at all.

This is a question about the representation, not about what `p` names: `"."` also names the working
directory and `Path.empty == ofPosixString! "."`, but it holds a `.` segment and so is not `isEmpty`.
Ask `isCurrentDir` for the location.
-/
@[inline]
def isEmpty (p : Path) : Bool :=
  p.anchor matches .neutral && p.segments.isEmpty

/--
The Windows prefix of `p` as raw bytes and without a trailing separator, if it has one.

Returns `none` on POSIX paths and on Windows paths with no prefix (e.g. `foo\bar` or `\foo`).
-/
@[inline]
def windowsPrefix? (p : Path) : Option ByteArray :=
  p.anchor.prefix?

/--
The drive-letter prefix as raw bytes (e.g. the bytes of `"C:"`), in the case it was written in.
`==` folds that case, so `c:` and `C:` compare equal without being the same bytes.

Returns `none` on POSIX paths, on relative Windows paths that have no drive letter, and on prefixes
that name no drive (e.g. `\\server\share`) — use `windowsPrefix?` to see those.
-/
@[inline]
def drive? (p : Path) : Option ByteArray :=
  p.anchor.drive?

/--
The root separator (`/` or `\`) if the path has one written out; `none` otherwise.

A path can start at a root without one of its own, when its prefix supplies it (e.g.
`\\server\share`); `hasRoot` accounts for that, this does not.
-/
@[inline]
def root? (p : Path) : Option ByteArray :=
  p.anchor.root?

/--
True if `p` starts at a root: it has a root of its own, or a prefix that supplies one (any prefix
but a bare drive letter, e.g. `\\server\share`).

Weaker than `isAbsolute`: a Windows path can start at a root and still be relative, since `\foo`
names the root of whichever drive is current.
-/
@[inline]
def hasRoot (p : Path) : Bool :=
  p.anchor.hasRoot

/--
True if `p` is a verbatim Windows path, i.e. one carrying the `\\?\` marker.

Windows hands such a path to the file system as written, so `.` and `..` name ordinary directories
below it and `normalize` leaves it alone.
-/
@[inline]
def isVerbatim (p : Path) : Bool :=
  p.anchor.isVerbatim

/--
True if `p` names a location that depends on no current directory.

A POSIX path is absolute exactly when it has a root. A Windows path needs both a prefix and a root:
`C:\foo` and `\\server\share` are absolute, while `C:foo` is relative to the working directory of
drive `C:` and `\foo` to whichever drive is current.

The verdict is fixed by the syntax `p` was parsed with, not by the host platform.
-/
@[inline]
def isAbsolute (p : Path) : Bool :=
  p.anchor.isAbsolute

/--
True if `p` names a location only in relation to a current directory.

A POSIX path is relative exactly when it has no root. A Windows path is relative when it lacks a
prefix, a root, or both, and what it is relative to differs in each case: `foo\bar` resolves against
the working directory, `C:foo` against the working directory of drive `C:`, and `\foo` against the
root of whichever drive is current. That last one has a root, so `hasRoot` says nothing about
whether a path is relative.
-/
@[inline]
def isRelative (p : Path) : Bool :=
  !p.isAbsolute

/--
Append `segs` to `acc` as a verbatim prefix requires: `.` drops out and `..` pops the name before
it, or vanishes at the root.

Windows hands a `\\?\` path to the file system as written, so a `.` or `..` left in one names a
directory that must exist rather than moving anywhere. Segments arriving from a path parsed under
ordinary rules mean what they say, so they have to be resolved here, at the point they cross into
the verbatim path — afterwards nothing can, since `normalize` leaves verbatim paths alone.
-/
private def pushVerbatim (acc segs : Array Path.Segment) : Array Path.Segment :=
  segs.foldl (init := acc) fun acc s =>
    match s with
    | .current => acc
    | .parent => if acc.back? matches some (.normal _) then acc.pop else acc
    | .normal _ => acc.push s

/--
Append `other` to `p`.

`other` replaces `p` entirely if it is absolute or brings a Windows prefix of its own. If it is
rooted but has no prefix (a Windows `\foo`, relative to the current drive), it keeps only `p`'s
prefix: `C:\a` joined with `\b` is `C:\b`.

Joining onto a verbatim path resolves `.` and `..` in `other` as it goes, since the result would
otherwise name nothing on Windows.

A prefix that was standing alone gains the root separator a segment under it has to be written
behind, so `\\server\share` joined with `a` is `\\server\share\a`; see
`Anchor.rootedForSegments`.
-/
def join (p p₂ : Path) : Path :=
  match p₂.anchor with
  | .neutral =>
    if p₂.segments.isEmpty then p
    else
      -- A prefix that was standing alone has no root written after it, and putting a segment under
      -- it needs one; see `Anchor.rootedForSegments`.
      let anchor := p.anchor.rootedForSegments
      if p.isVerbatim then { anchor, segments := pushVerbatim p.segments p₂.segments }
      else { anchor, segments := p.segments ++ p₂.segments }
  | .windows none rooted =>
    if p.isVerbatim then
      { anchor := .ofWindows p.windowsPrefix? rooted, segments := pushVerbatim #[] p₂.segments }
    else { p₂ with anchor := .ofWindows p.windowsPrefix? rooted }
  | _ => p₂

/--
The anchor rendered as raw bytes: prefix concatenated with root (e.g. `"C:\\"`,
`"\\\\server\\share\\"`, `"/"`, or `""` for a neutral path).
-/
def anchorBytes (p : Path) : ByteArray :=
  p.windowsPrefix?.getD .empty ++ p.root?.getD .empty

/--
Resolve `.` segments and eliminate `..` segments syntactically.

`..` above a root is silently dropped (no error). A verbatim Windows path is returned unchanged,
since Windows hands one to the file system as written and `.` and `..` name ordinary directories
below it. No file system access is performed; symlinks are not resolved.

An unanchored path that cancels to nothing, such as `a/..`, normalizes to `Path.empty`, which every
renderer writes as `.`.

Because they are not, the result can name a different file than `p` does: `a/..` is only `.` when
`a` is a real directory, and `link/..` leads to whatever holds the link's target. Normalizing before
a comparison therefore does not make the comparison a statement about the file system — use
`resolveWithin` where that is what is needed.
-/
def normalize (p : Path) : Path :=
  if p.isVerbatim then p else

  -- Nothing sits above a root, so a ".." that reaches one is dropped; under any other anchor
  -- (including the drive-relative `C:`) a leading ".." is meaningful and is kept.
  let keepsLeadingParent := !p.hasRoot

  let acc := p.segments.foldl (init := #[]) fun acc s =>
    match s with
    | .current => acc
    | .parent =>
      match acc.back? with
      | some (.normal _) => acc.pop
      | some .parent => acc.push .parent
      | _ => if keepsLeadingParent then acc.push .parent else acc
    | other => acc.push other

  -- An unanchored path that normalizes to nothing keeps no segment standing in for the working
  -- directory: `.` is what such a path renders as, and holding a `.current` segment instead would
  -- make `normalize` produce a path that `startsWith` and `relativeTo?` read as one directory deep.
  { p with segments := acc }

/-!
The operations below ask what a path names, so they read `components` rather than `segments`: a
trailing `.` goes with the component it stands on, and `"a/b/."` and `"a/b"` have the same file name
and the same parent. `..` is a component, since a symbolic link makes `"a/b/.."` and `"a"` different
entries: a path ending in `..` has no file name, and its parent is what stands before the `..`.
-/

/--
The index of the last segment that is not `.`, i.e. of the last component.
-/
private def lastNameIdx? (segs : Array Segment) : Nat → Option Nat
  | 0 => none
  | n + 1 => if segs[n]? matches some .current then lastNameIdx? segs n else some n

private theorem lt_of_lastNameIdx?_eq {segs : Array Segment} {n i : Nat}
    (h : lastNameIdx? segs n = some i) : i < n := by
  induction n with
  | zero => simp [lastNameIdx?] at h
  | succ n ih =>
    rw [lastNameIdx?] at h
    split at h
    · exact Nat.lt_succ_of_lt (ih h)
    · injection h with h; omega

/--
How many segments `p` has once a trailing `.` is dropped, i.e. its number of components. `0` when
`p` has no component at all (a root, the empty path, or only `.` segments).
-/
private def nameEnd (p : Path) : Nat :=
  match lastNameIdx? p.segments p.segments.size with
  | some i => i + 1
  | none => 0

private theorem nameEnd_le (p : Path) : p.nameEnd ≤ p.segments.size := by
  rw [nameEnd]
  split
  · rename_i i h
    exact lt_of_lastNameIdx?_eq h
  · exact Nat.zero_le _

/--
The last component, i.e. the last segment that is not `.`.
-/
private def lastComponent? (p : Path) : Option Segment :=
  match lastNameIdx? p.segments p.segments.size with
  | some i => p.segments[i]?
  | none => none

/--
Drop the last component, returning the parent directory path.

A trailing `.` goes with the component it stands on, since `"a/b/."` names the same entry as
`"a/b"`, so the parent of both is `"a"`. A trailing `..` is a component of its own and is dropped
rather than resolved: the parent of `"a/b/.."` is `"a/b"`.

Returns `none` for root paths, empty paths, and `"."`. For any other unanchored path whose parent
would be empty (e.g. `"a"`), returns `some "."`. Only the dropped component is affected: the path is
not normalized, so an interior `.` is left as written and the parent of `"a/./b"` is `"a/."`.
-/
def parent? (path : Path) : Option Path :=
  match path.nameEnd, path.anchor with
  | 0, _ => none
  | 1, .neutral => some { path with segments := #[.current] }
  | n + 1, _ => some { path with segments := path.segments.extract 0 n }

/--
True if `p` starts at a root and has no component below it (i.e. only a root, with an optional
drive prefix). Examples: `"/"`, `"C:\\"`, `"\\"`, `"/."`.

Uses `hasRoot`, not `isAbsolute`, so the drive-relative `"\\"` counts.
-/
def isRoot (p : Path) : Bool :=
  p.hasRoot && p.components.isEmpty

/--
The raw bytes of the last component when it is an ordinary name.

Returns `none` when the path ends in `..` and when it has no name component at all (a root, the
empty path, or only `.` segments). Unlike `filename?` this does not validate the name against
`ValidFilename`, so it also covers the names only a verbatim Windows path can produce, where `/` is
an ordinary byte.
-/
private def lastName? (p : Path) : Option ByteArray :=
  match p.lastComponent? with
  | some (.normal v) => some v
  | _ => none

/--
The last `normal` segment (i.e. the file or directory name), validated as a `Filename`.

Returns `none` when the path ends in `..` and when it has no name segment at all (a root, the empty
path, or only `.` segments). A trailing `.` is ignored, since `"a/."` names the same entry as `"a"`.
It is also `none` for a name no `Filename` can carry — only a verbatim Windows path
produces one, since `\\?\a/b` names a single volume `a/b` rather than an `a` holding a `b`.

The result round-trips directly into `setFilename`/`HDiv` with no re-validation needed.
-/
def filename? (p : Path) : Option Filename :=
  p.lastName?.bind Filename.ofBytes?

/--
The filename without the last extension, as raw bytes.

Returns `none` when the last component is not an ordinary name (see `lastName?`).

Examples:
- `(ofPosixString! "src/Main.lean").fileStem? = some "Main".toByteArray`
- `(ofPosixString! "archive.tar.gz").fileStem? = some "archive.tar".toByteArray`
-/
def fileStem? (p : Path) : Option ByteArray := do
  let name ← p.lastName?
  return (extensionDot? name).elim name (name.extract 0 ·)

/--
The filename stem before the first extension (i.e. before the first `.` after any leading dot), as
raw bytes.

Returns `none` when the last component is not an ordinary name (see `lastName?`).

Examples:
- `(ofPosixString! "foo.tar.gz").filePrefix? = some "foo".toByteArray`
- `(ofPosixString! ".hidden").filePrefix? = some ".hidden".toByteArray`
- `(ofPosixString! ".hidden.tar.gz").filePrefix? = some ".hidden".toByteArray`
- `(ofPosixString! "Makefile").filePrefix? = some "Makefile".toByteArray`
-/
def filePrefix? (p : Path) : Option ByteArray := do
  let name ← p.lastName?
  return name.extract 0 (stemEnd name)

/--
The last file extension, validated as an `Extension` (without the leading `.`).

Returns `none` when the filename has no extension (including a trailing-dot name like `"a."`, whose
"extension" would be empty and so isn't a valid `Extension`) and when the last segment is not an
ordinary name. The result round-trips directly into `withExtension`/`addExtension` with no
re-validation needed.

Examples:
- `(ofPosixString! "Main.lean").extension? = some (.mk "lean".toByteArray)`
- `(ofPosixString! "archive.tar.gz").extension? = some (.mk "gz".toByteArray)`
- `(ofPosixString! "Makefile").extension? = none`
-/
def extension? (p : Path) : Option Extension := do
  let name ← p.lastName?
  let dot ← extensionDot? name
  Extension.ofBytes? (name.extract (dot + 1) name.size)

/--
True if the file name has at least one extension.
-/
def hasExtension (p : Path) : Bool :=
  p.extension?.isSome

/--
True if the last segment is an ordinary name and it is hidden (starts with `.`, e.g.
`.gitignore`).
-/
def isHidden (p : Path) : Bool :=
  p.lastName?.any (Internal.startsWithByte · Internal.dot)

/--
Unchecked primitive: replace the last `normal` segment with `fname`, leaving the rest unchanged.

If `p` has no `normal` file name (i.e. it is empty, a root, or ends in `..`), `p` is returned
unchanged, as it is for an `fname` that is empty or a dot segment. A trailing `.` is dropped along
with the name it stood on, so `"a/."` becomes `"b"` rather than `"b/."`. `fname` is otherwise not
validated — it must already be known to satisfy `ValidFilename` (e.g. because it was built from the
pieces of an existing, validated file name); public callers should use `setFilename` instead.
-/
private def setLastSegment (p : Path) (fname : ByteArray) : Path :=
  match lastNameIdx? p.segments p.segments.size with
  | some i =>
    if p.segments[i]? matches some (.normal _) then
      -- `.` and `..` are `ValidFilename` violations that the callers below can reach by truncation
      -- (`"..a"` minus its extension is `"."`). Storing one would make a `.normal` segment that
      -- renders as a special one, so the path would re-parse as a different path.
      if Internal.isDotSegment fname || fname.isEmpty then p
      else { p with segments := (p.segments.extract 0 i).push (.normal fname) }
    else p
  | none => p

/--
Replace the last path segment with `name`.

If `p` has no `normal` file name (i.e. it is empty, a root, or ends in `..`), `p` is returned
unchanged. A trailing `.` is replaced along with the name it stood on, so `"a/."` becomes `"b"`. For
a compile-time-known name, `p.setFilename (.mk "foo.txt".toByteArray)` just works; for a runtime
`String`, validate it first with `Filename.ofString?`.
-/
def setFilename (p : Path) (name : Filename) : Path :=
  p.setLastSegment name.value

/--
Replace the last file extension with `ext` (without leading `.`).

If the filename currently has no extension, `ext` is appended. If the path has no file name (e.g. it
is a root or empty), `p` is returned unchanged. Use `removeExtension` to strip an extension instead.
For a compile-time-known extension, `p.withExtension (.mk "gz".toByteArray)` just works; for a runtime
`String`, validate it first with `Extension.ofString?`.
-/
def withExtension (p : Path) (ext : Extension) : Path :=
  match p.fileStem? with
  | none => p
  | some stem => p.setLastSegment (stem ++ Internal.dotBytes ++ ext.value)

/--
Append `ext` (without leading `.`) to the file name, without removing any existing extensions.
-/
def addExtension (p : Path) (ext : Extension) : Path :=
  match p.lastName? with
  | none => p
  | some name => p.setLastSegment (name ++ Internal.dotBytes ++ ext.value)

/--
Remove the last file extension from the file name, keeping any earlier extensions.

If the file name carries no `.` past its first byte, or the path has no file name (e.g. it is a root
or empty), `p` is returned unchanged. So is a name that would be left as `.` or `..`, since those
name a directory rather than a file: `"..a"` and `"..."` keep their extensions.

The `.` need not introduce an `Extension`: a trailing dot is stripped, so `"a."` becomes `"a"` even
though `hasExtension` is `false` for it, an empty extension being one no `Extension` can hold.
-/
def removeExtension (p : Path) : Path :=
  match p.lastName? with
  | none => p
  | some name => (extensionDot? name).elim p fun dot => p.setLastSegment (name.extract 0 dot)

/--
All file extensions of the last segment, in order, without leading `.`, as raw bytes.

Examples:
- `(ofPosixString! "archive.tar.gz").suffixes = #["tar".toByteArray, "gz".toByteArray]`
- `(ofPosixString! "Makefile").suffixes = #[]`
-/
def suffixes (p : Path) : Array ByteArray :=
  match p.lastName? with
  | none => #[]
  | some name =>
    let firstDot := stemEnd name
    if firstDot == name.size then #[]
    else Internal.splitOnByteFrom name Internal.dot (firstDot + 1)

/--
Replace the stem (all of the filename before the extensions) with `stem`, keeping every existing
extension intact.

Complement of `withExtension`: `p.withStem s |>.suffixes = p.suffixes`. For a compile-time-known
stem, `p.withStem (.mk "backup".toByteArray)` just works; for a runtime `String`, validate it first with
`Filename.ofString?`.
-/
def withStem (p : Path) (stem : Filename) : Path :=
  match p.lastName? with
  | none => p
  | some name => p.setLastSegment (stem.value ++ name.extract (stemEnd name) name.size)

/--
A measure that `parent?` strictly decreases, which is what makes `parents` terminate.

`segments.size` alone will not do, since `"a"` and its parent `"."` both have one segment. The low
bit separates them, because `"."` is exactly the one-segment path that has no parent.
-/
private def parentMeasure (p : Path) : Nat :=
  2 * p.segments.size + (if p.parent?.isSome then 1 else 0)

private theorem parentMeasure_lt_of_parent_eq {p q : Path} (h : p.parent? = some q) :
    parentMeasure q < parentMeasure p := by
  have hp : p.parent?.isSome := by simp [h]
  have hle := nameEnd_le p
  rw [parent?] at h
  split at h
  · contradiction
  · rename_i hend _
    injection h with h
    subst h
    -- The parent is `"."`, the one path with no parent of its own.
    have hq : (Path.mk p.anchor #[Segment.current]).parent? = none := by
      simp [parent?, nameEnd, lastNameIdx?]
    have h1 : parentMeasure (Path.mk p.anchor #[Segment.current]) = 2 := by
      simp [parentMeasure, hq]
    have h2 : parentMeasure p = 2 * p.segments.size + 1 := by simp [parentMeasure, hp]
    omega
  · rename_i _ _ n hend _
    injection h with h
    subst h
    have hn : (p.segments.extract 0 n).size = n := by
      rw [Array.size_extract]; omega
    have h1 : parentMeasure { p with segments := p.segments.extract 0 n } ≤ 2 * n + 1 := by
      simp only [parentMeasure, hn]
      split <;> omega
    have h2 : parentMeasure p = 2 * p.segments.size + 1 := by simp [parentMeasure, hp]
    omega

/--
Implementation detail: iterator state for `Path.parents`.
-/
structure ParentsIterator where

  /--
  The path currently being examined.
  -/
  current : Path

namespace ParentsIterator

instance instIterator [Pure m] : Iterator ParentsIterator m Path where
  IsPlausibleStep
    | it, .yield it' out =>
        it.internalState.current.parent? = some out ∧ it'.internalState.current = out
    | _, .skip _ => False
    | _, .done => True
  step it :=
    pure (match it with
    | ⟨⟨cur⟩⟩ =>
      match hcur : cur.parent? with
      | none => .deflate ⟨.done, trivial⟩
      | some par => .deflate ⟨.yield ⟨⟨par⟩⟩ par, hcur, rfl⟩)

instance [Monad n] : IteratorLoop ParentsIterator Id n := .defaultImplementation

private def finitenessRelation [Pure m] : Iterators.FinitenessRelation ParentsIterator m where
  Rel := InvImage (· < ·) (parentMeasure ·.internalState.current)
  wf := InvImage.wf _ Nat.lt_wfRel.wf
  subrelation {it it'} h := by
    simp_wf
    obtain ⟨step, hsucc, hstep⟩ := h
    cases step with
    | yield it'' out =>
      simp only [IterStep.successor, Option.some.injEq] at hsucc
      subst hsucc
      obtain ⟨hpar, hcur⟩ := hstep
      rw [hcur]
      exact parentMeasure_lt_of_parent_eq hpar
    | skip it'' => exact hstep.elim
    | done => simp [IterStep.successor] at hsucc

instance instFinite [Pure m] : Iterators.Finite ParentsIterator m :=
  .of_finitenessRelation finitenessRelation

end ParentsIterator

/--
All ancestors of `p`, from the immediate parent up to (and including) the root, in order.

For `ofPosixString! "/a/b/c"` this yields an iterator over the paths
`["/a/b", "/a", "/"]`.
-/
def parents (p : Path) : Iter (α := ParentsIterator) Path :=
  (IterM.mk (m := Id) (β := Path) ⟨p⟩).toIter

/--
True if `p` and `prefx` share an anchor and `prefx`'s components are a prefix of `p`'s
(component-wise, not as a raw byte prefix).

`ofPosixString! "/usr/local"` starts with `ofPosixString! "/usr"` but not with `ofPosixString! "/us"`,
and no absolute path starts with a relative one.

A `..` is compared as written rather than resolved, so `"/usr/../etc".startsWith "/usr"` is `true`.
A `.` is not a component and so does not count either way. This is a syntactic test, not a
containment check — use `isUnder`, or `resolveWithin` when the answer has to hold on the file
system.
-/
def startsWith (p prefx : Path) : Bool :=
  p.anchor == prefx.anchor && prefx.components.isPrefixOf p.components

/--
True if `p` ends with `suffix` (component-wise).

Matching is on whole components from the back, so `"/usr/bin".endsWith "bin"` and
`"/usr/bin".endsWith "usr/bin"` are both `true`, but `"/usr/bin".endsWith "sr/bin"` is `false`. A
`.` is not a component, so `"/usr/bin/."` ends with `"bin"` too. An anchored `suffix` must match `p`
outright, anchor included: `"/usr/bin".endsWith "/usr/bin"` is `true` while `"/usr/bin".endsWith
"/bin"` is `false`.
-/
def endsWith (p suffix : Path) : Bool :=
  let pc := p.components
  let sc := suffix.components
  if suffix.anchor matches .neutral then
    sc.size ≤ pc.size && pc.extract (pc.size - sc.size) == sc
  else
    p.anchor == suffix.anchor && pc == sc

/--
Remove `prefx` from the beginning of `p` (component-wise), leaving an unanchored path.

Returns `none` if `p` does not start with `prefx`. The result holds the components that remain, so
any `.` in `p` is dropped along the way and a `p` that is all prefix yields `Path.empty`.
-/
def dropPrefix? (p prefx : Path) : Option Path :=
  if p.startsWith prefx then
    some { anchor := .neutral, segments := p.components.extract prefx.components.size }
  else
    none

/--
True if `p` names `base` itself or something below it, after resolving `.` and `..` in both.

`"uploads/../etc/passwd".isUnder "uploads"` is `false`, where `startsWith` would say `true`.

This is a lexical test, and `..` is only lexically sound when no segment above it is a symbolic
link: with `uploads/link` pointing at `/`, `"uploads/link/../etc".isUnder "uploads"` is `true` while
the file the OS opens is `/etc`. Names are also compared byte for byte, so it answers `false` for
`"/ETC"` under `"/etc"` on the case-insensitive file systems Windows and macOS default to. Use it
to reject obviously-escaping input; use `resolveWithin` for a decision that has to hold against the
file system.
-/
def isUnder (p base : Path) : Bool :=
  p.normalize.startsWith base.normalize

/--
How many leading segments `a` and `b` have in common.
-/
private def commonPrefixLength (a b : Array Segment) : Nat :=
  go 0
where
  go (i : Nat) : Nat :=
    if ha : i < a.size then
      if hb : i < b.size then
        if a[i] == b[i] then go (i + 1) else i
      else i
    else i
  termination_by a.size - i

/--
Compute an unanchored path from `base` to `target` using `..` segments to walk up out of `base`, so
that `(base.join r).normalize = target.normalize` where `r` is the returned path.

The result is purely syntactic: it does not consult the file system and treats every leading
segment of `base` as a directory to ascend from (so `base` should usually be `normalize`d first if
it contains `.` or `..`).

Returns `none` if `base` and `target` have different anchors (e.g. different drive letters or
network shares on Windows, or one absolute and one relative), and if a `..` in `base` outlives the
part `target` shares with it: nothing names the directory such a `..` ascended out of, so no
relative path leads back into it.
-/
def relativeTo? (base target : Path) : Option Path :=
  if base.anchor != target.anchor then
    none
  else
    let b := base.components
    let t := target.components
    let n := commonPrefixLength b t
    if (b.extract n).any (· == Segment.parent) then
      none
    else
      let ups := Array.replicate (b.size - n) Segment.parent
      some { anchor := .neutral, segments := ups ++ t.extract n }

/--
`b`, or `"."` if `b` is empty.

Every renderer ends in this, because the empty byte string is not a path: no parser accepts it, so
returning it would produce bytes that cannot be read back. The paths that reach it — `Path.empty`,
and a Windows-prefixed anchor whose prefix the POSIX renderer has to drop — name no location of
their own, which is what `.` says.
-/
private def nonEmptyRender (b : ByteArray) : ByteArray :=
  if b.isEmpty then Internal.dotBytes else b

/--
Append `segments` to `init`, writing `sep` between consecutive segments and ahead of the first one
if `leadingSep`.
-/
private def joinSegments (init : ByteArray) (leadingSep : Bool) (sep : UInt8)
    (segments : Array Segment) : ByteArray :=
  match segments[0]? with
  | none => init
  | some first =>
    let head := (if leadingSep then init.push sep else init) ++ first.toBytes
    segments.foldl (init := head) (start := 1) fun acc s => acc.push sep ++ s.toBytes

/--
Render `p` to a POSIX-style byte string using `/` as the separator. Pure.

The segments are joined with `/`, behind a leading `/` if the anchor writes a root. A path
consisting of just a root renders as `"/"`.

A Windows prefix has no POSIX spelling and is dropped, so a path carrying one renders as a path
naming somewhere else: `C:\Windows` renders as `/Windows` and `\\server\share` renders as `.`. Use
`toPosixBytes?`, which refuses a render that changes the path, unless the result is only for
display.
-/
def toPosixBytes (p : Path) : ByteArray :=
  let init := if p.root?.isSome then Internal.slashBytes else .empty
  -- No path denotes the empty byte string, and no parser accepts it, so an anchor that writes
  -- nothing and no segments has to come out as the one path that names no location: `.`.
  nonEmptyRender <| joinSegments init false Internal.slash p.segments

/--
Render `p` to a Windows-style byte string using `\\` as the separator. Pure.

A prefix is written without a trailing separator, so `\\server\share` and `\\server\share\` stay
distinct. The segments are joined with `\\`.

Windows syntax that a segment merely contains is not escaped, so a path carrying one renders as a
path naming somewhere else: the POSIX file name `a\b` splits in two, and the POSIX relative `C:/a`
becomes the absolute `C:\a`. Use `toWindowsBytes?`, which refuses a render that changes the path,
unless the result is only for display.
-/
def toWindowsBytes (p : Path) : ByteArray :=
  let (init, leadingSep) :=
    match p.anchor with
    | .neutral => (ByteArray.empty, false)
    | .posix => (Internal.backslashBytes, false)
    | .windows pre rooted =>
      let pfx := pre.getD .empty
      if rooted then
        (pfx ++ Internal.backslashBytes, false)
      else
        -- Only a drive letter may be followed directly by a segment (`C:foo`); every other prefix
        -- is a location in its own right, so a segment under it needs a separator.
        (pfx, pre.any (!Internal.isDrivePrefix ·))

  nonEmptyRender <| joinSegments init leadingSep Internal.backslash p.segments

/--
Render `p` to a POSIX-style `String` using `/` as the separator. Pure.

The path is decoded as UTF-8, with every byte that is not part of a well-formed encoding replaced by
`U+FFFD`; use `toPosixBytes` to render it without loss.
-/
def toPosixString (p : Path) : String :=
  String.fromUTF8Lossy p.toPosixBytes

/--
Render `p` to a Windows-style `String` using `\\` as the separator. Pure.

The path is decoded as UTF-8, with every byte that is not part of a well-formed encoding replaced by
`U+FFFD`; use `toWindowsBytes` to render it without loss.
-/
def toWindowsString (p : Path) : String :=
  String.fromUTF8Lossy p.toWindowsBytes

/--
Append `other` to `p`. Infix alias for `join`.
-/
instance : HDiv Path Path Path where
  hDiv := join

/--
Append the single validated segment `name` to `p`.
-/
instance : HDiv Path Filename Path where
  hDiv p name := p.join (ofFilename name)

/--
Test `p` against a glob pattern.

The pattern always uses `/` to separate segments, regardless of platform, and every separator counts:
a path is parsed with its repeated and trailing separators collapsed, so `"a//b"` and `"a/b/"` name a
segment that no path has and match nothing. The path with no component at all — `Path.empty` and
`"."` alike — is matched as the `.` it renders as.

By default, Windows prefixes are ignored and an absolute root matches an empty leading segment, so
`"/usr"` and `"/"` match themselves and a leading `**/` or `/` is what matches absolute paths.
Pass `matchDrivePrefix := true` to instead have the prefix stand as that leading segment: `C:\a`
matches `"C:/a"`, `\\server\share\a` matches `"\\\\server\\share/a"`, and the drive-relative `C:a`
matches `"C:/a"` too, since the pattern language has no way to tell a root from its absence once a
prefix occupies the leading segment.

Supported wildcards:
- `*` — matches any sequence of characters within a single segment (not `/`)
- `**` — matches whole segments, and has to be a whole segment itself: zero or more of them before a
  further segment, one or more at the end of the pattern, so `"src/**"` matches everything below
  `src` but not `src` itself
- `?` — matches any single character (not `/`)
- `[abc]` / `[a-z]` — character class, matches one character in the set or range
- `[!abc]` / `[!a-z]` — negated character class, matches one character not in the set or range
- a `]` right after `[` or `[!` is an ordinary member, so `"[]]"` is the class of `]` and `"[]"` and
  `"[!]"` are unterminated

Matching is case-sensitive. Pass `caseInsensitive := true` to fold ASCII letters instead, which
suits the case-insensitive file systems Windows and macOS default to: `"src/main.lean"` then matches
`src/MAIN.lean`. Folding applies to literals and to character classes, and a range is tested against
the character in both ASCII cases, so `"[a-z]"` matches `B` and `"[A-Z]"` matches `b`. Letters
outside ASCII are matched as written, and `?`, `*` and `**` are unaffected — the path is split into
segments before matching, so folding can never make a wildcard cross a `/`.

The pattern is decoded as UTF-8 while the path is not, so `?` and a character class each match one
character of a segment, and a byte that is not part of a well-formed encoding matches as a single
`U+FFFD`.

Returns `true` if the pattern matches the full path. A syntactically invalid pattern — an
unterminated `[...]` class, or a `**` glued to anything else in its segment — matches nothing.

The path is matched by its components, so a `.` in it is not matched against a segment of the
pattern and `"a/./b"` matches `"a/b"`. A `..` is a component and is matched as written rather than
resolved, so `"uploads/../secret"` matches `"uploads/**"`. This is a syntactic test, not a
containment check — use `isUnder`, or `resolveWithin` when the answer has to hold on the file
system.
-/
def matchGlob (p : Path) (pattern : String) (matchDrivePrefix : Bool := false)
    (caseInsensitive : Bool := false) : Bool :=
  match Internal.parseGlob pattern with
  | none => false
  | some glob =>
    let pfx := if matchDrivePrefix then p.windowsPrefix?.toArray else #[]
    let comps := p.components.map Segment.toBytes
    -- The path is matched as its rendering split back on `/`, so a root writes an empty leading
    -- segment, and a bare root, whose whole rendering is `"/"`, writes one on either side of it.
    -- A prefix already stands as the leading segment, and emitting both would leave `C:\a` needing
    -- the doubled `"C://a"`.
    let root :=
      if p.root?.isSome && pfx.isEmpty then
        if comps.isEmpty then #[ByteArray.empty, ByteArray.empty] else #[ByteArray.empty]
      else
        #[]
    -- A path anchored to nothing and with no component names the working directory, which is what
    -- it renders as; without this it would be matched as no segments at all and match nothing.
    let comps := if pfx.isEmpty && root.isEmpty && comps.isEmpty then #[Internal.dotBytes] else comps

    Internal.matchSegments glob (pfx ++ root ++ comps) caseInsensitive 0 0

/--
Parse a POSIX-formatted byte string into a `Path`. Pure; uses `/` as the only separator.

Returns `none` for empty input or input containing a null byte, which no platform permits in a path
and which would otherwise be silently truncated when handed back to the OS.
-/
def ofPosixBytes? (b : ByteArray) : Option Path :=
  if b.isEmpty || Internal.containsByte b Internal.nul then
    none
  else
    let (anchor, segments) := Internal.parsePosix b
    some { anchor, segments }

/--
Parse the UTF-8 encoding of a POSIX-formatted string into a `Path`. See `ofPosixBytes?`.
-/
def ofPosixString? (s : String) : Option Path :=
  ofPosixBytes? s.toByteArray

/--
Parse a POSIX-formatted string into a `Path`, panicking with an error message if `s` is empty or
contains a null byte. See `ofPosixString?` for the total version.

For a literal written in the source; `path("…")` validates one at elaboration time instead. A panic
returns the `Inhabited` default rather than stopping the program, so on rejected input this yields
`Path.empty`, and `base / Path.ofPosixString! s` is then `base` itself — an operation meant to reach
something below `base` silently names `base`. Parse anything that came from outside the source with
`ofPosixString?`, or with `ofString` to have the failure raised.
-/
def ofPosixString! (s : String) : Path :=
  match ofPosixString? s with
  | some p => p
  | none => panic! s!"invalid path {s.quote}"

/--
Parse a Windows-formatted byte string into a `Path`. Pure; accepts both `\` and `/`,
and an optional drive-letter prefix such as `"C:"`.

Returns `none` for empty input or input containing a null byte.

A leading `\\` introduces a prefix: a UNC share (`\\server\share`), a device path (`\\.\COM42`), or a
verbatim path (`\\?\C:\foo`, `\\?\UNC\server\share`). A bare `\\` with nothing after it is a plain
root instead, and `?` is not read as a server name, so only the literal `\\?\` spelling is verbatim
and `//?/x` is an ordinary rooted path.

A verbatim path is read under different rules, since Windows hands one to the filesystem without
normalizing it: only `\` separates, so a `/` stays part of a name, and `.` and `..` are ordinary
names that `normalize` leaves alone.
-/
def ofWindowsBytes? (b : ByteArray) : Option Path :=
  if b.isEmpty || Internal.containsByte b Internal.nul then
    none
  else
    let (anchor, segments) := Internal.parseWindows b
    some { anchor, segments }

/--
Parse the UTF-8 encoding of a Windows-formatted string into a `Path`. See `ofWindowsBytes?`.
-/
def ofWindowsString? (s : String) : Option Path :=
  ofWindowsBytes? s.toByteArray

/--
Parse a Windows-formatted string into a `Path`, panicking with an error message if `s` is empty or
contains a null byte. See `ofWindowsString?` for the total version.

For a literal written in the source. A panic returns the `Inhabited` default rather than stopping
the program, so on rejected input this yields `Path.empty`, and `base / Path.ofWindowsString! s` is
then `base` itself. Parse anything that came from outside the source with `ofWindowsString?`, or
with `ofString` to have the failure raised.
-/
def ofWindowsString! (s : String) : Path :=
  match ofWindowsString? s with
  | some p => p
  | none => panic! s!"invalid path {s.quote}"

/--
`b`, if reading it back with `parse` names the same path as `p` again.

The comparison is `==`, so `Path.empty` passes: it renders as `.`, which reads back as the
one-segment `.` path, and neither has a component. That matters because `Path.empty` is what
`normalize`, `dropPrefix?`, and `relativeTo?` produce whenever a relative path cancels to nothing.
-/
private def checkedRender (p : Path) (parse : ByteArray → Option Path) (b : ByteArray) :
    Option ByteArray :=
  if parse b == some p then some b else none

/--
Render `p` to a POSIX-style byte string using `/` as the separator, or `none` if POSIX syntax would
not read the result back as the same location. Pure.

Rendering a path across the flavour it was parsed with is lossy, and lossy in a way that produces
another well-formed path rather than an error: `C:\Users` renders as `/Users` and `\\server\share`
as `.`. This is `toPosixBytes` with that outcome ruled out, so a `some` is the path itself in POSIX
syntax and nothing else. The check is `==`, so it reads back the same path rather than the same
value; `Path.empty` renders as `.` and passes. See `checkedRender`.

Use this wherever the rendered path is handed on to name a file, and `toPosixBytes` only where the
result is for display.
-/
def toPosixBytes? (p : Path) : Option ByteArray :=
  checkedRender p ofPosixBytes? p.toPosixBytes

/--
Render `p` to a Windows-style byte string using `\` as the separator, or `none` if Windows syntax
would not read the result back as the same location. Pure. See `toPosixBytes?`; the losses here are
a POSIX root becoming drive-relative, and a segment holding Windows syntax — a `\`, or a leading
drive letter — being read as more than a name.
-/
def toWindowsBytes? (p : Path) : Option ByteArray :=
  checkedRender p ofWindowsBytes? p.toWindowsBytes

/--
Render `p` to a POSIX-style `String` using `/` as the separator, or `none` if POSIX syntax would not
read the result back as `p`. See `toPosixBytes?`.

Only the render is checked; the decoding is as lossy as `toPosixString`'s, so a path whose bytes are
not valid UTF-8 still comes back with `U+FFFD` in it. Use `toPosixBytes?` to render without loss.
-/
def toPosixString? (p : Path) : Option String :=
  String.fromUTF8Lossy <$> p.toPosixBytes?

/--
Render `p` to a Windows-style `String` using `\` as the separator, or `none` if Windows syntax would
not read the result back as `p`. See `toWindowsBytes?` and the decoding note on `toPosixString?`.
-/
def toWindowsString? (p : Path) : Option String :=
  String.fromUTF8Lossy <$> p.toWindowsBytes?

/--
A path as the term that rebuilds it: the parse call for the flavour it was parsed with, in the
syntax that flavour renders.

Falls back to the anchor and segments spelled out whenever that call would not reproduce the path —
because the checked render refuses it (a segment holding syntax the flavour gives meaning to), or
because its bytes are not valid UTF-8 and no string literal can hold them. `Path.empty` is shown as
itself rather than as the `.` it renders to, which reads back as a different path.
-/
instance : Repr Path where
  reprPrec p prec :=
    if p.isEmpty then
      "Std.Path.empty"
    else
      let (call, rendered) := match p.anchor with
        | .windows .. => (("Std.Path.ofWindowsString! " : Std.Format), p.toWindowsBytes?)
        | _ => ("Std.Path.ofPosixString! ", p.toPosixBytes?)
      match rendered.bind String.fromUTF8? with
      | some s => Repr.addAppParen (call ++ repr s) prec
      -- `Path.mk` is private, so this form is for reading rather than for pasting back.
      | none =>
        Repr.addAppParen ("Std.Path.mk " ++ reprArg p.anchor ++ " " ++ reprArg p.segments) prec

section IO

/--
The platform path separator character at runtime: `'/'` on POSIX, `'\\'` on Windows.
-/
def pathSeparator : IO Char :=
  return if System.Platform.isWindows then '\\' else '/'

/--
All path separator characters accepted by the current platform.

On POSIX: `['/']`. On Windows: `['\\', '/']`.
-/
def pathSeparators : IO (List Char) :=
  return if System.Platform.isWindows then ['\\', '/'] else ['/']

/--
Parse `b` using the platform-native separator and format, delegating to `ofPosixBytes?` on POSIX and
`ofWindowsBytes?` on Windows.

Lossless, so this is the function to use for a path the OS handed back: on POSIX a path is an
arbitrary byte string and on Windows it is WTF-8, so neither is guaranteed to be valid UTF-8.
-/
def ofBytes (b : ByteArray) : IO Path :=
  let res := if System.Platform.isWindows then ofWindowsBytes? b else ofPosixBytes? b
  res.elim (throw <| .userError s!"invalid path {(String.fromUTF8Lossy b).quote}") pure

/--
Render `p` to a byte string using the platform-native separator and format.

Lossless, and checked to be: a render the host's syntax would not read as `p` again fails rather
than handing the OS a different path. A path parsed under one platform's rules can carry a segment
that is syntax under the other's — the POSIX-parsed relative `C:/foo` would render as the absolute
Windows `C:\foo`, and a POSIX file name holding a `\` would split in two — and a Windows prefix has
no POSIX spelling at all.

This is `toPosixBytes?` or `toWindowsBytes?` chosen by the host and raising instead of returning
`none`. Reach for those to render for a named platform, and for `toPosixBytes`/`toWindowsBytes` only
where an unchecked render is wanted.
-/
def toBytes (p : Path) : IO ByteArray := do
  let checked := if System.Platform.isWindows then p.toWindowsBytes? else p.toPosixBytes?
  if let some b := checked then
    return b
  let unchecked := if System.Platform.isWindows then p.toWindowsBytes else p.toPosixBytes
  throw <| .userError
    s!"path does not survive rendering to the host platform's syntax: it would be read back as \
       {(String.fromUTF8Lossy unchecked).quote}"

/--
Parse `s` using the platform-native separator, delegating to
`ofPosixString?` on POSIX and `ofWindowsString?` on Windows.
-/
def ofString (s : String) : IO Path :=
  ofBytes s.toByteArray

/--
Render `p` to a string using the platform-native separator and format.

Decoding is lossy in the same way as `toPosixString` and `toWindowsString`; use `toBytes` to render
the path without loss.
-/
def toString (p : Path) : IO String :=
  String.fromUTF8Lossy <$> p.toBytes

/--
The process's current working directory.

Read as raw bytes, so a working directory whose name is not valid UTF-8 survives intact.
-/
def currentDir : IO Path :=
  ofBytes =<< Internal.UV.System.cwd

/--
Resolve `p` against the process's current working directory if it is relative.

If `p` is already absolute, it is returned unchanged. A drive-relative Windows path (e.g. `C:foo`) is
resolved against the current directory with its drive prefix dropped, since the per-drive working
directory is not available; a rooted one with no drive (e.g. `\foo`) takes the current directory's
drive. No symlinks are resolved; use `resolve` for that.

The result is `normalize`d, so any `..` in `p` is removed lexically and the path returned can name a
different file than `p` does when a segment above the `..` is a symbolic link. Use `resolve`, or
`resolveWithin` to keep the result inside a directory.
-/
def cwd (p : Path) : IO Path := do
  if p.isAbsolute then return p
  let cwdPath ← currentDir
  -- Only a drive prefix can reach here: every other prefix is absolute on its own. Dropping it
  -- keeps the root, so `\foo` still resolves against the current directory's drive.
  let rel := match p.anchor with
    | .windows _ rooted => { p with anchor := .ofWindows none rooted }
    | _ => p
  return cwdPath.join rel |>.normalize

/--
Make `p` absolute and resolve all symlinks, returning the canonical path.

Fails with an `IO.Error` if any segment of the path does not exist on the file system.
Unlike `cwd`, this performs actual file system access and resolves symlinks.
-/
def resolve (p : Path) : IO Path :=
  ofBytes =<< Internal.UV.System.realPath =<< p.toBytes

/--
True if `p` itself is a symbolic link, read without following it.

`false` if `p` names nothing. A symbolic link whose target is missing is indistinguishable from a
missing name to `resolve`, which fails with `noFileOrDirectory` for both, so this is what separates
them.
-/
def isSymlink (p : Path) : IO Bool :=
  Internal.UV.System.isSymlink =<< p.toBytes

/--
Resolve the longest ancestor of `p` that exists, then put the components below it back.

Resolving down to the deepest existing ancestor settles every symbolic link along the way, and a
component below it names nothing, so it can be appended as written. Only a genuine "no such file" is
taken to mean a component is missing; every other failure is raised, so a symbolic link that cannot
be followed is never mistaken for a plain name.

A `..` below the deepest existing ancestor is refused rather than removed: with nothing on disk to
resolve it against, the only way to eliminate it would be the lexical rewrite that this whole
function exists to avoid. A dangling symbolic link is refused for the same reason.
-/
private partial def resolveExisting (p : Path) : IO Path := do
  try
    p.resolve
  catch
    | e@(.noFileOrDirectory ..) =>
      match p.parent?, p.lastComponent? with
      | some parent, some last =>
        if last matches .parent then
          throw <| .userError "cannot resolve `..` below a path that does not exist"
        let resolved := (← resolveExisting parent).join { anchor := .neutral, segments := #[last] }
        -- A symbolic link whose target is missing is `ENOENT` to `realPath`, exactly as a name that
        -- is not there at all is. Appending one as an ordinary name would return a path that still
        -- leads wherever the link points, which is the escape `resolveWithin` is there to stop.
        --
        -- The link is looked for under the *resolved* parent, not under `p`: the parent has been
        -- through `realPath`, so nothing above `last` is a link any more and the answer is about
        -- `last` alone. Asking about `p` instead would be answering a different question.
        if ← resolved.isSymlink then
          throw <| .userError
            s!"cannot resolve {(resolved.toPosixString).quote}: it is a symbolic link whose target \
               does not exist"
        return resolved
      | _, _ => throw e
    | e => throw e

/--
Resolve `p` beneath `base` and fail unless it really lands there.

`p` must be relative and carry no drive or root, since an anchored one would replace `base` under
`join` rather than extend it. `base` itself is resolved first, so the answer is about the directory
`base` leads to rather than about how `base` is spelled.

Every component of the result that exists is resolved, so a symbolic link out of the tree is caught
even when a `..` behind it makes the path look contained; the components below the deepest existing
one name nothing and are appended as written.

A component that is a symbolic link with a missing target is refused rather than appended. `resolve`
cannot see where such a link leads, but the OS still follows it, so there is no verdict to give:
this holds whichever way the link points, and a link inside `base` waiting for its target to be
created is refused along with one aimed out of it.

Succeeding therefore says the returned path is under `base` at the moment of the call. It is not a
promise about the moment the caller uses it — anything may replace a component with a symbolic link
in between.
-/
def resolveWithin (base p : Path) : IO Path := do
  unless p.anchor matches .neutral do
    throw <| .userError
      s!"path to resolve within {(base.toPosixString).quote} must be relative and carry no drive \
         or root"
  let root ← base.resolve
  let resolved ← resolveExisting (root.join p)
  unless resolved.isUnder root do
    throw <| .userError s!"path escapes {(base.toPosixString).quote}"
  return resolved

end IO
end Path
end Std
