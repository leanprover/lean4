/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Init.Data.String
public import Init.Data.Repr
public import Init.Data.BEq
public import Init.Data.Hashable
public import Init.Data.Iterators.Producers
public import Init.Data.Ord.Array
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
All structural operations (`join`, `parent`, `normalize`, etc.) work directly on these two fields,
so they are pure and require no OS calls.

Use `Path.ofPosixString` or `Path.ofWindowsString` for pure construction from strings when the
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
deriving Inhabited, BEq, DecidableEq, Hashable

namespace Path

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
True if `p` has no anchor and no segments.
-/
@[inline]
def isEmpty (p : Path) : Bool :=
  p.anchor matches .neutral && p.segments.isEmpty

/--
The Windows prefix of `p` as raw bytes and without a trailing separator, if it has one.

Returns `none` on POSIX paths and on Windows paths with no prefix (e.g. `foo\bar` or `\foo`).
-/
@[inline]
def winPrefix? (p : Path) : Option ByteArray :=
  p.anchor.prefix?

/--
The drive-letter prefix as raw bytes (e.g. the bytes of `"C:"`).

Returns `none` on POSIX paths, on relative Windows paths that have no drive letter, and on prefixes
that name no drive (e.g. `\\server\share`) — use `winPrefix?` to see those.
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
Append `other` to `p`.

`other` replaces `p` entirely if it is absolute or brings a Windows prefix of its own. If it is
rooted but has no prefix (a Windows `\foo`, relative to the current drive), it keeps only `p`'s
prefix: `C:\a` joined with `\b` is `C:\b`.
-/
def join (p p₂ : Path) : Path :=
  match p₂.anchor with
  | .neutral => { p with segments := p.segments ++ p₂.segments }
  | .windows none rooted => { p₂ with anchor := .ofWindows p.winPrefix? rooted }
  | _ => p₂

/--
The anchor rendered as raw bytes: prefix concatenated with root (e.g. `"C:\\"`,
`"\\\\server\\share\\"`, `"/"`, or `""` for a neutral path).
-/
def anchorBytes (p : Path) : ByteArray :=
  p.winPrefix?.getD .empty ++ p.root?.getD .empty

/--
Resolve `.` segments and eliminate `..` segments syntactically.

`..` above a root is silently dropped (no error). No file system access is performed; symlinks are
not resolved.
-/
def normalize (p : Path) : Path :=
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

  -- An unanchored path that normalizes to nothing is still ".", not empty.
  if acc.isEmpty && p.anchor matches .neutral then { p with segments := #[.current] }
  else { p with segments := acc }

/--
Drop the last segment, returning the parent directory path.

Returns `none` for root paths and empty paths. For a relative path whose parent would be empty
(e.g. `"a"`), returns `some "."`. `"."` is its own parent. Does not normalize the path first; call
`normalize` beforehand if needed.
-/
def parent (path : Path) : Option Path :=
  if path.segments.isEmpty then
    none
  else
    let segs := path.segments.pop
    if segs.isEmpty && path.anchor matches .neutral then some { path with segments := #[.current] }
    else some { path with segments := segs }

/--
True if `p` starts at a root and has no segments (i.e. only a root, with an optional drive
prefix). Examples: `"/"`, `"C:\\"`, `"\\"`.

Uses `hasRoot`, not `isAbsolute`, so the drive-relative `"\\"` counts.
-/
def isRoot (p : Path) : Bool :=
  p.hasRoot && p.segments.isEmpty

/--
The last `normal` segment (i.e. the file or directory name), validated as a `Filename`.

Returns `none` when the path ends in `.` or `..`, and when it has no segments at all (a root or the
empty path). The result round-trips directly into `setFileName`/`HDiv` with no re-validation needed.
-/
def fileName (p : Path) : Option Filename :=
  match p.segments.back? with
  | some (.normal v) => Filename.ofBytes? v
  | _ => none

/--
The filename without the last extension, as raw bytes.

Returns `none` when there is no file name (see `fileName`).

Examples:
- `(ofPosixString "src/Main.lean" |>.get!).fileStem = some "Main".toByteArray`
- `(ofPosixString "archive.tar.gz" |>.get!).fileStem = some "archive.tar".toByteArray`
-/
def fileStem (p : Path) : Option ByteArray := do
  let name := (← p.fileName).value

  match Internal.revFindByte? name Internal.dot with
  | none => some name
  -- A name that is nothing but a leading dot and a stem, like `.gitignore`, has no extension.
  | some lastDot => if lastDot = 0 then some name else some (name.extract 0 lastDot)

/--
The filename stem before the first extension (i.e. before the first `.` after any leading dot), as
raw bytes.

Returns `none` when there is no file name (see `fileName`).

Examples:
- `(ofPosixString "foo.tar.gz" |>.get!).filePrefix = some "foo".toByteArray`
- `(ofPosixString ".hidden" |>.get!).filePrefix = some ".hidden".toByteArray`
- `(ofPosixString ".hidden.tar.gz" |>.get!).filePrefix = some ".hidden".toByteArray`
- `(ofPosixString "Makefile" |>.get!).filePrefix = some "Makefile".toByteArray`
-/
def filePrefix (p : Path) : Option ByteArray := do
  let name := (← p.fileName).value
  return name.extract 0 (stemEnd name)

/--
The last file extension, validated as an `Extension` (without the leading `.`).

Returns `none` when the filename has no extension (including a trailing-dot name like `"a."`, whose
"extension" would be empty and so isn't a valid `Extension`) or when there is no file name. The
result round-trips directly into `withExtension`/`addExtension` with no re-validation needed.

Examples:
- `(ofPosixString "Main.lean" |>.get!).extension = some (.mk "lean".toByteArray)`
- `(ofPosixString "archive.tar.gz" |>.get!).extension = some (.mk "gz".toByteArray)`
- `(ofPosixString "Makefile" |>.get!).extension = none`
-/
def extension (p : Path) : Option Extension := do
  let name := (← p.fileName).value

  match Internal.revFindByte? name Internal.dot with
  | none => none
  | some lastDot =>
    if lastDot = 0 then
      none
    else
      Extension.ofBytes? (name.extract (lastDot + 1) name.size)

/--
True if the file name has at least one extension.
-/
def hasExtension (p : Path) : Bool :=
  p.extension.isSome

/--
True if `p` has a file name and it is hidden (starts with `.`, e.g. `.gitignore`).

Returns `false` when there is no file name (see `fileName`).
-/
def isHidden (p : Path) : Bool :=
  p.fileName.elim false Filename.isHidden

/--
Unchecked primitive: replace the last `normal` segment with `fname`, leaving the rest unchanged.

If the last segment is not a `normal` file name (i.e. `p` is empty, a root, or ends in `.` or
`..`), `p` is returned unchanged. `fname` is not validated — it must already be known to satisfy
`ValidFilename` (e.g. because it was built from the pieces of an existing, validated file name);
public callers should use `setFileName` instead.
-/
private def setLastSegment (p : Path) (fname : ByteArray) : Path :=
  match p.segments.back? with
  | some (.normal _) => { p with segments := p.segments.pop.push (.normal fname) }
  | _ => p

/--
Replace the last path segment with `name`.

If `p` has no `normal` file name (i.e. it is empty, a root, or ends in `.` or `..`), `p` is returned
unchanged. For a compile-time-known name, `p.setFileName (.mk "foo.txt".toByteArray)` just works; for a
runtime `String`, validate it first with `Filename.ofString?`.
-/
def setFileName (p : Path) (name : Filename) : Path :=
  p.setLastSegment name.value

/--
Replace the last file extension with `ext` (without leading `.`).

If the filename currently has no extension, `ext` is appended. If the path has no file name (e.g. it
is a root or empty), `p` is returned unchanged. Use `removeExtension` to strip an extension instead.
For a compile-time-known extension, `p.withExtension (.mk "gz".toByteArray)` just works; for a runtime
`String`, validate it first with `Extension.ofString?`.
-/
def withExtension (p : Path) (ext : Extension) : Path :=
  match p.fileStem with
  | none => p
  | some stem => p.setLastSegment (stem ++ Internal.dotBytes ++ ext.value)

/--
Append `ext` (without leading `.`) to the file name, without removing any existing extensions.
-/
def addExtension (p : Path) (ext : Extension) : Path :=
  match p.fileName with
  | none => p
  | some name => p.setLastSegment (name.value ++ Internal.dotBytes ++ ext.value)

/--
Remove the last file extension from the file name, keeping any earlier extensions.

If the file name has no extension, or the path has no file name (e.g. it is a root or empty), `p` is
returned unchanged.
-/
def removeExtension (p : Path) : Path :=
  match p.extension, p.fileStem with
  | some _, some stem => p.setLastSegment stem
  | _, _ => p

/--
All file extensions of the last segment, in order, without leading `.`, as raw bytes.

Examples:
- `(ofPosixString "archive.tar.gz" |>.get!).suffixes = #["tar".toByteArray, "gz".toByteArray]`
- `(ofPosixString "Makefile" |>.get!).suffixes = #[]`
-/
def suffixes (p : Path) : Array ByteArray :=
  match p.fileName with
  | none => #[]
  | some name =>
    let name := name.value
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
  match p.fileName with
  | none => p
  | some name =>
    let name := name.value
    p.setLastSegment (stem.value ++ name.extract (stemEnd name) name.size)

/--
Implementation detail: iterator state for `Path.parents`.
-/
structure ParentsIterator where

  /--
  The path currently being examined.
  -/
  current : Path

  /--
  Remaining budget; equals the segment count of the initial path.
  -/
  fuel : Nat

namespace ParentsIterator

abbrev stateOf (it : IterM (α := ParentsIterator) m Path) : ParentsIterator :=
  match it with | ⟨s⟩ => s

instance instIterator [Pure m] : Iterator ParentsIterator m Path where
  IsPlausibleStep it
    | .yield it' out =>
        (stateOf it).fuel = (stateOf it').fuel + 1 ∧
        (stateOf it).current.parent = some out ∧
        (out == (stateOf it).current) = false ∧
        (stateOf it').current = out
    | .skip _ => False
    | .done => True
  step it :=
    pure (match it with
    | ⟨⟨_, 0⟩⟩ => .deflate ⟨.done, trivial⟩
    | ⟨⟨cur, fuel + 1⟩⟩ =>
      match cur.parent with
      | none => .deflate ⟨.done, trivial⟩
      | some par =>
        match h : (par == cur) with
        | true  => .deflate ⟨.done, trivial⟩
        | false => .deflate ⟨.yield ⟨⟨par, fuel⟩⟩ par, rfl, rfl, h, rfl⟩)

instance [Monad n] : IteratorLoop ParentsIterator Id n := .defaultImplementation

end ParentsIterator

/--
All ancestors of `p`, from the immediate parent up to (and including) the root, in order.

For `ofPosixString "/a/b/c"` this yields an iterator over the paths
`["/a/b", "/a", "/"]`.
-/
def parents (p : Path) : Iter (α := ParentsIterator) Path :=
  (IterM.mk (m := Id) (β := Path) ⟨p, p.segments.size⟩).toIter

/--
True if `p` and `prefx` share an anchor and `prefx`'s segments are a prefix of `p`'s (segment-wise,
not as a raw byte prefix).

`ofPosixString "/usr/local"` starts with `ofPosixString "/usr"` but not with `ofPosixString "/us"`,
and no absolute path starts with a relative one.
-/
def startsWith (p prefx : Path) : Bool :=
  p.anchor == prefx.anchor && prefx.segments.isPrefixOf p.segments

/--
True if `p` ends with `suffix` (segment-wise).

Matching is on whole segments from the back, so `"/usr/bin".endsWith "bin"` and
`"/usr/bin".endsWith "usr/bin"` are both `true`, but `"/usr/bin".endsWith "sr/bin"` is `false`. An
anchored `suffix` must match `p` outright, anchor included: `"/usr/bin".endsWith "/usr/bin"` is
`true` while `"/usr/bin".endsWith "/bin"` is `false`.
-/
def endsWith (p suffix : Path) : Bool :=
  if suffix.anchor matches .neutral then
    suffix.segments.size ≤ p.segments.size &&
      p.segments.extract (p.segments.size - suffix.segments.size) p.segments.size == suffix.segments
  else
    p.anchor == suffix.anchor && p.segments == suffix.segments

/--
Remove `prefx` from the beginning of `p` (segment-wise), leaving an unanchored path.

Returns `none` if `p` does not start with `prefx`.
-/
def dropPrefix? (p prefx : Path) : Option Path :=
  if p.startsWith prefx then
    some { anchor := .neutral, segments := p.segments.extract prefx.segments.size p.segments.size }
  else
    none

/--
How many leading segments `a` and `b` have in common.
-/
private def commonPrefixLength (a b : Array Segment) : Nat :=
  go 0
where
  go (i : Nat) : Nat :=
    if h : i < min a.size b.size then
      if a[i]! == b[i]! then go (i + 1) else i
    else
      i
  termination_by min a.size b.size - i

/--
Compute an unanchored path from `base` to `target` using `..` segments to walk up out of `base`, so
that `(base.join r).normalize = target.normalize` where `r` is the returned path.

The result is purely syntactic: it does not consult the file system and treats every leading
segment of `base` as a directory to ascend from (so `base` should usually be `normalize`d first if
it contains `.` or `..`).

Returns `none` if `base` and `target` have different anchors (e.g. different drive letters or
network shares on Windows, or one absolute and one relative).
-/
def relativeTo? (base target : Path) : Option Path :=
  if base.anchor != target.anchor then
    none
  else
    let n := commonPrefixLength base.segments target.segments
    let ups := Array.replicate (base.segments.size - n) Segment.parent
    some { anchor := .neutral, segments := ups ++ target.segments.extract n target.segments.size }

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

A Windows prefix is silently dropped; the segments are joined with `/`, behind a leading `/` if the
anchor writes a root. A path consisting of just a root renders as `"/"`.
-/
def toPosixBytes (p : Path) : ByteArray :=
  let init := if p.root?.isSome then Internal.slashBytes else .empty
  joinSegments init false Internal.slash p.segments

/--
Render `p` to a Windows-style byte string using `\\` as the separator. Pure.

A prefix is written without a trailing separator, so `\\server\share` and `\\server\share\` stay
distinct. The segments are joined with `\\`.
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

  joinSegments init leadingSep Internal.backslash p.segments

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

The pattern always uses `/` to separate segments, regardless of platform. By default, Windows
prefixes are ignored and an absolute root matches an empty leading segment (so use a leading
`**/` or `/` to match absolute paths); pass `matchDrivePrefix := true` to instead require the
pattern to match the prefix (e.g. `"C:"` or `"\\\\server\\share"`) as its own leading segment.

Supported wildcards:
- `*` — matches any sequence of characters within a single segment (not `/`)
- `**` — matches zero or more whole segments; only recognized as a whole segment
- `?` — matches any single character (not `/`)
- `[abc]` / `[a-z]` — character class, matches one character in the set or range
- `[!abc]` / `[!a-z]` — negated character class, matches one character not in the set or range

The pattern is decoded as UTF-8 while the path is not, so `?` and a character class each match one
character of a segment, and a byte that is not part of a well-formed encoding matches as a single
`U+FFFD`.

Returns `true` if the pattern matches the full path. A syntactically invalid pattern (e.g. an
unterminated `[...]` class) matches nothing.
-/
def matchGlob (p : Path) (pattern : String) (matchDrivePrefix : Bool := false) : Bool :=
  match Internal.parseGlob pattern with
  | none => false
  | some glob =>
    let pfx := if matchDrivePrefix then p.winPrefix?.toArray else #[]
    let root := if p.root?.isSome then #[ByteArray.empty] else #[]

    Internal.matchSegments glob (pfx ++ root ++ p.segments.map Segment.toBytes) 0 0

/--
Parse a POSIX-formatted byte string into a `Path`. Pure; uses `/` as the only separator.

Returns `none` for empty input or input containing a null byte, which no platform permits in a path
and which would otherwise be silently truncated when handed back to the OS.
-/
def ofPosixBytes (b : ByteArray) : Option Path :=
  if b.isEmpty || Internal.containsByte b Internal.nul then
    none
  else
    let (anchor, segments) := Internal.parsePosix b
    some { anchor, segments }

/--
Parse the UTF-8 encoding of a POSIX-formatted string into a `Path`. See `ofPosixBytes`.
-/
def ofPosixString (s : String) : Option Path :=
  ofPosixBytes s.toByteArray

/--
Parse a POSIX-formatted string into a `Path`, panicking with an error message if `s` is empty or
contains a null byte. See `ofPosixString` for the total version.
-/
def ofPosixString! (s : String) : Path :=
  match ofPosixString s with
  | some p => p
  | none => panic! s!"invalid path {s.quote}"

/--
Parse a Windows-formatted byte string into a `Path`. Pure; accepts both `\` and `/`,
and an optional drive-letter prefix such as `"C:"`.

Returns `none` for empty input or input containing a null byte.

A leading `\\` introduces a prefix: a UNC share (`\\server\share`), a device path (`\\.\COM42`), or a
verbatim path (`\\?\C:\foo`, `\\?\UNC\server\share`). A bare `\\` with nothing after it is a plain
root instead.

A verbatim path is not split into segments at all: everything after the literal `\\?\` marker stays
in the prefix, so `normalize` leaves its `.` and `..` alone, as Windows does when it hands the path
to the filesystem unchanged.
-/
def ofWindowsBytes (b : ByteArray) : Option Path :=
  if b.isEmpty || Internal.containsByte b Internal.nul then
    none
  else
    let (anchor, segments) := Internal.parseWindows b
    some { anchor, segments }

/--
Parse the UTF-8 encoding of a Windows-formatted string into a `Path`. See `ofWindowsBytes`.
-/
def ofWindowsString (s : String) : Option Path :=
  ofWindowsBytes s.toByteArray

/--
Parse a Windows-formatted string into a `Path`, panicking with an error message if `s` is empty or
contains a null byte. See `ofWindowsString` for the total version.
-/
def ofWindowsString! (s : String) : Path :=
  match ofWindowsString s with
  | some p => p
  | none => panic! s!"invalid path {s.quote}"

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
Parse `b` using the platform-native separator and format, delegating to `ofPosixBytes` on POSIX and
`ofWindowsBytes` on Windows.

Lossless, so this is the function to use for a path the OS handed back: on POSIX a path is an
arbitrary byte string and on Windows it is WTF-8, so neither is guaranteed to be valid UTF-8.
-/
def fromBytes (b : ByteArray) : IO Path :=
  let res := if System.Platform.isWindows then ofWindowsBytes b else ofPosixBytes b
  res.elim (throw <| .userError s!"invalid path {(String.fromUTF8Lossy b).quote}") pure

/--
Render `p` to a byte string using the platform-native separator and format. Lossless.
-/
def toBytes (p : Path) : IO ByteArray :=
  return if System.Platform.isWindows then p.toWindowsBytes else p.toPosixBytes

/--
Parse `s` using the platform-native separator, delegating to
`ofPosixString` on POSIX and `ofWindowsString` on Windows.
-/
def fromString (s : String) : IO Path :=
  fromBytes s.toByteArray

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
  fromBytes =<< Internal.UV.System.cwd

/--
Resolve `p` against the process's current working directory if it is relative.

If `p` is already absolute, it is returned unchanged. A drive-relative Windows path (e.g. `C:foo`) is
resolved against the current directory with its drive prefix dropped, since the per-drive working
directory is not available; a rooted one with no drive (e.g. `\foo`) takes the current directory's
drive. No symlinks are resolved; use `resolve` for that.
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
  fromBytes =<< Internal.UV.System.realPath =<< p.toBytes

end IO
end Path
end Std
