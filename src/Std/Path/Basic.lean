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
public import Init.Data.Ord.String
public import Init.System.IO
public import Init.System.Platform
public import Std.Path.Component
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
A platform-neutral, parsed file system path stored as an array of `Component`s.

All structural operations (`join`, `parent`, `normalize`, etc.) work directly on the `components`
array, so they are pure and require no OS calls. Platform-specific behaviour is limited to parsing
(`fromString`) and rendering (`toString`), which are `IO` actions.

Use `Path.ofPosixString` or `Path.ofWindowsString` for pure construction from string literals
when the platform format is known at compile time.
-/
structure Path where
  private mk ::
  /--
  The parsed path components in order (e.g. `#[.root "/", .normal "usr", .normal "bin"]`).
  -/
  components : Array Path.Component
deriving Inhabited, BEq, Hashable, Repr, Ord

namespace Path

private def splitAtLastDot (name : String) : Option (String.Slice × String.Slice) :=
  name.revFind? '.' |>.map fun dotPos => (name.extract name.startPos dotPos, name.extract dotPos.next! name.endPos)

@[inline]
private def get (path : Path) (idx : Nat) : Option Path.Component :=
  path.components[idx]?

/--
A valid file name: non-empty, not `.` or `..`, and contains no separator (`/`, `\`) or null byte
characters. Satisfied by `by decide` for string literals.
-/
abbrev ValidFileName (x : String) : Prop :=
  ¬x.isEmpty ∧ x ≠ "." ∧ x ≠ ".." ∧ x.toList.all (not <| · matches '\\' | '/' | '\x00')

/--
A valid file extension: non-empty and contains no separator (`/`, `\`), dot (`.`), or null byte.
Pass without the leading `.` — the dot is added by the caller. Satisfied by `by decide` for string
literals.
-/
abbrev ValidExtension (x : String) : Prop :=
  ¬x.isEmpty ∧ x.toList.all (not <| · matches '\\' | '/' | '\x00' | '.')

/--
A validated file name: a `String` known, by construction, to satisfy `ValidFileName`.
-/
structure Filename where
  /--
  The underlying file name.
  -/
  value : String

  /--
  Proof that `data` satisfies `ValidFileName`.
  -/
  proof : ValidFileName value := by decide
deriving BEq, DecidableEq, Hashable, Repr, Ord

namespace Filename

instance : Inhabited Filename := ⟨⟨"_", by decide⟩⟩

/--
Validate `s` as a `Filename`, returning `none` if it fails `ValidFileName`.
-/
def ofString? (s : String) : Option Filename :=
  if h : ValidFileName s then some ⟨s, h⟩ else none

/--
Validate `s` as a `Filename`, panicking with an error message if it fails `ValidFileName`.
-/
def ofString! (s : String) : Filename :=
  match ofString? s with
  | some name => name
  | none => panic! s!"invalid file name: {s.quote}"

instance : Coe Filename String := ⟨Filename.value⟩

instance : ToString Filename := ⟨Filename.value⟩

/--
True if the file name starts with `.` (a Unix-style hidden file, e.g. `.gitignore`).
-/
def isHidden (f : Filename) : Bool :=
  f.value.startsWith "."

end Filename

/--
A validated file extension (without the leading `.`): a `String` known, by construction, to satisfy
`ValidExtension`.
-/
structure Extension where
  /--
  The underlying extension, without the leading `.`.
  -/
  value : String

  /--
  Proof that `data` satisfies `ValidExtension`.
  -/
  proof : ValidExtension value := by decide
deriving BEq, DecidableEq, Hashable, Repr, Ord

namespace Extension

instance : Inhabited Extension := ⟨⟨"_", by decide⟩⟩

/--
Validate `s` as an `Extension`, returning `none` if it fails `ValidExtension`.
-/
def ofString? (s : String) : Option Extension :=
  if h : ValidExtension s then some ⟨s, h⟩ else none

/--
Validate `s` as an `Extension`, panicking with an error message if it fails `ValidExtension`.
-/
def ofString! (s : String) : Extension :=
  match ofString? s with
  | some ext => ext
  | none => panic! s!"invalid extension: {s.quote}"

instance : Coe Extension String := ⟨Extension.value⟩

instance : ToString Extension := ⟨Extension.value⟩

end Extension

/--
The empty path: no components. Joining any path with `empty` yields that path unchanged.
-/
def empty : Path := { components := #[] }

/--
A single-component path built from the validated `name`.
-/
def ofFilename (name : Filename) : Path := { components := #[.normal name.value] }

/--
True if `p` has no components.
-/
@[inline]
def isEmpty (p : Path) : Bool :=
  p.components.isEmpty

/--
True if the first component of `p` is `root` (or `drivePrefix` followed by `root`).

This is purely component-based and does not depend on the host platform. Note this differs from
Python and Rust on Windows: a rooted path with no drive letter (e.g. `\foo`) is treated as absolute
here, whereas they treat it as drive-relative (resolved against the current drive). Consequently
`join` replaces the left side when the right side is such a path, rather than keeping the left drive.
-/
def isAbsolute (p : Path) : Bool :=
  match p.get 0, p.get 1 with
  | some (.root _), _ => true
  | some (.drivePrefix _), some (.root _) => true
  | _, _ => false

/--
True if `p` is not absolute.
-/
@[inline]
def isRelative (p : Path) : Bool :=
  ¬p.isAbsolute


/--
Append `other` to `p`.

If `other` is an absolute path (its first component is `root` or `drivePrefix`), `other` replaces
`p` entirely — same semantics as Python's `PurePath.__truediv__` and Rust's `Path::join`.
-/
@[inline]
def join (p p₂ : Path) : Path :=
  if p₂.isAbsolute then p₂
  else { components := p.components ++ p₂.components }

/--
The drive-letter prefix as a string (e.g. `"C:"`).

Returns `none` on POSIX paths and relative Windows paths that have no drive letter.
-/
def drive? (p : Path) : Option String :=
  match p.get 0 with
  | some (.drivePrefix v) => some v
  | _ => none

/--
The root separator string (`"/"` or `"\\"`) if the path is absolute; `none` otherwise.
-/
def root? (p : Path) : Option String :=
  match p.get 0, p.get 1 with
  | some (.drivePrefix _), some (.root root) => some root
  | some (.root root), _ => some root
  | _, _ => none

/--
Drive concatenated with root (e.g. `"C:\\"`, `"/"`, or `""` for a relative path).
-/
def anchor (p : Path) : String :=
  (p.drive?.getD "") ++ (p.root?.getD "")

/--
The number of `normal` components in `p` (drive prefix, root, `.`, and `..` are not counted).

Examples:
- `depth (ofPosixString "/usr/local/bin" |>.get!) = 3`
- `depth (ofPosixString ".." |>.get!) = 0`
-/
def depth (p : Path) : Nat :=
  p.components.foldl (fun acc c => match c with | .normal _ => acc + 1 | _ => acc) 0

/--
Resolve `.` components and eliminate `..` components syntactically.

`..` above a root is silently dropped (no error). No file system access is performed; symlinks are
not resolved.
-/
def normalize (p : Path) : Path where
  components :=
    let acc := p.components.foldl (fun acc c =>
      match c with
      | .current => acc
      | .parent =>
        match acc.back? with
        | some (.normal _) => acc.pop
        | some .parent => acc.push .parent
        -- A drive prefix with no root is drive-relative, so a leading ".." is kept like in any
        -- other relative path.
        | some (.drivePrefix _) => acc.push .parent
        | none => acc.push .parent -- relative path: preserve leading ".."
        | _ => acc -- root: drop ".."
      | other => acc.push other
    ) #[]

    -- A relative path that normalizes to nothing is still ".", not empty.
    if acc.isEmpty && p.isRelative then #[.current] else acc

/--
Drop the last component, returning the parent directory path.

Returns `none` for root paths and empty paths. For a relative path whose parent would be empty
(e.g. `"a"`), returns `some "."`. `"."` is its own parent. Does not normalize the path first; call
`normalize` beforehand if needed.
-/
def parent (path : Path) : Option Path :=
  match path.components.back? with
  | none => none
  | some (.root _) | some (.drivePrefix _) => none
  | _ =>
    let cs := path.components.pop
    if cs.isEmpty then some { components := #[.current] }
    else some { components := cs }

/--
True if `p` is an absolute path with no further components (i.e. only a root, with an optional
drive prefix). Examples: `"/"`, `"C:\\"`.
-/
def isRoot (p : Path) : Bool :=
  p.isAbsolute && p.parent.isNone

/--
The last `normal` component (i.e. the file or directory name), validated as a `Filename`.

Returns `none` when the path ends with `root`, `current`, or `parent` components, or when the path
is empty. The result round-trips directly into `withFileName`/`HDiv` with no re-validation needed.
-/
def fileName (p : Path) : Option Filename :=
  match p.components.back? with
  | some (.normal v) => Filename.ofString? v
  | _ => none

/--
The filename without the last extension.

Returns `none` when there is no file name (see `fileName`).

Examples:
- `(ofPosixString "src/Main.lean" |>.get!).fileStem = some "Main"`
- `(ofPosixString "archive.tar.gz" |>.get!).fileStem = some "archive.tar"`
-/
def fileStem (p : Path) : Option String := do
  let name := (← p.fileName).value

  let (searchIn, hadLeadingDot) :=
    if name.startsWith "." && name.length > 1 then (String.ofList name.toList.tail, true)
    else (name, false)

  match splitAtLastDot searchIn with
  | none => some name
  | some (stem, _)  => if hadLeadingDot then some <| "." ++ stem else some stem.toString

/--
The filename stem before the first extension (i.e. before the first `.` after any leading dot).

Returns `none` when there is no file name (see `fileName`).

Examples:
- `(ofPosixString "foo.tar.gz" |>.get!).filePrefix = some "foo"`
- `(ofPosixString ".hidden" |>.get!).filePrefix = some ".hidden"`
- `(ofPosixString ".hidden.tar.gz" |>.get!).filePrefix = some ".hidden"`
- `(ofPosixString "Makefile" |>.get!).filePrefix = some "Makefile"`
-/
def filePrefix (p : Path) : Option String :=
  p.fileName.map fun name =>
    let name := name.value
    let (leadingDot, rest) :=
      if name.startsWith "." && name.length > 1 then (".", name.drop 1 |>.toString)
      else ("", name)

    let parts := rest.split "." |>.toArray
    if parts.isEmpty then name
    else leadingDot ++ parts[0]!.toString

/--
The last file extension, validated as an `Extension` (without the leading `.`).

Returns `none` when the filename has no extension (including a trailing-dot name like `"a."`, whose
"extension" would be empty and so isn't a valid `Extension`) or when there is no file name. The
result round-trips directly into `withExtension`/`addExtension` with no re-validation needed.

Examples:
- `(ofPosixString "Main.lean" |>.get!).extension = some (.mk "lean")`
- `(ofPosixString "archive.tar.gz" |>.get!).extension = some (.mk "gz")`
- `(ofPosixString "Makefile" |>.get!).extension = none`
-/
def extension (p : Path) : Option Extension :=
  p.fileName.bind fun name =>
    let name := name.value
    let searchIn :=
      if name.startsWith "." && name.length > 1 then name.extract name.startPos.next! name.endPos
      else name

    splitAtLastDot searchIn
    |>.bind (Extension.ofString? ·.2.toString)

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
Unchecked primitive: replace the last `normal` component with `fname`, leaving the rest unchanged.

If the last component is not a `normal` file name (i.e. `p` is empty, a root, or ends in `.` or
`..`), `p` is returned unchanged. `fname` is not validated — it must already be known to satisfy
`ValidFileName` (e.g. because it was built from the pieces of an existing, validated file name);
public callers should use `setFileName` instead.
-/
private def setLastComponent (p : Path) (fname : String) : Path :=
  match p.components.back? with
  | some (.normal _) => { p with components := p.components.pop.push (.normal fname) }
  | _ => p

/--
Replace the last path component with `name`.

If `p` has no `normal` file name (i.e. it is empty, a root, or ends in `.` or `..`), `p` is returned
unchanged. For a compile-time-known name, `p.setFileName (.mk "foo.txt")` just works; for a runtime
`String`, validate it first with `Filename.ofString?`.
-/
def setFileName (p : Path) (name : Filename) : Path :=
  p.setLastComponent name.value

/--
Replace the last file extension with `ext` (without leading `.`).

If the filename currently has no extension, `ext` is appended. If the path has no file name (e.g. it
is a root or empty), `p` is returned unchanged. Use `removeExtension` to strip an extension instead.
For a compile-time-known extension, `p.withExtension (.mk "gz")` just works; for a runtime `String`,
validate it first with `Extension.ofString?`.
-/
def withExtension (p : Path) (ext : Extension) : Path :=
  match p.fileStem with
  | none => p
  | some stem => p.setLastComponent (stem ++ "." ++ ext.value)

/--
Append `ext` (without leading `.`) to the file name, without removing any existing extensions.
-/
def addExtension (p : Path) (ext : Extension) : Path :=
  match p.fileName with
  | none => p
  | some name => p.setLastComponent (name.value ++ "." ++ ext.value)

/--
Remove the last file extension from the file name, keeping any earlier extensions.

If the file name has no extension, or the path has no file name (e.g. it is a root or empty), `p` is
returned unchanged.
-/
def removeExtension (p : Path) : Path :=
  match p.extension, p.fileStem with
  | some _, some stem => p.setLastComponent stem
  | _, _ => p

/--
All file extensions of the last component, in order, without leading `.`.

Examples:
- `(ofPosixString "archive.tar.gz" |>.get!).suffixes = #["tar", "gz"]`
- `(ofPosixString "Makefile" |>.get!).suffixes = #[]`
-/
def suffixes (p : Path) : Array String :=
  p.fileName.elim #[] fun name =>
    let name := name.value
    let name' := if name.startsWith "." && name.length > 1 then name.drop 1 else name
    let last := name'.split "." |>.toArray
    if last.size < 2 then #[]
    else last.drop 1 |>.map (·.toString)

/--
Replace the stem (all of the filename before the extensions) with `stem`, keeping every existing
extension intact.

Complement of `withExtension`: `p.withStem s |>.suffixes = p.suffixes`. For a compile-time-known stem,
`p.withStem (.mk "backup")` just works; for a runtime `String`, validate it first with
`Filename.ofString?`.
-/
def withStem (p : Path) (stem : Filename) : Path :=
  match p.fileName with
  | none => p
  | some _ =>
    let exts := p.suffixes

    let newName :=
      if exts.isEmpty then stem.value
      else stem.value ++ "." ++ String.intercalate "." exts.toList

    p.setLastComponent newName

/--
Implementation detail: iterator state for `Path.parents`.
-/
structure ParentsIterator where

  /--
  The path currently being examined.
  -/
  current : Path

  /--
  Remaining budget; equals the component count of the initial path.
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
  (IterM.mk (m := Id) (β := Path) ⟨p, p.components.size⟩).toIter

/--
True if `p` starts with `prefix` (component-wise, not as a raw string prefix).

`ofPosixString "/usr/local"` starts with `ofPosixString "/usr"` but not with `ofPosixString "/us"`.
-/
def startsWith (p prefx : Path) : Bool :=
  p.components.extract 0 prefx.components.size == prefx.components

/--
True if `p` ends with `suffix` (component-wise), matching Rust's `Path::ends_with`.

Matching is on whole components from the back, so `"/usr/bin".endsWith "bin"` and
`"/usr/bin".endsWith "usr/bin"` are both `true`, but `"/usr/bin".endsWith "sr/bin"` is `false`. A root
or drive in `suffix` must line up with `p`'s: `"/usr/bin".endsWith "/usr/bin"` is `true` while
`"/usr/bin".endsWith "/bin"` is `false`.
-/
def endsWith (p suffix : Path) : Bool :=
  let prefixSize := p.components.size - suffix.components.size
  p.components.extract prefixSize p.components.size == suffix.components

/--
Remove `prefix` from the beginning of `p` (component-wise).

Returns `none` if `p` does not start with `prefix`.
-/
def dropPrefix? (p prefx : Path) : Option Path :=
  if p.startsWith prefx then
    some { components := p.components.extract prefx.components.size p.components.size }
  else
    none

/--
Compute a relative path from `base` to `target` using `..` components to walk up out of `base`, so
that `(base.join r).normalize = target.normalize` where `r` is the returned path.

The result is purely syntactic: it does not consult the file system and treats every leading
component of `base` as a directory to ascend from (so `base` should usually be `normalize`d first if
it contains `.` or `..`).

Returns `none` if `base` and `target` have different roots (e.g. different drive letters on Windows,
or one absolute and one relative).
-/
def relativeTo? (base target : Path) : Option Path :=
  if base.drive? != target.drive? then
    none
  else if base.isAbsolute != target.isAbsolute then
    none
  else
    let bc := base.components
    let tc := target.components

    -- Count matching components from the front.
    let n :=
      (Array.range (min bc.size tc.size))
      |>.foldl (fun acc i => if acc == i && bc[i]! == tc[i]! then i + 1 else acc) 0

    let upComps : Array Component := (List.replicate (bc.size - n) .parent).toArray
    some { components := upComps ++ tc.extract n tc.size }

/--
Render `p` to a POSIX-style string using `/` as the separator. Pure.

`drivePrefix` components (Windows-only) are silently dropped; all other components are joined with
`/`. A path consisting of just a root renders as `"/"`.
-/
def toPosixString (p : Path) : String :=
  let (result, _) := p.components.foldl (fun (acc, sep) c =>
    match c with
    | .drivePrefix _ => (acc, sep)
    | .root _ => ("/", "")
    | .current => (acc ++ sep ++ ".", "/")
    | .parent => (acc ++ sep ++ "..", "/")
    | .normal v => (acc ++ sep ++ v, "/"))
    ("", "")
  result

/--
Render `p` to a Windows-style string using `\\` as the separator. Pure.

Drive prefixes are written without a trailing separator (the `root` component provides it). All
components are joined with `\\`.
-/
def toWindowsString (p : Path) : String :=
  let (result, _) := p.components.foldl fun (acc, sep) c =>
    match c with
    | .drivePrefix v => (acc ++ v, "")
    | .root _ => (acc ++ "\\", "")
    | .current => (acc ++ sep ++ ".", "\\")
    | .parent => (acc ++ sep ++ "..", "\\")
    | .normal v => (acc ++ sep ++ v, "\\")
    ("", "")
  result

/--
Append `other` to `p`. Infix alias for `join`.
-/
instance : HDiv Path Path Path where
  hDiv := join

/--
Append the single validated component `name` to `p`.
-/
instance : HDiv Path Filename Path where
  hDiv p name := p.join (ofFilename name)

/--
Test `p` against a glob pattern.

The pattern always uses `/` to separate segments, regardless of platform. By default, drive
prefixes are ignored and an absolute root matches an empty leading segment (so use a leading
`**/` or `/` to match absolute paths); pass `matchDrivePrefix := true` to instead require the
pattern to match the drive prefix (e.g. `"C:"`) as its own leading segment.

Supported wildcards:
- `*` — matches any sequence of characters within a single component (not `/`)
- `**` — matches zero or more components (path segments); only recognized as a whole segment
- `?` — matches any single character (not `/`)
- `[abc]` / `[a-z]` — character class, matches one character in the set or range
- `[!abc]` / `[!a-z]` — negated character class, matches one character not in the set or range

Returns `true` if the pattern matches the full path. A syntactically invalid pattern (e.g. an
unterminated `[...]` class) matches nothing.
-/
def matchGlob (p : Path) (pattern : String) (matchDrivePrefix : Bool := false) : Bool :=
  match Internal.parseGlob pattern with
  | none => false
  | some glob =>
    let comps := p.components.filter fun
      | .drivePrefix _ => matchDrivePrefix
      | _ => true

    Internal.matchSegments glob comps 0 0

/--
Parse a POSIX-formatted string into a `Path`. Pure; uses `/` as the only separator.

Returns `none` for the empty string or input containing a null byte (`\x00`), which no platform
permits in a path and which would otherwise be silently truncated when rendered to a native string.
-/
def ofPosixString (s : String) : Option Path :=
  if s.isEmpty || s.contains '\x00' then none
  else match Internal.posixPathParser.run s with
  | .ok cs => some { components := cs }
  | .error _ => none

/--
Parse a POSIX-formatted string into a `Path`, panicking with an error message if `s` is empty or
contains a null byte. See `ofPosixString` for the total version.
-/
def ofPosixString! (s : String) : Path :=
  match ofPosixString s with
  | some p => p
  | none => panic! s!"invalid path {s.quote}"

/--
Parse a Windows-formatted string into a `Path`. Pure; accepts both `\` and `/`,
and an optional drive-letter prefix such as `"C:"`.

Returns `none` for the empty string or input containing a null byte (`\x00`). UNC paths
(`\\server\share`) are not specially recognized: a leading `\\` collapses to a single `root`, so the
server and share become ordinary components.
-/
def ofWindowsString (s : String) : Option Path :=
  if s.isEmpty || s.contains '\x00' then none
  else match Internal.windowsPathParser.run s with
  | .ok cs => some { components := cs }
  | .error _ => none

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
Parse `s` using the platform-native separator, delegating to
`ofPosixString` on POSIX and `ofWindowsString` on Windows.
-/
def fromString (s : String) : IO Path :=
  let res := if System.Platform.isWindows then ofWindowsString s else ofPosixString s
  res.elim (throw <| .userError s!"invalid path {s.quote}") pure

/--
Render `p` to a string using the platform-native separator and format.
-/
def toString (p : Path) : IO String :=
  return if System.Platform.isWindows then p.toWindowsString else p.toPosixString

/--
Resolve `p` against the process's current working directory if it is relative.

If `p` is already absolute, it is returned unchanged. A drive-relative Windows path (e.g. `C:foo`) is
resolved against the current directory with its drive prefix dropped, since the per-drive working
directory is not available. No symlinks are resolved; use `resolve` for that.
-/
def toAbsoluteCwd (p : Path) : IO Path := do
  if p.isAbsolute then return p
  let cwdPath ← fromString (← Internal.UV.System.cwd)
  let rel := match p.get 0 with
    | some (.drivePrefix _) => { p with components := p.components.extract 1 p.components.size }
    | _ => p
  return cwdPath.join rel |>.normalize

/--
Make `p` absolute and resolve all symlinks, returning the canonical path.

Fails with an `IO.Error` if any component of the path does not exist on the file system.
Unlike `toAbsoluteCwd`, this performs actual file system access and resolves symlinks.
-/
def resolve (p : Path) : IO Path :=
  fromString =<< Internal.UV.System.realPath =<< p.toString

end IO
end Path
end Std
