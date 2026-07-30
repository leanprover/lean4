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
public import Init.Data.Repr
public import Init.Data.BEq
public import Init.Data.Hashable
public import Init.Data.ToString.Basic
public import Init.Data.Ord.String

public section

/-!
# Path.Component

The `Path.Component` type, the parsed building block of a `Std.Path`, and the `Path.Prefix` type of
Windows path prefixes. The `Path` structure itself is defined in `Std.Path.Basic`.
-/

namespace Std

/--
What a Windows path is anchored to, ahead of its root: a drive letter, a network share, or a device.
POSIX paths never have a prefix.

Prefixes are only produced by parsing a Windows-style string, and only as the first component of a
path.
-/
inductive Path.Prefix where

  /--
  A drive letter, e.g. `C:` in `C:\Windows`. The `value` includes the trailing colon.
  -/
  | disk (value : String)

  /--
  A UNC share, e.g. `\\server\share`. `share` is empty for a path that names only a server.
  -/
  | unc (server share : String)

  /--
  A path in the device namespace, e.g. `\\.\COM42` or `\\.\pipe\name`, where `value` is the first
  segment after `\\.\`.
  -/
  | deviceNS (value : String)

  /--
  A verbatim path, e.g. `\\?\cat_pics`, which Windows hands to the filesystem without normalizing
  it. `value` is the first segment after `\\?\`.
  -/
  | verbatim (value : String)

  /--
  A verbatim drive letter, e.g. `\\?\C:`. The `value` includes the trailing colon.
  -/
  | verbatimDisk (value : String)

  /--
  A verbatim UNC share, e.g. `\\?\UNC\server\share`.
  -/
  | verbatimUNC (server share : String)
deriving Inhabited, BEq, Hashable, Repr, Ord

namespace Path.Prefix

/--
Render the prefix in Windows form, without a trailing separator.
-/
def toWindowsString : Prefix → String
  | .disk value => value
  | .unc server share => "\\\\" ++ server ++ (if share.isEmpty then "" else "\\" ++ share)
  | .deviceNS value => "\\\\.\\" ++ value
  | .verbatim value => "\\\\?\\" ++ value
  | .verbatimDisk value => "\\\\?\\" ++ value
  | .verbatimUNC server share =>
    "\\\\?\\UNC\\" ++ server ++ (if share.isEmpty then "" else "\\" ++ share)

/--
Whether this is a verbatim (`\\?\`) prefix. Windows applies no normalization of its own to such a
path, so `.` and `..` in it are taken literally by the filesystem rather than resolved.
-/
def isVerbatim : Prefix → Bool
  | .verbatim _ | .verbatimDisk _ | .verbatimUNC _ _ => true
  | _ => false

/--
The drive letter with its trailing colon (e.g. `"C:"`), for the two prefixes that name one.
-/
def drive? : Prefix → Option String
  | .disk value | .verbatimDisk value => some value
  | _ => none

/--
Whether the prefix names an absolute location on its own, without a root following it.

A drive letter does not: `C:foo` is relative to the working directory of drive `C:`. Every other
prefix does, so `\\server\share` and `\\?\cat_pics` are absolute as they stand.
-/
def hasImplicitRoot : Prefix → Bool
  | .disk _ | .verbatimDisk _ => false
  | _ => true

end Path.Prefix

/--
A single parsed segment of a file system path.

Paths are stored as `Array Component`, so all structural operations (parent, join, normalize) work
directly on this array without re-scanning strings.
-/
inductive Path.Component where

  /--
  A Windows path prefix, e.g. `"C:"` or `"\\\\server\\share"` (without the trailing separator).

  Only produced when parsing a Windows-style string, and only in first position. POSIX paths never
  contain this component.
  -/
  | winPrefix (value : Path.Prefix)

  /--
  The root separator (`/` on POSIX, `\` on Windows).

  Present as the first component of every absolute path. Relative paths never
  start with `root`.
  -/
  | root (value : String)

  /--
  The special `.` segment, meaning "current directory".

  Preserved during parsing so that round-trips are lossless; `Path.normalize`
  removes these.
  -/
  | current

  /--
  The special `..` segment, meaning "parent directory".

  Preserved during parsing; `Path.normalize` resolves these where possible.
  -/
  | parent

  /--
  An ordinary path segment — a file or directory name with no separators.

  The `value` is the raw segment string (e.g. `"src"`, `"Main.lean"`).
  -/
  | normal (value : String)
deriving Inhabited, BEq, Hashable, Repr, Ord

end Std
