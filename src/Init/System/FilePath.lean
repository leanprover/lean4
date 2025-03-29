/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
prelude
import Init.System.Platform
import Init.Data.ToString.Basic

namespace System
open Platform

/--
A path on the file system.

Paths consist of a sequence of directories followed by the name of a file or directory. They are
delimited by a platform-dependent separator character (see `System.FilePath.pathSeparator`).
-/
structure FilePath where
  /-- The string representation of the path. -/
  toString : String
  deriving Inhabited, DecidableEq, Hashable

instance : Repr FilePath where
  reprPrec p := Repr.addAppParen ("FilePath.mk " ++ repr p.toString)

instance : ToString FilePath where
  toString p := p.toString

namespace FilePath

/--
The character that separates directories.

On platforms that support multiple separators, `System.FilePath.pathSeparator` is the “ideal” one expected by users
on the platform. `System.FilePath.pathSeparators` lists all supported separators.
-/
def pathSeparator : Char :=
  if isWindows then '\\' else '/'

/--
The list of all path separator characters supported on the current platform.

On platforms that support multiple separators, `System.FilePath.pathSeparator` is the “ideal” one
expected by users on the platform.
-/
def pathSeparators : List Char :=
  if isWindows then ['\\', '/'] else ['/']

/--
The character that separates file extensions from file names.
-/
def extSeparator : Char := '.'

/--
The file extension expected for executable binaries on the current platform, or `""` if there is no
such extension.
-/
def exeExtension : String :=
  if isWindows then "exe" else ""

/--
Normalizes a path, returning an equivalent path that may better follow platform conventions.

In particular:
 * On Windows, drive letters are made uppercase.
 * On platforms that support multiple path separators (that is, where
   `System.FilePath.pathSeparators` has length greater than one), alternative path separators are
   replaced with the preferred path separator.

There is no guarantee that two equivalent paths normalize to the same path.
-/
-- TODO: normalize `a/`, `a//b`, etc.
def normalize (p : FilePath) : FilePath := Id.run do
  let mut p := p
  -- normalize drive letter
  if isWindows && p.toString.length >= 2 && (p.toString.get 0).isLower && p.toString.get ⟨1⟩ == ':' then
    p := ⟨p.toString.set 0 (p.toString.get 0).toUpper⟩
  -- normalize separator
  unless pathSeparators.length == 1 do
    p := ⟨p.toString.map fun c => if pathSeparators.contains c then pathSeparator else c⟩
  return p

-- the following functions follow the names and semantics from Rust's `std::path::Path`

/--
An absolute path starts at the root directory or a drive letter. Accessing files through an absolute
path does not depend on the current working directory.
-/
def isAbsolute (p : FilePath) : Bool :=
  pathSeparators.contains p.toString.front || (isWindows && p.toString.length > 1 && p.toString.iter.next.curr == ':')

/--
A relative path is one that depends on the current working directory for interpretation. Relative
paths do not start with the root directory or a drive letter.
-/
def isRelative (p : FilePath) : Bool :=
  !p.isAbsolute

/--
Appends two paths, taking absolute paths into account. This operation is also accessible via the `/`
operator.

If `sub` is an absolute path, then `p` is discarded and `sub` is returned. If `sub` is a relative
path, then it is attached to `p` with the platform-specific path separator.
-/
def join (p sub : FilePath) : FilePath :=
  if sub.isAbsolute then
    sub
  else
    ⟨p.toString ++ pathSeparator.toString ++ sub.toString⟩

instance : Div FilePath where
  div := FilePath.join

instance : HDiv FilePath String FilePath where
  hDiv p sub := FilePath.join p ⟨sub⟩

private def posOfLastSep (p : FilePath) : Option String.Pos :=
  p.toString.revFind pathSeparators.contains

/--
Returns the parent directory of a path, if there is one.

If the path is that of the root directory or the root of a drive letter, `none` is returned.
Otherwise, the path's parent directory is returned.
-/
def parent (p : FilePath) : Option FilePath :=
  let extractParentPath := FilePath.mk <$> p.toString.extract {} <$> posOfLastSep p
  if p.isAbsolute then
    let lengthOfRootDirectory := if pathSeparators.contains p.toString.front then 1 else 3
    if p.toString.length == lengthOfRootDirectory then
      -- `p` is a root directory
      none
    else if posOfLastSep p == String.Pos.mk (lengthOfRootDirectory - 1) then
      -- `p` is a direct child of the root
      some ⟨p.toString.extract 0 ⟨lengthOfRootDirectory⟩⟩
    else
      -- `p` is an absolute path with at least two subdirectories
      extractParentPath
  else
    -- `p` is a relative path
    extractParentPath

/--
Extracts the last element of a path if it is a file or directory name.

Returns `none ` if the last entry is a special name (such as `.` or `..`) or if the path is the root
directory.
-/
def fileName (p : FilePath) : Option String :=
  let lastPart := match posOfLastSep p with
    | some sepPos => p.toString.extract (sepPos + '/') p.toString.endPos
    | none        => p.toString
  if lastPart.isEmpty || lastPart == "." || lastPart == ".." then none else some lastPart

/--
Extracts the stem (non-extension) part of `p.fileName`.

If the filename contains multiple extensions, then only the last one is removed. Returns `none` if
there is no file name at the end of the path.

Examples:
 * `("app.exe" : System.FilePath).fileStem = some "app"`
 * `("file.tar.gz" : System.FilePath).fileStem = some "file.tar"`
 * `("files/" : System.FilePath).fileStem = none`
 * `("files/picture.jpg" : System.FilePath).fileStem = some "picture"`
-/
def fileStem (p : FilePath) : Option String :=
  p.fileName.map fun fname =>
    match fname.revPosOf '.' with
    | some ⟨0⟩ => fname
    | some pos => fname.extract 0 pos
    | none     => fname

/--
Extracts the extension part of `p.fileName`.

If the filename contains multiple extensions, then only the last one is extracted. Returns `none` if
there is no file name at the end of the path.

Examples:
 * `("app.exe" : System.FilePath).extension = some "exe"`
 * `("file.tar.gz" : System.FilePath).extension = some "gz"`
 * `("files/" : System.FilePath).extension = none`
 * `("files/picture.jpg" : System.FilePath).extension = some "jpg"`
-/
def extension (p : FilePath) : Option String :=
  p.fileName.bind fun fname =>
    match fname.revPosOf '.' with
    | some 0   => none
    | some pos => fname.extract (pos + '.') fname.endPos
    | none     => none

/--
Replaces the file name at the end of the path `p` with `fname`, placing `fname` in the parent
directory of `p`.

If `p` has no parent directory, then `fname` is returned unmodified.
-/
def withFileName (p : FilePath) (fname : String) : FilePath :=
  match p.parent with
  | none => ⟨fname⟩
  | some p => p / fname

/--
Appends the extension `ext` to a path `p`.

`ext` should not have leading `.`, as this function adds one. If `ext` is the empty string, no
`.` is added.

Unlike `System.FilePath.withExtension`, this does not remove any existing extension.
-/
def addExtension (p : FilePath) (ext : String) : FilePath :=
  match p.fileName with
  | none => p
  | some fname => p.withFileName (if ext.isEmpty then fname else fname ++ "." ++ ext)

/--
Replaces the current extension in a path `p` with `ext`, adding it if there is no extension. If the
path has multiple file extensions, only the last one is replaced. If the path has no filename, or if
`ext` is the empty string, then the filename is returned unmodified.

`ext` should not have a leading `.`, as this function adds one.

Examples:
* `("files/picture.jpeg" : System.FilePath).withExtension "jpg" = ⟨"files/picture.jpg"⟩`
* `("files/" : System.FilePath).withExtension "zip" = ⟨"files/"⟩`
* `("files" : System.FilePath).withExtension "zip" = ⟨"files.zip"⟩`
* `("files/archive.tar.gz" : System.FilePath).withExtension "xz" = ⟨"files.tar.xz"⟩`
-/
def withExtension (p : FilePath) (ext : String) : FilePath :=
  match p.fileStem with
  | none => p
  | some stem => p.withFileName (if ext.isEmpty then stem else stem ++ "." ++ ext)

/--
Splits a path into a list of individual file names at the platform-specific path separator.
-/
def components (p : FilePath) : List String :=
  p.normalize |>.toString.splitOn pathSeparator.toString

end FilePath

/--
Constructs a path from a list of file names by interspersing them with the current platform's path
separator.
-/
def mkFilePath (parts : List String) : FilePath :=
  ⟨String.intercalate FilePath.pathSeparator.toString parts⟩

instance : Coe String FilePath where
  coe := FilePath.mk

abbrev SearchPath := List FilePath

namespace SearchPath

/--
The character that is used to separate the entries in the `$PATH` (or `%PATH%`) environment variable.

This value is platform dependent.
-/
protected def separator : Char :=
  if isWindows then ';' else ':'

/--
Separates the entries in the `$PATH` (or `%PATH%`) environment variable by the current
platform-dependent separator character.
-/
def parse (s : String) : SearchPath :=
  s.split (fun c => SearchPath.separator == c) |>.map FilePath.mk

/--
Joins a list of paths into a suitable value for the current platform's `$PATH` (or `%PATH%`)
environment variable.
-/
def toString (path : SearchPath) : String :=
  SearchPath.separator.toString.intercalate (path.map FilePath.toString)

end SearchPath

end System
