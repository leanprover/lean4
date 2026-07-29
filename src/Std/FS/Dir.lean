/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.FS.Types
public import Std.FS.File
public import Std.Internal.FS
public import Std.IO.Basic
public import Std.Path
public import Init.Data.Array.QSort.Basic
public import Init.Data.Iterators.Producers
public import Init.Data.Iterators.Consumers
public import Init.While

public section

/-!
# Directories

`Dir` is a thin wrapper around an open directory stream, the counterpart of `File` for the entries of
a directory rather than the bytes of a file. It is stepped one entry at a time with `Dir.next` or
driven as an iterator with `Dir.iter`; `walk` layers a recursive traversal on top. Alongside them sit
the path-keyed operations that create, list, and remove directories.
-/

namespace Std.FS

/--
An open directory stream. Not thread-safe by default; concurrent access must be explicitly
synchronized using `Mutex`.
-/
structure Dir where
  private mk ::
  private toInternal : Internal.FS.Dir

  /--
  The path the directory was opened at.
  -/
  path : Path

/--
A single entry of a directory. Entries are produced by reading a directory and describe one name
within it, not the whole path; `DirEntry.path` re-attaches the directory the entry came from.
-/
structure DirEntry where
  private mk ::

  /--
  The directory the entry was read from.
  -/
  parent : Path

  /--
  The entry's name within `parent`.
  -/
  fileName : Path.Filename

  /--
  The entry kind the directory read reported, or `unknown` when the filesystem does not track types.
  Resolved by `DirEntry.fileType`.
  -/
  private reportedType : FileType

namespace DirEntry

/--
The full path of the entry.
-/
def path (entry : DirEntry) : Path :=
  entry.parent / entry.fileName

/--
The entry's kind, without following symlinks: a symlink reports `symlink` rather than the kind of
its target.

Most filesystems report the kind as part of the directory read, in which case this is free. Where
they do not, it falls back to querying the entry, which can fail if the entry has since been removed.
-/
def fileType (entry : DirEntry) : IO FileType := do
  if entry.reportedType matches .unknown then
    return (← symlinkMetadata entry.path).type
  else
    return entry.reportedType

/--
Whether the entry is a directory rather than a symlink pointing at one.
-/
def isDir (entry : DirEntry) : IO Bool := do
  return (← entry.fileType) matches .dir

/--
Full metadata for the entry, following symlinks. Prefer `fileType` when only the kind is needed,
since that usually avoids a query.
-/
def metadata (entry : DirEntry) : IO Metadata :=
  Std.FS.metadata entry.path

end DirEntry

/--
Implementation detail: the state behind the iterator returned by `Dir.iter`.
-/
structure DirIterator where

  /--
  The directory the entries are pulled from. All the position state lives in the stream itself, so
  stepping the iterator leaves this unchanged.
  -/
  private dir : Dir

namespace Dir

/--
Open a directory for reading its entries. Fails if `path` does not name a directory.
-/
def «open» (path : Path) : IO Dir := do
  return ⟨← Internal.FS.openDir (← path.toString), path⟩

/--
Open a directory, run `f`, and close the directory in a `finally` block.
-/
def withDir (path : Path) (f : Dir → IO α) : IO α := do
  let dir ← Dir.open path
  try
    f dir
  finally
    Internal.FS.closeDir dir.toInternal

/--
Explicitly close the directory stream. Prefer `withDir`, which closes it however the block is left.
-/
def close (dir : Dir) : IO Unit :=
  Internal.FS.closeDir dir.toInternal

/--
Read the next entry, or `none` once the directory is exhausted. `.` and `..` are never reported, and
the order is whatever the filesystem uses.
-/
def next (dir : Dir) : IO (Option DirEntry) := do
  let some ent ← Internal.FS.readDirEntry dir.toInternal | return none
  let some fileName := Path.Filename.ofString? ent.name
    | throw <| IO.userError s!"Std.FS.Dir.next: {ent.name.quote} is not a valid file name"
  return some ⟨dir.path, fileName, FileType.ofDirentType ent.type⟩

/--
Read every remaining entry into an array.
-/
def drain (dir : Dir) : IO (Array DirEntry) := do
  let mut acc := #[]
  repeat
    let some entry ← dir.next | break
    acc := acc.push entry
  return acc

/--
The entries of `dir`, pulled one at a time as the iterator is stepped. Reads from the stream, so the
directory must stay open for as long as the iterator is used.
-/
def iter (dir : Dir) : IterM (α := DirIterator) IO DirEntry :=
  IterM.mk ⟨dir⟩

/--
Metadata for the directory itself.
-/
def metadata (dir : Dir) : IO Metadata :=
  Std.FS.metadata dir.path

end Dir

@[no_expose]
instance : Iterator DirIterator IO DirEntry where
  IsPlausibleStep _ _ := True
  step it := do
    match ← it.internalState.dir.next with
    | some entry => return .deflate ⟨.yield ⟨it.internalState⟩ entry, trivial⟩
    | none => return .deflate ⟨.done, trivial⟩

instance [Monad n] : IteratorLoop DirIterator IO n := .defaultImplementation

instance : Std.IO.Close IO Dir where
  close := Dir.close

/--
Every entry of a directory, in whatever order the filesystem reports them. Use `readDirSorted` when
the order has to be stable.
-/
def readDir (path : Path) : IO (Array DirEntry) :=
  Dir.withDir path Dir.drain

/--
Like `readDir`, but ordered by entry name.
-/
def readDirSorted (path : Path) : IO (Array DirEntry) := do
  return (← readDir path).qsort (·.fileName.value < ·.fileName.value)

/--
Create a directory. The parent must already exist; use `createDirAll` to create the whole chain.

As in `File.open`, `perm` is an upper bound rather than an exact request: the OS drops any bit the
calling process' permission mask excludes. Use `setPermissions` afterwards to set them exactly.
-/
def createDir (path : Path) (perm : FileRight := .defaultDir) : IO Unit := do
  Internal.FS.createDir (← path.toString) perm.flags

/--
Return `true` if the path exists and is a directory. Returns `false` on any error.
-/
def isDir (path : Path) : BaseIO Bool := do
  match ← (metadata path).toBaseIO with
  | .ok m => pure (m.type matches .dir)
  | .error _ => pure false

/--
Create a directory along with any missing parents, applying `perm` to each directory it creates. A
no-op if the directory already exists.
-/
partial def createDirAll (path : Path) (perm : FileRight := .defaultDir) : IO Unit := do
  if ← isDir path then
    return
  if let some parent := path.parent then
    createDirAll parent perm
  try
    createDir path perm
  catch e =>
    -- Another process may have won the race to create the same directory, which is not a failure.
    unless ← isDir path do
      throw e

/--
Remove an empty directory. Fails if it still has entries; use `removeDirAll` to remove the contents
along with it.
-/
def removeDir (path : Path) : IO Unit := do
  Internal.FS.removeDir (← path.toString)

/--
Run `action`, discarding any exception it throws when `ignoreErrors` is set.
-/
private def runIgnoring (ignoreErrors : Bool) (action : IO Unit) : IO Unit :=
  if ignoreErrors then
    try action catch _ => pure ()
  else
    action

/--
Remove a directory along with everything beneath it. Symlinks are removed rather than followed, so
the trees they point at are left alone.

With `ignoreErrors` set, entries that cannot be removed (e.g. permission denied) are skipped instead
of aborting the removal, which then leaves the directory partially removed.
-/
partial def removeDirAll (path : Path) (ignoreErrors : Bool := false) : IO Unit :=
  runIgnoring ignoreErrors do
    for entry in ← readDir path do
      runIgnoring ignoreErrors do
        if ← entry.isDir then
          removeDirAll entry.path ignoreErrors
        else
          removeFile entry.path
    removeDir path

/--
Recursively copy the directory tree at `src` to `dst`, which must not exist. Files are copied
byte-for-byte and symlinks are recreated verbatim rather than followed. Directories are created with
the permission bits of their counterpart in `src`, subject to the process' permission mask.

With `ignoreErrors` set, entries that cannot be copied are skipped instead of aborting the copy,
which then leaves `dst` incomplete.
-/
partial def copyDir (src dst : Path) (ignoreErrors : Bool := false) : IO Unit :=
  runIgnoring ignoreErrors do
    createDir dst (← metadata src).permissions
    for entry in ← readDir src do
      runIgnoring ignoreErrors do
        let target := dst / entry.fileName
        match ← entry.fileType with
        | .dir => copyDir entry.path target ignoreErrors
        | .symlink => createSymlink (← readSymlink entry.path) target
        | _ => copyFile entry.path target

/--
Implementation detail: the state behind the iterator returned by `walk`.
-/
structure WalkIterator where

  /--
  Directories that have been yielded but not descended into yet, most recently discovered first.
  -/
  private pending : Array Path

  /--
  The entries of the directory currently being yielded from.
  -/
  private current : Array DirEntry

  /--
  Index into `current` of the entry to yield next.
  -/
  private idx : Nat

  /--
  Whether a subdirectory that cannot be read is skipped rather than aborting the walk.
  -/
  private ignoreErrors : Bool

@[no_expose]
instance : Iterator WalkIterator IO DirEntry where
  IsPlausibleStep _ _ := True

  step it := do
    let state := it.internalState
    if h : state.idx < state.current.size then
      let entry := state.current[state.idx]
      -- Only the path is kept, so a walk holds no directory stream open between steps.
      let descend ← if state.ignoreErrors then entry.isDir.toBaseIO.map (·.toOption.getD false) else entry.isDir
      let pending := if descend then state.pending.push entry.path else state.pending
      return .deflate ⟨.yield ⟨{ state with pending, idx := state.idx + 1 }⟩ entry, trivial⟩
    else
      match state.pending.back? with
      | none => return .deflate ⟨.done, trivial⟩
      | some dir =>
        let entries ←
          try
            readDir dir
          catch e =>
            if state.ignoreErrors then pure #[] else throw e
        return .deflate ⟨.skip ⟨{ state with pending := state.pending.pop, current := entries, idx := 0 }⟩, trivial⟩

instance [Monad n] : IteratorLoop WalkIterator IO n := .defaultImplementation

/--
Every entry beneath `dir`, recursively, pulled as the iterator is stepped. Where `Dir.iter` reads a
single level, this descends into each subdirectory it yields. Symlinks are yielded but not followed,
so the traversal cannot cycle.

Each directory is read in full as it is reached, but only one is held open at a time. `dir` itself is
read eagerly, so a `dir` that cannot be read fails here rather than on the first step.

With `ignoreErrors` set, subdirectories that cannot be read are skipped instead of aborting the walk.
-/
def walk (dir : Path) (ignoreErrors : Bool := false) : IO (IterM (α := WalkIterator) IO DirEntry) := do
  let current ← readDir dir
  return IterM.mk { pending := #[], current, idx := 0, ignoreErrors }

/--
Every entry beneath `dir` whose full path matches the `/`-separated glob `pattern`. See
`Path.matchGlob` for the pattern syntax and `walk` for the traversal and `ignoreErrors`.
-/
def glob (dir : Path) (pattern : String) (ignoreErrors : Bool := false) : IO (Array DirEntry) := do
  let mut acc := #[]
  for entry in ← walk dir ignoreErrors do
    if entry.path.matchGlob pattern then
      acc := acc.push entry
  return acc

/--
Create a uniquely named directory inside `dir`. The caller is responsible for removing it.
-/
def createTempDirIn (dir : Path) : IO Path := do
  let template := dir / (Path.ofPosixString "lean-XXXXXX").get!
  Path.fromString (← Internal.FS.createTempDir (← template.toString))

/--
Create a uniquely named directory in `Std.FS.tempDir`. The caller is responsible for removing it.
-/
def createTempDir : IO Path := do
  createTempDirIn (← tempDir)

/--
Create a temporary directory inside `dir`, run `f`, and remove the directory and its contents in a
`finally` block.
-/
def withTempDirIn (dir : Path) (f : Path → IO α) : IO α := do
  let path ← createTempDirIn dir
  try
    f path
  finally
    removeDirAll path

/--
Create a temporary directory in `Std.FS.tempDir`, run `f`, and remove the directory and its contents
in a `finally` block.
-/
def withTempDir (f : Path → IO α) : IO α := do
  withTempDirIn (← tempDir) f

end Std.FS
