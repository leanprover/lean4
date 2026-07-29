/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.FS.Types
public import Std.Internal.FS
public import Std.IO.Basic
public import Std.IO.Buffered
public import Std.Path
public import Std.Time
public import Init.System.Platform
public import Init.Data.ToString.Macro
public import Init.While
public import Init.Data.Option.BasicAux
public import Init.Data.Iterators.Producers
public import Init.Data.Iterators.Consumers

public section

/-!
# File

`File` is a thin wrapper around an OS file handle with no buffering and no built-in lock. If
locking is needed, wrap with `Mutex` or call `File.lock`. See the `Std.FS` module overview for the
shared threading model.
-/

open Std.Time

namespace Std.FS

private def timestampOfTimespec (t : Internal.FS.Timespec) : Timestamp :=
  Timestamp.ofNanosecondsSinceUnixEpoch (Nanosecond.Offset.ofInt (t.sec.toInt * 1000000000 + t.nsec.toInt))

private def timestampToFloatSeconds (t : Timestamp) : Float :=
  let secs := t.toSecondsSinceUnixEpoch.val
  let f := secs.natAbs.toUInt64.toFloat
  if secs < 0 then -f else f

private def metadataOfStat (s : Internal.FS.Stat) : Metadata where
  accessed := timestampOfTimespec s.atim
  modified := timestampOfTimespec s.mtim
  creationTime := some (timestampOfTimespec s.birthtim)
  byteSize := s.size
  type := FileType.ofMode s.mode
  numLinks := s.nlink
  permissions := FileRight.ofMode s.mode
  inode := some s.ino
  device := some s.dev
  uid := if System.Platform.isWindows then none else some s.uid.toUInt32
  gid := if System.Platform.isWindows then none else some s.gid.toUInt32

private def filesystemStatsOfStatFS (s : Internal.FS.StatFS) : FileSystemStats where
  type := s.type
  blockSize := s.blockSize
  blocks := s.blocks
  blocksFree := s.blocksFree
  blocksAvailable := s.blocksAvailable
  files := s.files
  filesFree := s.filesFree

/--
The directory that the temporary-file helpers below default to: `$TMPDIR`
(falling back to `/tmp`) on POSIX, `%TEMP%`/`%TMP%` (falling back to `C:\Windows\Temp`) on Windows.
-/
def tempDir : IO Path := do
  if System.Platform.isWindows then
    if let some dir ← IO.getEnv "TEMP" then Path.fromString dir
    else if let some dir ← IO.getEnv "TMP" then Path.fromString dir
    else Path.fromString "C:\\Windows\\Temp"
  else
    if let some dir ← IO.getEnv "TMPDIR" then Path.fromString dir
    else Path.fromString "/tmp"

/--
An open file: a thin wrapper around an OS file handle. Not thread-safe by default; concurrent access
must be explicitly synchronized using `Mutex`.
-/
structure File where
  private mk ::
  private toInternal : Internal.FS.File

private def OpenMode.rawFlags (mode : OpenMode) : UInt32 :=
  Internal.FS.openFlags mode.read mode.write mode.append mode.truncate mode.create mode.createNew |||
    mode.custom.getD 0

namespace File

/--
Open a regular file. The default mode opens an existing file read-only; pass a `mode` that creates to
bring the file into existence, in which case `perm` is applied to the new file.

`perm` is an upper bound rather than an exact request: the OS drops any bit the calling process'
permission mask excludes, so a newly created file can end up with fewer rights than were asked for.
Use `setPermissions` afterwards to set them exactly.

Fails if `path` names a directory or any other non-regular entry, such as a device or a FIFO.
-/
def «open» (path : Path) (mode : OpenMode := .readOnly) (perm : FileRight := .default) : IO File := do
  return ⟨← Internal.FS.openFile (← path.toString) mode.rawFlags perm.flags⟩

/--
Create a regular file for writing, truncating it if it already exists, and apply `perm` to it if it
is newly created. As in `File.open`, `perm` is subject to the process' permission mask.
-/
def create (path : Path) (perm : FileRight := .default) : IO File :=
  File.open path .writeCreate perm

/--
Open a file, run `f`, and close the file in a `finally` block. A `mode` that creates the file applies
`FileRight.default`; use `File.open` to choose the permission bits.
-/
def withFile (path : Path) (mode : OpenMode := .readOnly) (f : File → IO α) : IO α := do
  let file ← File.open path mode
  try
    f file
  finally
    Internal.FS.close file.toInternal

/--
Explicitly close the file. Closing does not call `fsync`; use `syncAll` before closing for
durability. Prefer `withFile`, which closes the file however the block is left.
-/
def close (file : File) : IO Unit :=
  Internal.FS.close file.toInternal

/--
Flush data and metadata to the device (`fsync`).
-/
def syncAll (file : File) : IO Unit :=
  Internal.FS.syncAll file.toInternal

/--
Flush data only, skipping metadata (`fdatasync`). Cheaper when durability of timestamps and size is
not required.
-/
def syncData (file : File) : IO Unit :=
  Internal.FS.syncData file.toInternal

/--
Copy up to `length` bytes from `src`, starting at `srcOffset`, into `dst` at its current cursor
position, using the OS's copy acceleration where available (`sendfile`). Returns the number of bytes
actually copied, which is less than `length` when `src` ends first.

Reads from `src` are positional, so its cursor is left alone.
-/
def sendFile (src dst : File) (srcOffset : UInt64) (length : USize) : IO USize :=
  Internal.FS.sendFile dst.toInternal src.toInternal srcOffset.toInt64 length

/--
Acquire a shared or exclusive lock, blocking until it is available.
-/
def lock (file : File) (exclusive : Bool := true) : IO Unit :=
  Internal.FS.lock file.toInternal exclusive

/--
Try to acquire a lock without blocking. Returns `false` immediately if it is held by another process.
-/
def tryLock (file : File) (exclusive : Bool := true) : IO Bool :=
  Internal.FS.tryLock file.toInternal exclusive

/--
Release the lock. Idempotent; succeeds even if no lock is held.
-/
def unlock (file : File) : IO Unit :=
  Internal.FS.unlock file.toInternal

/--
Lock the file, run `action`, and unlock it in a `finally` block.

The lock is advisory, so it only excludes processes that lock the same file too; it does not stop
anyone else from reading or writing the file while `action` runs.
-/
def withLock (file : File) (exclusive : Bool := true) (action : IO α) : IO α := do
  file.lock exclusive
  try
    action
  finally
    file.unlock

/--
Read up to `n` bytes at the current cursor position into `buf`, advancing the cursor past them.
Returns the filled slice; use the return value, not `buf`, after the call. A shorter result than `n`
indicates end-of-file.
-/
def read (file : File) (n : USize) (buf : ByteArray := .empty) : IO ByteArray :=
  Internal.FS.read file.toInternal n (-1) buf

/--
Read up to `n` bytes at `offset` into `buf` without moving the cursor (`pread`). Returns the filled
slice; use the return value, not `buf`, after the call.
-/
def readAt (file : File) (offset : UInt64) (n : USize) (buf : ByteArray := .empty) : IO ByteArray :=
  Internal.FS.read file.toInternal n offset.toInt64 buf

private def utf8OrThrow (caller : String) (bytes : ByteArray) : IO String :=
  match String.fromUTF8? bytes with
  | some s => pure s
  | none => throw <| IO.userError s!"{caller}: contents are not valid UTF-8"

private def readChunkSize : USize := 64 * 1024

/--
Read from the current cursor position to end-of-file, leaving the cursor at the end.
-/
partial def readToEnd (file : File) : IO ByteArray :=
  go .empty
where
  -- Each read appends to `acc` and reuses its storage, so the accumulator grows without copying.
  go (acc : ByteArray) : IO ByteArray := do
    let acc' ← file.read readChunkSize acc
    if acc'.size == acc.size then return acc' else go acc'

/--
Read from `offset` to end-of-file without moving the cursor. Yields no bytes when `offset` is at or
past the end.
-/
partial def readToEndAt (file : File) (offset : UInt64) : IO ByteArray :=
  go offset .empty
where
  go (offset : UInt64) (acc : ByteArray) : IO ByteArray := do
    let acc' ← file.readAt offset readChunkSize acc
    if acc'.size == acc.size then
      return acc'
    else
      go (offset + (acc'.size - acc.size).toUInt64) acc'

/--
Read from the current cursor position to end-of-file and decode the bytes as UTF-8, leaving the
cursor at the end. Fails if the bytes read are not valid UTF-8, which includes the case of a cursor
sitting mid-character.
-/
def readStringToEnd (file : File) : IO String := do
  utf8OrThrow "Std.FS.File.readStringToEnd" (← file.readToEnd)

/--
Read from `offset` to end-of-file and decode the bytes as UTF-8, without moving the cursor. Fails if
the bytes read are not valid UTF-8, which includes the case of an `offset` that falls mid-character.
-/
def readStringToEndAt (file : File) (offset : UInt64) : IO String := do
  utf8OrThrow "Std.FS.File.readStringToEndAt" (← file.readToEndAt offset)

/--
Write `bytes` at `offset` (`pwrite`), retrying until every byte is written.
-/
def writeAt (file : File) (offset : UInt64) (bytes : ByteArray) : IO Unit := do
  let mut pos : Nat := 0
  let mut off := offset
  while pos < bytes.size do
    let n ← Internal.FS.write file.toInternal (bytes.extract pos bytes.size) off.toInt64
    if n == 0 then
      throw <| IO.userError "Std.FS.File.writeAt: write returned 0 bytes"
    pos := pos + n.toNat
    off := off + n.toUInt64

/--
Write `bytes` at the current cursor position, retrying until every byte is written.
-/
def write (file : File) (bytes : ByteArray) : IO Unit := do
  let mut pos : Nat := 0
  while pos < bytes.size do
    let n ← Internal.FS.write file.toInternal (bytes.extract pos bytes.size) (-1)
    if n == 0 then
      throw <| IO.userError "Std.FS.File.write: write returned 0 bytes"
    pos := pos + n.toNat

/--
Write a string to the file at the current cursor position.
-/
def putStr (file : File) (s : String) : IO Unit :=
  file.write s.toUTF8

/--
Write a string followed by a newline to the file at the current cursor position.
-/
def putStrLn (file : File) (s : String) : IO Unit :=
  file.write (s ++ "\n").toUTF8

/--
Truncate or extend the file to exactly `len` bytes.
-/
def setLength (file : File) (len : UInt64) : IO Unit :=
  Internal.FS.setLength file.toInternal len

/--
Return metadata for the open file. Avoids the TOCTOU window of `FS.metadata`.
-/
def metadata (file : File) : IO Metadata := do
  return metadataOfStat (← Internal.FS.fileMetadata file.toInternal)

/--
Return the open file's current permission bits.
-/
def getPermissions (file : File) : IO FileRight := do
  return (← file.metadata).permissions

/--
Set the file's permission bits.
-/
def setPermissions (file : File) (perm : FileRight) : IO Unit :=
  Internal.FS.setFilePermissions file.toInternal perm.flags

/--
Set the file's access and modification timestamps.
-/
def setTimes (file : File) (accessed modified : Timestamp) : IO Unit :=
  Internal.FS.setFileTimes file.toInternal (timestampToFloatSeconds accessed) (timestampToFloatSeconds modified)

/--
Change the owner and group of the open file. On Windows this is a no-op.
-/
def chown (file : File) (uid gid : UInt32) : IO Unit := do
  unless System.Platform.isWindows do
    Internal.FS.setFileOwner file.toInternal uid gid

/-!
`Read`/`Write` drive the OS-level cursor the descriptor already tracks, while `ReadAt`/`WriteAt`
address the file by absolute offset. Wrapping a `File` in a `Std.IO.Cursor` layers a second,
independent position on top of the positional operations; it does not observe or move the OS cursor.
-/

instance : Std.IO.Read IO File where
  read file n buf := File.read file n buf

instance : Std.IO.Write IO File where
  write := File.write

instance : Std.IO.ReadAt IO File where
  readAt file offset n buf := File.readAt file offset n buf

instance : Std.IO.WriteAt IO File where
  writeAt := File.writeAt

instance : Std.IO.Size IO File where
  size file := return (← file.metadata).byteSize

instance : Std.IO.Close IO File where
  close := File.close

/--
The lines of `file`, read lazily from its current cursor position through a `BufferedReader`. See
`Std.IO.BufferedReader.lines` for how lines are delimited and decoded.

The buffering reads ahead, so `file` is left at the end of the last chunk the iterator pulled rather
than at the end of the last line it emitted, and it must stay open for as long as the iterator is
used.
-/
def lines (file : File) : IO (IterM (α := Std.IO.LineIterator IO File) IO String) := do
  return (← Std.IO.BufferedReader.new file File.readChunkSize).lines

end File

/--
Read an entire file into a `ByteArray`.
-/
def readBinFile (path : Path) : IO ByteArray :=
  File.withFile path .readOnly (·.readToEndAt 0)

/--
Read an entire UTF-8 file into a `String`. Fails on invalid UTF-8.
-/
def readFile (path : Path) : IO String := do
  let bytes ← readBinFile path
  match String.fromUTF8? bytes with
  | some s => pure s
  | none => throw <| IO.userError s!"Std.FS.readFile: {← path.toString} is not valid UTF-8"

/--
The lines of the file at `path`, read lazily as the iterator is stepped. See
`Std.IO.BufferedReader.lines` for how lines are delimited and decoded.

The file stays open for as long as the iterator is reachable; to close it at a definite point, open
it yourself and use `File.lines` inside `File.withFile`.
-/
def lines (path : Path) : IO (IterM (α := Std.IO.LineIterator IO File) IO String) := do
  File.lines (← File.open path)

/--
Write bytes to a file, creating or truncating it.
-/
def writeBinFile (path : Path) (contents : ByteArray) : IO Unit :=
  File.withFile path .writeCreate fun file => file.write contents

/--
Write a UTF-8 string to a file, creating or truncating it.
-/
def writeFile (path : Path) (contents : String) : IO Unit :=
  writeBinFile path contents.toUTF8

/--
Append bytes to a file, creating it if it does not exist.
-/
def appendBinFile (path : Path) (contents : ByteArray) : IO Unit :=
  File.withFile path .appendCreate fun file => file.write contents

/--
Append a UTF-8 string to a file, creating it if it does not exist.
-/
def appendFile (path : Path) (contents : String) : IO Unit :=
  appendBinFile path contents.toUTF8

/--
Copy a file from `src` to `dst`.
-/
def copyFile (src dst : Path) : IO Unit := do
  Internal.FS.copyFile (← src.toString) (← dst.toString) 0

/--
Delete a file.
-/
def removeFile (path : Path) : IO Unit := do
  Internal.FS.removeFile (← path.toString)

/--
Rename or move a file or directory.
-/
def rename (src dst : Path) : IO Unit := do
  Internal.FS.rename (← src.toString) (← dst.toString)

/--
Create a hard link at `link` pointing to `orig`. Both paths must be on the same filesystem.
-/
def hardLink (orig link : Path) : IO Unit := do
  Internal.FS.hardLink (← orig.toString) (← link.toString)

/--
Change the owner and group of the file or directory at `path`. Follows symlinks. On Windows this is a
no-op.
-/
def chown (path : Path) (uid gid : UInt32) : IO Unit := do
  unless System.Platform.isWindows do
    Internal.FS.setOwner (← path.toString) uid gid

/--
Like `chown` but operates on the symlink itself rather than its target. On Windows this is a no-op.
-/
def lchown (path : Path) (uid gid : UInt32) : IO Unit := do
  unless System.Platform.isWindows do
    Internal.FS.setSymlinkOwner (← path.toString) uid gid

/--
Truncate or extend the file at `path` to exactly `len` bytes without opening it first. Follows
symlinks.
-/
def truncate (path : Path) (len : UInt64) : IO Unit :=
  File.withFile path { read := false, write := true } fun file => file.setLength len

/--
Create a secure temporary file inside `dir`. The caller is responsible for deleting the file.
-/
def createTempFileIn (dir : Path) : IO (File × Path) := do
  let template := dir / (Path.ofPosixString "lean-XXXXXX").get!
  let (internal, resultPath) ← Internal.FS.createTempFile (← template.toString)
  return (⟨internal⟩, ← Path.fromString resultPath)

/--
Create a secure temporary file in `Std.FS.tempDir`. The caller is responsible for deleting the file.
-/
def createTempFile : IO (File × Path) := do
  createTempFileIn (← tempDir)

/--
Create a temporary file inside `dir`, run `f`, and delete the file in a `finally` block.
-/
def withTempFileIn (dir : Path) (f : File → Path → IO α) : IO α := do
  let (file, path) ← createTempFileIn dir
  try
    f file path
  finally
    file.close
    Internal.FS.removeFile (← path.toString)

/--
Create a temporary file in `Std.FS.tempDir`, run `f`, and delete the file in a `finally` block.
-/
def withTempFile (f : File → Path → IO α) : IO α := do
  withTempFileIn (← tempDir) f

/--
Create a symbolic link at `link` pointing to `target`. `target` is stored verbatim and need not exist
at creation time. The `dir` flag is required on Windows when the target is a directory; on POSIX it is
ignored.
-/
def createSymlink (target link : Path) (dir : Bool := false) : IO Unit := do
  -- The directory flag is a fixed, portable constant.
  let flags : UInt32 := if dir then 1 else 0
  Internal.FS.createSymlink (← target.toString) (← link.toString) flags

/--
Read the raw target of a symbolic link without resolving it. Contrast with `Path.resolve`, which
follows the full chain.
-/
def readSymlink (path : Path) : IO Path := do
  Path.fromString (← Internal.FS.readSymlink (← path.toString))

/--
Return metadata for a path, following symlinks.
-/
def metadata (path : Path) : IO Metadata := do
  return metadataOfStat (← Internal.FS.metadata (← path.toString))

/--
Return metadata for a path without following the final symlink.
-/
def symlinkMetadata (path : Path) : IO Metadata := do
  return metadataOfStat (← Internal.FS.symlinkMetadata (← path.toString))

/--
Return `true` if the path exists and is a regular file. Returns `false` on any error.
-/
def isFile (path : Path) : BaseIO Bool := do
  match ← (metadata path).toBaseIO with
  | .ok m => pure (m.type == .file)
  | .error _ => pure false

/--
Return `true` if the path is a symbolic link, without following it. Returns `false` on any error.
-/
def isSymlink (path : Path) : BaseIO Bool := do
  match ← (symlinkMetadata path).toBaseIO with
  | .ok m => pure (m.type == .symlink)
  | .error _ => pure false

/--
Return `true` if the path exists as any file type. Returns `false` on any error.
-/
def pathExists (path : Path) : BaseIO Bool := do
  match ← (metadata path).toBaseIO with
  | .ok _ => pure true
  | .error _ => pure false

/--
Return permission bits by path. Follows symlinks.
-/
def getPermissions (path : Path) : IO FileRight := do
  return (← metadata path).permissions

/--
Set permission bits by path. Follows symlinks.
-/
def setPermissions (path : Path) (perm : FileRight) : IO Unit := do
  Internal.FS.setPermissions (← path.toString) perm.flags

/--
Set both access and modification timestamps by path.
-/
def setTimes (path : Path) (accessed modified : Timestamp) : IO Unit := do
  Internal.FS.setTimes (← path.toString) (timestampToFloatSeconds accessed) (timestampToFloatSeconds modified)

/--
Like `setTimes` but operates on the symlink itself rather than its target.
-/
def setSymlinkTimes (path : Path) (accessed modified : Timestamp) : IO Unit := do
  Internal.FS.setSymlinkTimes (← path.toString) (timestampToFloatSeconds accessed) (timestampToFloatSeconds modified)

/--
Return filesystem-level statistics (total/free space, inode counts) for the filesystem containing
`path`.
-/
def fileSystemStats (path : Path) : IO FileSystemStats := do
  return filesystemStatsOfStatFS (← Internal.FS.filesystemStats (← path.toString))

end Std.FS
