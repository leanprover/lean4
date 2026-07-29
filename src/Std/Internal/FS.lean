/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Init.System.IO
public import Init.Data.ByteArray
public import Init.Data.SInt

public section

namespace Std.Internal.FS

/--
A point in time, split into whole seconds and nanoseconds since the Unix epoch.
-/
structure Timespec where
  sec : Int64
  nsec : Int64
deriving Repr, Inhabited

/--
The metadata the operating system reports for a filesystem entry, in the shape it reports it.
Higher layers translate this into `Std.FS.Metadata`.
-/
structure Stat where
  dev : UInt64
  mode : UInt64
  nlink : UInt64
  uid : UInt64
  gid : UInt64
  rdev : UInt64
  ino : UInt64
  size : UInt64
  blksize : UInt64
  blocks : UInt64
  flags : UInt64
  gen : UInt64
  atim : Timespec
  mtim : Timespec
  ctim : Timespec
  birthtim : Timespec
deriving Repr, Inhabited

/--
The statistics the operating system reports for a whole filesystem, in the shape it reports them
(reserved slots are omitted). Higher layers translate this into `Std.FS.FileSystemStats`.
-/
structure StatFS where
  type : UInt64
  blockSize : UInt64
  blocks : UInt64
  blocksFree : UInt64
  blocksAvailable : UInt64
  files : UInt64
  filesFree : UInt64
deriving Repr, Inhabited

private opaque FileImpl : NonemptyType.{0}

/--
A handle to an open file.
-/
def File : Type := FileImpl.type

instance : Nonempty File := FileImpl.property

/--
Compute the flag bitmask that `openFile` expects for the given open-mode booleans. `createNew`
implies `create`.

This is not pure bit arithmetic over portable constants: the individual flags have different numeric
values on different platforms, so the translation is done by the runtime for whichever platform it
was compiled on.
-/
@[extern "lean_uv_fs_open_flags"]
opaque openFlags (read write append truncate create createNew : Bool) : UInt32

/--
Open the file at `path` with the given `flags` (see `openFlags`) and the permissions `mode` to give
it if it is created.
-/
@[extern "lean_uv_fs_open"]
opaque openFile (path : @& String) (flags : UInt32) (mode : UInt32) : IO File

/--
Close `file`, releasing the handle.
-/
@[extern "lean_uv_fs_close"]
opaque close (file : @& File) : IO Unit

/--
Read up to `len` bytes from `file` starting at `offset`, where `-1` reads from the current cursor,
into `buf`, growing it if needed, and return the filled slice (use the return value, not `buf`, after
the call). A shorter result indicates end-of-file.

If `buf` is uniquely owned (no other references to it), its backing storage is reused and mutated in
place instead of allocating a new one; if it is shared, a fresh `ByteArray` is allocated and `buf` is
left untouched.
-/
@[extern "lean_uv_fs_read"]
opaque read (file : @& File) (len : USize) (offset : Int64) (buf : ByteArray) : IO ByteArray

/--
Write `data` to `file` starting at `offset`, where `-1` writes at the current cursor, returning the
number of bytes written.
-/
@[extern "lean_uv_fs_write"]
opaque write (file : @& File) (data : @& ByteArray) (offset : Int64) : IO USize

/--
Flush all buffered data and metadata of `file` to the storage device.
-/
@[extern "lean_uv_fs_fsync"]
opaque syncAll (file : @& File) : IO Unit

/--
Flush buffered data of `file`, but not necessarily its metadata.
-/
@[extern "lean_uv_fs_fdatasync"]
opaque syncData (file : @& File) : IO Unit

/--
Truncate or extend `file` to exactly `len` bytes.
-/
@[extern "lean_uv_fs_ftruncate"]
opaque setLength (file : @& File) (len : UInt64) : IO Unit

/--
Return the metadata of the open file `file`.
-/
@[extern "lean_uv_fs_fstat"]
opaque fileMetadata (file : @& File) : IO Stat

/--
Change the permission bits of `file`.
-/
@[extern "lean_uv_fs_fchmod"]
opaque setFilePermissions (file : @& File) (mode : UInt32) : IO Unit

/--
Change the owner and group of `file`.
-/
@[extern "lean_uv_fs_fchown"]
opaque setFileOwner (file : @& File) (uid gid : UInt32) : IO Unit

/--
Set the access and modification times of `file`, in seconds since the Unix epoch.
-/
@[extern "lean_uv_fs_futime"]
opaque setFileTimes (file : @& File) (atime mtime : Float) : IO Unit

/--
Copy up to `length` bytes from `inFile`, starting at `inOffset`, to `outFile`, returning the number
of bytes actually copied. Uses the operating system's copy acceleration where it has any.
-/
@[extern "lean_uv_fs_sendfile"]
opaque sendFile (outFile inFile : @& File) (inOffset : Int64) (length : USize) : IO USize

/--
Acquire an advisory lock on `file`, blocking until it is available. `exclusive` selects an exclusive
(write) lock over a shared (read) lock.
-/
@[extern "lean_uv_fs_lock"]
opaque lock (file : @& File) (exclusive : Bool) : IO Unit

/--
Try to acquire an advisory lock on `file` without blocking, returning `false` if it is already held.
-/
@[extern "lean_uv_fs_trylock"]
opaque tryLock (file : @& File) (exclusive : Bool) : IO Bool

/--
Release the advisory lock held on `file`.
-/
@[extern "lean_uv_fs_unlock"]
opaque unlock (file : @& File) : IO Unit

/--
Copy the file at `src` to `dst`. `flags` selects between the platform's copy behaviours.
-/
@[extern "lean_uv_fs_copyfile"]
opaque copyFile (src dst : @& String) (flags : UInt32) : IO Unit

/--
Delete the file at `path`.
-/
@[extern "lean_uv_fs_unlink"]
opaque removeFile (path : @& String) : IO Unit

/--
Rename or move `src` to `dst`.
-/
@[extern "lean_uv_fs_rename"]
opaque rename (src dst : @& String) : IO Unit

/--
Create a hard link `link` pointing at the existing file `path`.
-/
@[extern "lean_uv_fs_link"]
opaque hardLink (path link : @& String) : IO Unit

/--
Create a symbolic link `path` pointing at `target`. `flags` carries the bits that Windows needs to
distinguish a link to a directory; they are ignored elsewhere.
-/
@[extern "lean_uv_fs_symlink"]
opaque createSymlink (target path : @& String) (flags : UInt32) : IO Unit

/--
Read the target of the symbolic link `path` without resolving it.
-/
@[extern "lean_uv_fs_readlink"]
opaque readSymlink (path : @& String) : IO String

/--
Change the permission bits of `path`, following symlinks.
-/
@[extern "lean_uv_fs_chmod"]
opaque setPermissions (path : @& String) (mode : UInt32) : IO Unit

/--
Change the owner and group of `path`, following symlinks.
-/
@[extern "lean_uv_fs_chown"]
opaque setOwner (path : @& String) (uid gid : UInt32) : IO Unit

/--
Change the owner and group of the symlink `path` itself.
-/
@[extern "lean_uv_fs_lchown"]
opaque setSymlinkOwner (path : @& String) (uid gid : UInt32) : IO Unit

/--
Set the access and modification times of `path`, in seconds since the Unix epoch.
-/
@[extern "lean_uv_fs_utime"]
opaque setTimes (path : @& String) (atime mtime : Float) : IO Unit

/--
Set the access and modification times of the symlink `path` itself, without following it, in seconds
since the Unix epoch.
-/
@[extern "lean_uv_fs_lutime"]
opaque setSymlinkTimes (path : @& String) (atime mtime : Float) : IO Unit

/--
Return the metadata of `path`, following symlinks.
-/
@[extern "lean_uv_fs_stat"]
opaque metadata (path : @& String) : IO Stat

/--
Return the metadata of `path` without following the final symlink.
-/
@[extern "lean_uv_fs_lstat"]
opaque symlinkMetadata (path : @& String) : IO Stat

/--
Return filesystem-level statistics (total/free space, entry counts) for the filesystem containing
`path`.
-/
@[extern "lean_uv_fs_statfs"]
opaque filesystemStats (path : @& String) : IO StatFS

/--
Test whether `path` is accessible in the ways `mode` selects (existence, and readability,
writability or executability), returning whether the check succeeds.
-/
@[extern "lean_uv_fs_access"]
opaque access (path : @& String) (mode : UInt32) : IO Bool

/--
Create and open a uniquely named temporary file derived from `template`, returning the open file and
the path that was created.
-/
@[extern "lean_uv_fs_mkstemp"]
opaque createTempFile (template : @& String) : IO (File × String)

end Std.Internal.FS
