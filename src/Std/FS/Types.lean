/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Init.Data.ByteArray
public import Init.System.IO
public import Std.Time

public section

/-!
# FS Core Types

Core value types shared across `Std.FS`: file types, open modes, permission bits, and metadata.

These are value types rather than handles; the IO operations that consume them live in the other
`Std.FS` modules. See issue #13922 for the path side of this redesign.
-/

open Std.Time

namespace Std.FS

/--
The kind of a filesystem entry.

`unknown` is used when the OS does not report a type (e.g. some network filesystems), in which case
querying the entry's metadata directly is required to resolve it.
-/
inductive FileType where

  /--
  A regular file.
  -/
  | file

  /--
  A directory.
  -/
  | dir

  /--
  A symbolic link.
  -/
  | symlink

  /--
  A block device (e.g. a disk).
  -/
  | blockDevice

  /--
  A character device (e.g. `/dev/null`).
  -/
  | charDevice

  /--
  A named pipe (FIFO).
  -/
  | fifo

  /--
  A Unix domain socket.
  -/
  | socket

  /--
  The type was not reported by the OS (e.g. some network filesystems).
  -/
  | unknown
deriving Inhabited, BEq, Repr, DecidableEq

namespace FileType

/--
Read the entry kind out of a raw file mode, as reported by the metadata queries.
-/
@[extern "lean_uv_fs_file_type_of_mode"]
opaque ofMode (mode : UInt64) : FileType

end FileType

/--
How a file is opened. Combines the predefined flags below with optional raw OS-level flags via
`custom`. The default opens an existing file read-only.
-/
structure OpenMode where

  /--
  Allow reads.
  -/
  read : Bool := true

  /--
  Allow writes.
  -/
  write : Bool := false

  /--
  All writes go to end-of-file; incompatible with `truncate`.
  -/
  append : Bool := false

  /--
  Truncate the file to zero length on open; requires `write`.
  -/
  truncate : Bool := false

  /--
  Create the file if it does not exist.
  -/
  create : Bool := false

  /--
  Create the file, failing if it already exists. The check and the creation happen as one step, so
  this is safe against another process racing to create the same path.
  -/
  createNew : Bool := false

  /--
  Raw OS-level flags, merged with the flags derived from the other fields.
  -/
  custom : Option UInt32 := none
deriving Inhabited, Repr

namespace OpenMode

/--
Open an existing file for reading only.
-/
def readOnly : OpenMode := { read := true }

/--
Open an existing file for reading and writing without truncation.
-/
def readWrite : OpenMode := { read := true, write := true }

/--
Create a file for writing, truncating it if it already exists.
-/
def writeCreate : OpenMode := { write := true, create := true, truncate := true }

/--
Open a file for appending, creating it if necessary.
-/
def appendCreate : OpenMode := { write := true, append := true, create := true }

end OpenMode

/--
The access rights of a single principal (user, group, or other) over a file.
-/
structure AccessRight where

  /--
  The file can be read.
  -/
  read : Bool := false

  /--
  The file can be written to.
  -/
  write : Bool := false

  /--
  The file can be executed.
  -/
  execution : Bool := false
deriving Inhabited, BEq, Repr

/--
The permission bits of a file, split between the owner, the owning group, and everyone else.
-/
structure FileRight where

  /--
  The owner's permissions to access the file.
  -/
  user : AccessRight := {}

  /--
  The assigned group's permissions to access the file.
  -/
  group : AccessRight := {}

  /--
  The permissions that all others have to access the file.
  -/
  other : AccessRight := {}
deriving Inhabited, BEq, Repr

namespace FileRight

/--
Pack the permissions into the raw bit field the OS expects.
-/
def flags (r : FileRight) : UInt32 :=
  let bit (b : Bool) (v : UInt32) : UInt32 := if b then v else 0
  bit r.user.read 0o400 ||| bit r.user.write 0o200 ||| bit r.user.execution 0o100 |||
  bit r.group.read 0o040 ||| bit r.group.write 0o020 ||| bit r.group.execution 0o010 |||
  bit r.other.read 0o004 ||| bit r.other.write 0o002 ||| bit r.other.execution 0o001

/--
Read the permissions out of a raw file mode, as reported by the metadata queries.
-/
def ofMode (mode : UInt64) : FileRight where
  user := { read := mode &&& 0o400 != 0, write := mode &&& 0o200 != 0, execution := mode &&& 0o100 != 0 }
  group := { read := mode &&& 0o040 != 0, write := mode &&& 0o020 != 0, execution := mode &&& 0o010 != 0 }
  other := { read := mode &&& 0o004 != 0, write := mode &&& 0o002 != 0, execution := mode &&& 0o001 != 0 }

/--
The default for a new file: the owner may read and write it, everyone else may only read it.
-/
def default : FileRight where
  user := { read := true, write := true }
  group := { read := true }
  other := { read := true }

/--
The default for a new directory: the owner may read, write and enter it, everyone else may only read
and enter it.
-/
def defaultDir : FileRight where
  user := { read := true, write := true, execution := true }
  group := { read := true, execution := true }
  other := { read := true, execution := true }

end FileRight

/--
Filesystem metadata for a file, directory, or special entry.

Timestamps use `Std.Time.Timestamp`. `creationTime` is `Option` because Linux does not expose a file
creation time. `inode`, `device`, `uid`, and `gid` are `Option` because they are unavailable on some
filesystems (FAT32, network mounts) or platforms (Windows).
-/
structure Metadata where

  /--
  Last access time.
  -/
  accessed : Timestamp

  /--
  Last modification time.
  -/
  modified : Timestamp

  /--
  Creation time, when the platform exposes it.
  -/
  creationTime : Option Timestamp

  /--
  Size of the file in bytes.
  -/
  byteSize : UInt64

  /--
  The kind of entry this metadata describes.
  -/
  type : FileType

  /--
  The number of hard links to the file.
  -/
  numLinks : UInt64

  /--
  The file's permission bits.
  -/
  permissions : FileRight

  /--
  Inode number; `none` on FAT32 and some network filesystems.
  -/
  inode : Option UInt64

  /--
  Device identifier; `none` on FAT32 and some network filesystems.
  -/
  device : Option UInt64

  /--
  Owner user ID; `none` on Windows.
  -/
  uid : Option UInt32

  /--
  Owner group ID; `none` on Windows.
  -/
  gid : Option UInt32
deriving Inhabited, Repr

namespace Metadata

/--
True if both metadata values refer to the same underlying file, compared by `inode` and `device`.

Returns `false` if either value has no inode (e.g. on FAT32).
-/
def sameFile (a b : Metadata) : Bool :=
  match a.inode, a.device, b.inode, b.device with
  | some ai, some ad, some bi, some bd => ai == bi && ad == bd
  | _, _, _, _ => false

end Metadata

/--
Filesystem-level statistics for the filesystem containing a path: total and free space, and inode
counts.
-/
structure FileSystemStats where

  /--
  Filesystem type identifier, as reported by the OS.
  -/
  type : UInt64

  /--
  Fundamental block size, in bytes.
  -/
  blockSize : UInt64

  /--
  Total number of blocks in the filesystem.
  -/
  blocks : UInt64

  /--
  Number of free blocks.
  -/
  blocksFree : UInt64

  /--
  Number of free blocks available to unprivileged users.
  -/
  blocksAvailable : UInt64

  /--
  Total number of file nodes (inodes).
  -/
  files : UInt64

  /--
  Number of free file nodes.
  -/
  filesFree : UInt64
deriving Inhabited, Repr

end Std.FS
