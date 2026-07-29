/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.FS.Types
public import Std.FS.File
public import Std.FS.Dir

/-!
# Filesystem Library

A filesystem library for Lean. It provides handle-based file access, whole-file convenience helpers,
and the metadata and permission types shared across them.

## Overview

- `File` — an open file, a thin unbuffered wrapper around an OS file handle.
- `Dir` / `DirEntry` — an open directory and the entries read from it.
- `Metadata` / `FileType` / `FileRight` — the values that describe a filesystem entry.

Two parallel styles are offered throughout: **handle-based** operations that act on an already-open
`File`, and **path-keyed** operations that take a `Path` and perform the open/close internally.
Whole-file helpers like `readFile` and `writeFile` belong to the latter; methods like `File.readAt`
to the former.

Operations that come in a text and a bytes flavour name the bytes one `Bin` and leave the text one
unmarked when the text flavour is the common case (`readFile`/`readBinFile`), and mark the text one
`String` when the bytes flavour is (`File.readToEnd`/`File.readStringToEnd`). Text always means
UTF-8, and decoding fails on invalid input.

**Threading model**: `File` is *not* thread-safe by default and carries no built-in lock. Concurrent
access must be synchronized explicitly with `Mutex`. For cross-process coordination, `File` exposes
advisory locks (`File.lock`, `File.tryLock`, `File.withLock`).

## Reading and Writing Whole Files

The simplest operations read or write a file in one call, opening and closing it internally. `lines`
is the exception: it hands back an iterator that reads as it is stepped, so a large file never has to
be held in memory at once.

```lean
import Std.FS

open Std.FS

def main : IO Unit := do
  -- Read an entire UTF-8 file
  let contents ← readFile "config.txt"

  -- Read raw bytes
  let bytes ← readBinFile "image.png"

  -- Iterate the lines without holding the whole file in memory
  for line in ← lines "data.csv" do
    IO.println line

  -- Write (creating or truncating)
  writeFile "out.txt" "Hello, World!\n"
  writeBinFile "out.bin" bytes

  -- Append (creating if missing)
  appendFile "log.txt" "another line\n"
  appendBinFile "out.bin" bytes
```

## Working with Open Files

For finer control — streaming, positioned I/O, syncing, locking — open a `File` directly. Prefer
`File.withFile`, which closes the file in a `finally` block:

```lean
def copyFirstKb (src dst : Path) : IO Unit :=
  File.withFile src .readOnly fun input => do
    let chunk ← input.readAt 0 1024 (ByteArray.emptyWithCapacity 1024)
    File.withFile dst .writeCreate fun output =>
      output.write chunk
```

Files are opened with an `OpenMode`. Common modes are provided as `OpenMode.readOnly`,
`OpenMode.readWrite`, `OpenMode.writeCreate`, and `OpenMode.appendCreate`; the structure can also be
built field-by-field, with raw OS flags supplied via `OpenMode.custom`.

```lean
-- Open an existing file read-only (the default)
let file ← File.open "data.txt"

-- Open for appending, creating the file with the given permissions if it is missing
let file ← File.open "log.txt" .appendCreate .default

-- Create for writing, truncating an existing file
let file ← File.create "out.txt"
```

### Positioned vs. Cursor I/O

`File` supports both cursor-relative and positioned access. `readAt`/`writeAt` use an explicit
`offset` (`pread`/`pwrite`) and do not move the cursor, while `read`, `write`, `putStr`, and
`putStrLn` operate at the current cursor position:

```lean
File.withFile "out.txt" .readWrite fun file => do
  file.putStrLn "line one"           -- writes at the cursor
  file.writeAt 0 "X".toUTF8           -- overwrites byte 0, cursor unchanged
  file.setLength 100                  -- truncate or extend to 100 bytes
```

Both styles are also available through the `Std.IO` classes: `File` implements `Read`/`Write` (the
OS cursor) as well as `ReadAt`/`WriteAt`/`Size` (absolute offsets), so a `Std.IO.Cursor File` gives
sequential access driven by its own position rather than the descriptor's.

### Durability

Closing a file does **not** flush to disk. When durability matters, call `File.syncAll` (`fsync`,
data and metadata) or the cheaper `File.syncData` (`fdatasync`, data only) before closing.

### Advisory Locking

`File` exposes cross-process advisory locks. Use `File.withLock` to hold a lock for the duration of
an action:

```lean
File.withFile "shared.db" .readWrite fun file =>
  file.withLock (exclusive := true) do
    -- excludes other processes that lock this file for this block
    pure ()
```

The locks are advisory: a process that never locks the file can still read and write it.

## Directories

`readDir` lists one level of a directory, `readDirSorted` does the same in name order, and `walk`
descends recursively. All three produce `DirEntry` values, which name one entry within a parent
directory and answer `path`, `fileType`, and `metadata` about it.

```lean
for entry in ← readDir "src" do
  IO.println (← entry.path.toString)

-- Recursively, descending into subdirectories as they are reached
for entry in ← walk "src" do
  if (← entry.fileType) == .file then
    IO.println (← entry.path.toString)

-- Recursively, keeping only the paths matching a glob
let sources ← glob "src" "**/*.lean"
```

`walk` yields symlinks without following them, so a traversal cannot cycle. Passing
`ignoreErrors := true` skips subdirectories that cannot be read (e.g. permission denied) rather than
aborting the whole walk; the same flag is accepted by `removeDirAll` and `copyDir`.

For step-by-step control, open a `Dir` and read from it directly. Entries arrive one at a time, so a
directory with very many entries never has to be held in memory at once:

```lean
Dir.withDir "src" fun dir => do
  while let some entry ← dir.next do
    IO.println entry.fileName
```

Directories are created with `createDir` (the parent must exist) or `createDirAll` (which creates
the whole chain), and removed with `removeDir` (which requires them to be empty) or `removeDirAll`.
`copyDir` copies a tree, and `isDir` checks a path without throwing.

## Metadata and Permissions

`metadata` returns a `Metadata` record (size, timestamps, type, permission bits, and platform-
dependent fields like `inode` and `uid`). `metadata` follows symlinks; `symlinkMetadata` reports on
the link itself. Open files expose `File.metadata`, which avoids the TOCTOU window of the path-keyed
query.

```lean
let md ← metadata "data.txt"
IO.println s!"{md.byteSize} bytes, type {repr md.type}"
```

Permissions are modeled by `FileRight` (owner/group/other, each an `AccessRight` of
read/write/execute). Defaults `FileRight.default` (`0o644`) and `FileRight.defaultDir` (`0o755`) are
provided. Read and set them via `getPermissions`/`setPermissions` (by path or on an open `File`), and
adjust timestamps with `setTimes`.

For existence checks that never throw, `isFile`, `isSymlink`, and `pathExists` return `false` on any
error.

## Structural Operations, Links, and Temporary Files

Path-keyed mutations live alongside the `File` type: `copyFile`, `rename`, `removeFile`, `hardLink`,
`truncate`, and ownership changes (`chown`, `lchown`). Symlinks are created with `createSymlink` and
inspected, without resolving, via `readSymlink` (contrast `Path.resolve`, which follows the full
chain).

Temporary files and directories are created securely and cleaned up with the `with*` helpers:

```lean
File.withTempFile fun file path => do
  file.putStrLn "scratch data"
  -- file is deleted when this block exits

withTempDir fun dir => do
  writeFile (dir / path("scratch.txt")) "scratch data"
  -- dir is removed, along with its contents, when this block exits
```
-/
