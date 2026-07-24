# Summary

This proposal redesigns Lean's FS and Path API using LibUV, replacing a lot of types, making them more complete and removing the `FILE*` dependency in the C++ side. It also adds directory traversals, metadata inspection, some useful functions like copying without reading the entire file into memory and a way to integrate with `Std.Async` in a clean way. This design changes `FS.Handle` and `FS.Stream` to a layer approach with more low-level changes that requires the user to do synchronization and buffering on the Lean side.

Since these things will depend on Std abstractions, it lives under `Std.FS` and `Std.Async.FS`. Path-related changes are tracked separately in issue #13922.

# Migration

A lot of functions are just going to be moved to other namespaces like `IO.FS.readFile` that goes to `Std.FS.readFile`. The `Handle` type will just be split into multiple low level ones like `File`, `Dir`, `Handle` (a smaller version with `uv_pipe_t` and `uv_tty_t`).

| Old                                             | New                                           | Notes                                                  |
| ----------------------------------------------- | --------------------------------------------- | ------------------------------------------------------ |
| `IO.FS.Handle`                                  | `Std.FS.File`                                 | for regular files opened by path                       |
| `IO.FS.Handle`                                  | `Std.FS.Dir`                                  | for regular directories opened by path                 |
| `IO.FS.Handle`                                  | `Std.FS.Handle`                               | for stdin/stdout/stderr and IPC pipes                  |
| `IO.FS.Stream`                                  | `Std.FS.Stream`                               | Keep the abstraction for LSP capture of the Stdout     |
| `IO.getStdin` / `getStdout` / `getStderr`       | `Handle.stdin` / `.stdout` / `.stderr`        | now `Stdin`/`Stdout`/`Stderr`, which have no `close`   |
| `IO.FS.Handle.putStr` / `IO.FS.Handle.putStrLn` | `Std.FS.File.putStr` / `Std.FS.File.putStrLn` | same semantics                                         |
| `IO.FS.Handle.isEof`                            | —                                             | no direct equivalent; `File.readAt` returns empty at EOF |
| `IO.FS.readFile`                                | `Std.FS.readFile`                             | same semantics                                         |
| `IO.FS.writeFile`                               | `Std.FS.writeFile`                            | same semantics                                         |
| `IO.FS.readBinFile`                             | `Std.FS.readBinFile`                          | same semantics                                         |
| `IO.FS.writeBinFile`                            | `Std.FS.writeBinFile`                         | same semantics                                         |
| `IO.FS.lines`                                   | `Std.FS.lines`                                | same semantics                                         |
| `IO.FS.hardLink`                                | `Std.FS.hardLink`                             | same semantics                                         |

## Async Integration

`uv_fs_*` operations can be used asynchronously and synchronously (by specifying a NULL loop and callback), so with a `Std/Async/FS` we can just add operations in the namespace like `.readAsync` that will return a `Promise` instead of blocking. `Std.Async.FS` gives every `Std.FS`/`Std.FS.File` operation an `*Async` counterpart, including path-keyed convenience helpers (`readFileAsync`, `writeFileAsync`, `appendFileAsync`, …), directory operations (`readDirAsync`, `removeDirAllAsync`, `copyDirAsync`, `walkAsync`, `globAsync`), symlinks, metadata/permissions, and temporary files/directories. The full list is in [Async Variants](#async-variants); everything lives in the same `Std.FS` / `Std.FS.File` namespaces as its synchronous counterpart, so the two are used side by side without extra `open`s.

The async variants return `Async α` (over `Std.Async`'s `Promise`), not `IO α`. `Handle`, `Pipe`, and `TTY` get async read/write too — for those the asynchronous form is the *primitive* one, since `uv_read_start`/`uv_write` are natively asynchronous and the synchronous variants are what require extra machinery to emulate. `Dir` and the buffered wrappers have no async counterparts: directory iteration is exposed asynchronously only through the eager path-keyed `readDirAsync`/`walkAsync`.

File locking is the exception: acquiring a contended lock with `flock` (POSIX) or `LockFileEx` (Windows) is a blocking syscall with no libuv equivalent and SHOULDN'T run on the event loop thread, so `File.lockAsync` schedules a dedicated work thread using `uv_queue_work` and resumes a `Promise` once it completes. `File.tryLockAsync` and `File.unlockAsync` are the exception to the exception: a non-blocking `trylock` and releasing a lock never block for an unbounded time, so they run inline rather than needing a work thread. As `flock` is advisory it does not interfere with any of the operations of libuv and thus, is safe to use with another flocks.

`walkAsync`/`globAsync` collect eagerly into an `Array` rather than returning a lazy `IterM`, since `Async` has no lazy-iterator integration yet (unlike the synchronous `FS.walk`, which returns `IterM (α := WalkIterator) IO DirEntry`).

## Concurrency Model

All raw IO types (`File`, `Handle`, `Pipe`, `Dir`) are not thread-safe by default. Concurrency and parallelism safety is achieved through explicit wrappers like `Mutex α` and `RecursiveMutex α`.

# Core Abstractions

## Paths and Filesystem Entries

Path types and path manipulation are specified in issue #13922. This proposal only covers the filesystem abstractions that operate on paths.

- `Dir`: An open directory handle.
- `DirEntry`: A single filesystem entry produced during directory iteration.
- `Metadata`: Filesystem metadata for files, directories, or special entries.
- `FileType`: Enumeration of entry kinds: `file`, `dir`, `symlink`, `blockDevice`, `charDevice`, `fifo`, `socket`, `unknown`.
- `File`: A thin wrapper around `uv_file`. Not thread-safe by default, concurrent access must be explicitly synchronized using `Mutex`.
- `BufferedReader α`: Buffered wrapper around any readable type.
- `BufferedWriter α`: Buffered writer over any writable type.
- `LineWriter α`: A writer wrapper that flushes automatically on newline characters (`\n`). Used by `Stdout`.
- `FilesystemStats`: Filesystem-level statistics (total/free space, inode counts) for the filesystem containing a path.

## Handles and Streams

- `Handle`: A system stream endpoint whose kind (`tty`, `pipe`, or a redirected `file`) is discovered at runtime via `uv_guess_handle`. Exposes only the operations valid for every kind.
- `Pipe`: A `Handle` known by construction to be a `uv_pipe_t`.
- `TTY`: A `Handle` known by construction to be a `uv_tty_t`, adding the terminal-only operations.
- `Stdin` / `Stdout` / `Stderr`: Cached singletons over descriptors 0/1/2, with buffering and *without* a `Close` instance.
- `Stream`: A record of closures that abstracts over any readable/writable endpoint, so stdout can be substituted at runtime.

## Type Classes

- `Read`: Typeclass for types that support sequential, cursor-advancing reads; provides `read : α → (n : USize) → ByteArray → IO ByteArray`, which appends up to `n` bytes after `buf`'s existing content. A result with no bytes appended signals end-of-file. Implemented by `File`, `Handle`, `Pipe`, and `TTY`.
- `Write`: Typeclass for types that support writing bytes; provides `write : α → ByteArray → IO Unit`. Implemented by `File`, `Handle`, `Pipe`, `TTY`, `BufferedWriter α`, and `LineWriter α`.
- `Close`: Typeclass for types that hold a resource that must be released; provides `close : α → IO Unit`. Implemented by `File`, `Dir`, `Handle`, `Pipe`, `TTY`, and the buffered wrappers (`BufferedReader`, `BufferedWriter`, `LineWriter`, which flush before delegating to the inner sink's `close`). Lets generic code release whatever `Read`/`Write` source or sink it was handed without depending on its concrete type. `Stdin`/`Stdout`/`Stderr` deliberately have **no** instance, so no generic cleanup path can close descriptors 0/1/2 — see [Standard Streams](#standard-streams).

# Detailed Explanation

## Iterators

Some operations return `IterM` (defined in `Std/Data/Iterators`) rather than eagerly collected `Array`s.

| Iterator State Type | Element    | Used by     |
| ------------------- | ---------- | ----------- |
| `DirIterator`       | `DirEntry` | `Dir.iter`  |
| `WalkIterator`      | `DirEntry` | `FS.walk` |

## FileType

```lean
inductive FileType where
  | file        -- regular file
  | dir         -- directory
  | symlink     -- symbolic link
  | blockDevice -- block device (e.g. disk)
  | charDevice  -- character device (e.g. /dev/null)
  | fifo        -- named pipe (FIFO)
  | socket      -- Unix domain socket
  | unknown     -- type not reported by the OS (e.g. some network filesystems)
```

| Function                | Type                     | Description                                                                                                   |
| ----------------------- | ------------------------ | ------------------------------------------------------------------------------------------------------------- |
| `FileType.ofDirentType` | `UInt8 → FileType`       | Interpret a raw `uv_dirent_t` type code.                                                                      |
| `FileType.ofStatMode`   | `UInt64 → FileType`      | Interpret the `S_IFMT` bits of a raw POSIX `st_mode`, as returned by `stat`/`lstat`/`fstat`.                  |

## OpenMode

`OpenMode` is a struct specifying how a file is opened. The default value opens an existing file
read-only.

**Fields**

| Field                        | Type           | Default | Description                                                |
| ---------------------------- | -------------- | ------- | ---------------------------------------------------------- |
| `OpenMode.read`              | `Bool`         | `true`  | Allow reads                                                |
| `OpenMode.write`             | `Bool`         | `false` | Allow writes                                               |
| `OpenMode.append`            | `Bool`         | `false` | All writes go to end-of-file; incompatible with `truncate` |
| `OpenMode.truncate`          | `Bool`         | `false` | Truncate to zero on open; requires `write`                 |
| `OpenMode.create`            | `Bool`         | `false` | Create the file if it does not exist (`O_CREAT`)           |
| `OpenMode.createNew`         | `Bool`         | `false` | Create the file, failing if it already exists (`O_CREAT \| O_EXCL`); guarantees exclusive creation |
| `OpenMode.custom`            | `Option USize` | `none`  | Pass raw OS-level flags directly; merged with the flags derived from the other fields. Use when no predefined field covers the required behavior. |

**Presets**

| Name                    | Value                                            | Description                                        |
| ----------------------- | ------------------------------------------------ | -------------------------------------------------- |
| `OpenMode.readOnly`     | `{ read }`                                       | Open an existing file for reading only.            |
| `OpenMode.readWrite`    | `{ read, write }`                                | Open an existing file for reading and writing without truncation. |
| `OpenMode.writeCreate`  | `{ write, create }`                              | Create or open a file for writing.                 |
| `OpenMode.appendCreate` | `{ write, append, create }`                      | Open a file for appending, creating it if necessary. |

`OpenMode.rawFlags : OpenMode → UInt32` computes the `uv_fs_open` flag bitmask, merging in `custom`.
It is public so `Std.Async.FS` can share it rather than re-deriving the bits.

## Permissions

`AccessRight` and `FileRight` keep the same shape as `IO.AccessRight`/`IO.FileRight` in the current API, moved to `Std.FS`.

```lean
structure AccessRight where
  /-- The file can be read. -/
  read      : Bool := false
  /-- The file can be written to. -/
  write     : Bool := false
  /-- The file can be executed. -/
  execution : Bool := false

structure FileRight where
  /-- The owner's permissions to access the file. -/
  user  : AccessRight := {}
  /-- The assigned group's permissions to access the file. -/
  group : AccessRight := {}
  /-- The permissions that all others have to access the file. -/
  other : AccessRight := {}
```

| Name                    | Type                                    | Description                                         |
| ----------------------- | --------------------------------------- | --------------------------------------------------- |
| `FileRight.flags`       | `FileRight → UInt32`                    | Convert to a raw POSIX bit field (for `chmod`, etc.) |
| `FileRight.ofStatMode`  | `UInt64 → FileRight`                    | Interpret the low 9 permission bits of a raw POSIX `st_mode` |
| `FileRight.default`     | `FileRight`                             | `0o644` — owner read/write; group and other read    |
| `FileRight.defaultDir`  | `FileRight`                             | `0o755` — owner read/write/execute; group and other read/execute |

## File Type

`File` is a wrapper around `uv_file` with no buffering and no built-in lock. If buffering or locking is needed, wrap with `Mutex (BufferedWriter File)` or call `File.lock`.

| Function                 | Type                                                                               | Description                                                                                                                                               | Operation                                                     |
| ------------------------ | ---------------------------------------------------------------------------------- | --------------------------------------------------------------------------------------------------------------------------------------------------------- | ------------------------------------------------------------- |
| `File.openExisting`      | `Path → (mode : OpenMode := .readOnly) → IO File`                                  | Open an existing file. Fails if the file does not exist. Default mode is read-only; pass `.readWrite` to open for reading and writing without truncation. | `uv_fs_open`                                                  |
| `File.create`            | `Path → (mode : OpenMode := .writeCreate) → (perm : FileRight := .default) → IO File` | Create or open a file, applying `perm` if it is newly created.                                                                                        | `uv_fs_open`                                                  |
| `File.withFile`          | `Path → (mode : OpenMode := .readOnly) → (File → IO α) → IO α`                     | Open a file, run an action, close in a `finally` block.                                                                                                   |
| `File.close`             | `File → IO Unit`                                                                   | Explicitly close the file. Prefer `withFile` or explicit `close`. Closing does not call `fsync`; use `syncAll` before closing for durability.             | `uv_fs_close`                                                 |
| `File.syncAll`           | `File → IO Unit`                                                                   | Flush data and metadata to the device (`fsync`).                                                                                                          | `uv_fs_fsync`                                                 |
| `File.syncData`          | `File → IO Unit`                                                                   | Flush data only, skipping metadata (`fdatasync`). Cheaper when durability of timestamps/size is not required.                                             | `uv_fs_fdatasync`                                             |
| `File.sendFile`          | `(src dst : File) → (offset : Int64) → (length : USize) → IO USize`                | Copy up to `length` bytes from `src` at `offset` into `dst` using OS copy acceleration. Returns the number of bytes actually copied.                      | `uv_fs_sendfile`                                              |
| `File.lock`              | `File → (exclusive : Bool := true) → IO Unit`                                      | Acquire a shared or exclusive lock, blocking the calling thread until available. (Only `lockAsync` needs `uv_queue_work`, to keep the event loop free.)   | `LockFileEx` on Windows, `flock` on POSIX                     |
| `File.tryLock`           | `File → (exclusive : Bool := true) → IO Bool`                                      | Try to acquire a lock without blocking. Returns `false` immediately if held by another process.                                                           | (`LockFileEx` on Windows, `flock` on POSIX)                   |
| `File.unlock`            | ` File → IO Unit`                                                                  | Release the lock. Idempotent; succeeds even if no lock is held.                                                                                           | `UnlockFileEx` on Windows, `flock` on POSIX                   |
| `File.atomically`        | `File → (exclusive : Bool := true) → IO α → IO α`                                  | Lock, run action, unlock in `finally`. Uses `File.lock`/`File.unlock`.                                                                                    |                                                               |
| `File.read`              | `File → (n : USize) → (buf : ByteArray) → IO ByteArray`                            | Read up to `n` bytes at the current cursor position, advancing it. Bytes are appended after `buf`'s existing content; use the return value, not `buf`, after the call. No bytes appended signals end-of-file. Backs the `Read File` instance. | `uv_fs_read`                                                  |
| `File.readAt`            | `File → (offset : UInt64) → (n : USize) → (buf : ByteArray) → IO ByteArray`        | Read up to `n` bytes at `offset` into `buf` without moving the cursor (`pread`). Returns the filled slice; use the return value, not `buf`, after the call. | `uv_fs_read`                                                  |
| `File.writeAt`           | `File → (offset : UInt64) → ByteArray → IO Unit`                                   | Write at `offset` (`pwrite`), retrying until every byte is written.                                                                                       | `uv_fs_write`                                                 |
| `File.write`             | `File → ByteArray → IO Unit`                                                       | Write at the current cursor position, retrying until every byte is written.                                                                               | `uv_fs_write`                                                 |
| `File.putStr`            | `File → String → IO Unit`                                                          | Write a UTF-8 string at the current cursor position.                                                                                                      |                                                               |
| `File.putStrLn`          | `File → String → IO Unit`                                                          | Write a UTF-8 string followed by `\n` at the current cursor position.                                                                                     |                                                               |
| `File.setLength`         | `File → (len : UInt64) → IO Unit`                                                  | Truncate or extend the file to exactly `len` bytes.                                                                                                       | `uv_fs_ftruncate`                                             |
| `File.metadata`          | `File → IO Metadata`                                                               | Return metadata for the open file. Avoids TOCTOU vs `Path.metadata`.                                                                                      | `uv_fs_fstat`                                                 |
| `File.setPermissions`    | `File → FileRight → IO Unit`                                                     | Set the file's permission bits.                                                                                                                           | `uv_fs_fchmod`                                                |
| `File.setTimes`          | `File → (accessed : Timestamp) → (modified : Timestamp) → IO Unit`                 | Set access and modification timestamps.                                                                                                                   | `uv_fs_futime`                                                |
| `File.chown`             | `File → (uid gid : UInt32) → IO Unit`                                              | Change the owner and group of the open file. On Windows this is a noop.                                                                                   | `uv_fs_fchown`                                                |

## Handle Type

`Handle` is an open stream endpoint whose *kind is discovered at runtime*: `uv_guess_handle(fd)`
reports `UV_TTY`, `UV_NAMED_PIPE`, or `UV_FILE`, and the kind decides which libuv API is legal for it.
A `Handle` therefore exposes exactly the operations valid for every kind — sequential read, write,
close — and nothing more.

**Why `Handle` is not a `File`.** The tempting simplification is that on POSIX everything is a file
descriptor, so `Handle` could just be `File` and `Pipe`/`TTY` could disappear. It does not hold:

- **libuv forbids the mixing.** Regular-file descriptors are always reported ready by `epoll`/`kqueue`,
  so readiness polling is meaningless and libuv does not support files as streams: `uv_read_start` is
  invalid on a `UV_FILE`, and conversely `uv_fs_read` on a terminal bypasses everything `uv_tty_t`
  exists to do. `uv_tty_init` on a non-terminal descriptor returns `EINVAL`.
- **`File`'s API is offset-based; pipes and terminals have no offsets.** `readAt`, `writeAt`,
  `setLength`, and `sendFile` all take an offset, and `pread`/`pwrite` on a pipe or terminal fail with
  `ESPIPE`. So do `ftruncate` and `flock`, and `fstat` reports nothing useful. Collapsing the types
  would produce one whose entire documented surface throws on two of its three kinds.
- **On Windows they are not the same OS object.** `uv_tty_t` wraps a console handle and performs
  UTF-16 conversion, ANSI escape emulation, and virtual-terminal mode handling; a pipe is a Named Pipe
  driven by overlapped I/O; a file is a `HANDLE` for `ReadFile`. The POSIX intuition does not port.

The containment runs one way only: a `File` offers a superset of `Handle`'s operations, never the
reverse. No coercion between them is provided, since it would silently discard the
positioned-vs-cursor distinction.

**Redirected stdio.** `uv_guess_handle` returns `UV_FILE` when stdio is redirected to a regular file
(`./program > out.txt`). The handle then dispatches reads and writes via `uv_fs_read`/`uv_fs_write`
internally, but it stays typed as a `Handle`: the program did not gain the ability to seek or lock its
own stdout just because the shell redirected it.

```lean
inductive HandleKind where
  | file  -- `uv_guess_handle` reported `UV_FILE` (redirected stdio)
  | tty   -- `UV_TTY`
  | pipe  -- `UV_NAMED_PIPE`
```

| Function          | Type                                                      | Description                                                                                                                                                                                               | libuv                          |
| ----------------- | --------------------------------------------------------- | ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ------------------------------ |
| `Handle.ofFd`     | `(fd : UInt32) → (readable : Bool) → IO Handle`            | Adopt an existing descriptor, dispatching on `uv_guess_handle`: `UV_FILE` is kept as a raw descriptor, `UV_TTY` is initialized with `uv_tty_init`, `UV_NAMED_PIPE` with `uv_pipe_init` + `uv_pipe_open`. `UV_TCP`/`UV_UDP` are rejected — those belong to `Std.Async.TCP`/`UDP`. | `uv_guess_handle`              |
| `Handle.kind`     | `Handle → BaseIO HandleKind`                               | The kind reported at construction.                                                                                                                                                                        | `uv_guess_handle`              |
| `Handle.read`     | `Handle → (n : USize) → (buf : ByteArray) → IO ByteArray`  | Read up to `n` bytes into `buf`, reusing its storage in place when `buf` is uniquely owned. Returns the filled slice; use the return value, not `buf`. Returns `buf` truncated to its original size at EOF. | `uv_read_start` / `uv_fs_read` |
| `Handle.write`    | `Handle → ByteArray → IO Unit`                             | Write bytes.                                                                                                                                                                                              | `uv_write` / `uv_fs_write`     |
| `Handle.flush`    | `Handle → IO Unit`                                         | Flush any buffered output. No-op for unbuffered handles.                                                                                                                                                  |                                |
| `Handle.close`    | `Handle → IO Unit`                                         | Close the handle and release resources.                                                                                                                                                                   | `uv_close` / `uv_fs_close`     |
| `Handle.asTTY?`   | `Handle → BaseIO (Option TTY)`                             | Refine to a `TTY` if the kind is `tty`, so the terminal-only operations become available.                                                                                                                 |                                |
| `Handle.asPipe?`  | `Handle → BaseIO (Option Pipe)`                            | Refine to a `Pipe` if the kind is `pipe`.                                                                                                                                                                 |                                |
| `Handle.isTty`    | `Handle → BaseIO Bool`                                     | `kind == .tty`. Retained as a convenience.                                                                                                                                                                | `uv_guess_handle`              |
| `Handle.isPipe`   | `Handle → BaseIO Bool`                                     | `kind == .pipe`.                                                                                                                                                                                          | `uv_guess_handle`              |
| `Handle.isFile`   | `Handle → BaseIO Bool`                                     | `kind == .file`.                                                                                                                                                                                          | `uv_guess_handle`              |

The three predicates are mutually exclusive, hence `kind` is the primitive and they are derived from
it.

`Handle.read`/`write` block the calling thread. For the `tty`/`pipe` kinds the underlying libuv API is
asynchronous (`uv_read_start`/`uv_write`), so the synchronous form is implemented by bridging through a
semaphore that the completion callback posts from the event loop's driver thread. Concurrent
operations on one handle return `EALREADY` rather than interleaving; as with `File`, sharing a
`Handle` across threads requires an explicit `Mutex`.

## Standard Streams

`Handle.stdin`, `Handle.stdout`, and `Handle.stderr` are **cached singletons**, built once from
descriptors 0/1/2. They must not be re-initialized: two `uv_tty_init` calls on descriptor 1 produce two
`uv_tty_t` contending for one console.

They are returned as the distinct types `Stdin`, `Stdout`, and `Stderr`, each wrapping a `Handle` plus
the buffering appropriate to it:

| Type     | Buffering                          | Rationale                                                        |
| -------- | ---------------------------------- | ---------------------------------------------------------------- |
| `Stdin`  | `Mutex (BufferedReader Handle)`    | Read buffering, with `readLine`.                                 |
| `Stdout` | `RecursiveMutex` + line buffering  | Flushes on `\n` so line-oriented output is delivered promptly.    |
| `Stderr` | `Mutex Handle`, unbuffered         | Diagnostics must survive a crash that never reaches a flush.      |

**They deliberately have no `Close` instance**, and therefore no way to close descriptors 0/1/2. This
follows Rust, where `Stdout` is its own type with no `close` method and dropping a handle leaves the
descriptor open — and departs from Go, Python, and Java, which expose `os.Stdout.Close()` /
`sys.stdout.close()` / `System.out.close()` and let a program disable its own output (silently, in
Java's case).

The reason to prefer Rust's answer here is specific to this design: `Close` is a *typeclass*, and the
buffered wrappers close what they wrap — `BufferedWriter.close` and `LineWriter.close` both flush and
then call `Close.close` on the inner sink. If the standard streams were ordinary `Close`-able values,
a single `Close.close` reached through a generic cleanup path would close descriptor 1 for the whole
process, with no line of code naming stdout anywhere. Go and Python are not exposed to this because
they have no such polymorphism; removing the instance removes the possibility at the type level rather
than relying on callers to avoid it.

This is why the buffering above is described by behavior rather than spelled `LineWriter Handle`:
`LineWriter α` and `BufferedWriter α` inherit a `Close` instance from `α`, so the buffering must live
*inside* the newtype rather than the newtype being a type alias for a buffered wrapper.

Closing a standard descriptor remains possible, but only by naming it: `Handle.ofFd 1 (readable :=
false)` yields an ordinary, closable `Handle`. That mirrors Rust's requirement to go through an
explicit owned descriptor. The runtime object additionally carries a no-op-close flag, so an FFI path
that reaches a standard handle by another route still cannot wedge the process's output.

## Pipe and TTY

`Pipe` (`uv_pipe_t`) and `TTY` (`uv_tty_t`) are `Handle`s refined by known kind. They share
`Handle`'s read/write/close and exist as distinct types so that kind-specific operations are available
only where they are meaningful: `TTY.setMode .raw` must not typecheck on a stdout that the shell
redirected to a file.

| Function             | Type                                                    | Description                                                                                                 | libuv                     |
| -------------------- | ------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------- | ------------------------- |
| `Pipe.read`          | `Pipe → (n : USize) → (buf : ByteArray) → IO ByteArray`  | Read up to `n` bytes into `buf`; returns the filled slice.                                                  | `uv_read_start`           |
| `Pipe.write`         | `Pipe → ByteArray → IO Unit`                            | Write bytes to the pipe.                                                                                    | `uv_write`                |
| `Pipe.close`         | `Pipe → IO Unit`                                        | Close the pipe and release its resources.                                                                   | `uv_close`                |
| `TTY.read`           | `TTY → (n : USize) → (buf : ByteArray) → IO ByteArray`   | Read up to `n` bytes into `buf`; returns the filled slice.                                                  | `uv_read_start`           |
| `TTY.write`          | `TTY → ByteArray → IO Unit`                             | Write bytes to the terminal.                                                                                | `uv_write`                |
| `TTY.close`          | `TTY → IO Unit`                                         | Close the terminal handle and release its resources.                                                        | `uv_close`                |
| `TTY.setMode`        | `TTY → TTYMode → IO Unit`                               | Set the terminal input mode.                                                                                | `uv_tty_set_mode`         |
| `TTY.getWinSize`     | `TTY → IO (UInt32 × UInt32)`                            | Return the terminal's width and height in character cells.                                                  | `uv_tty_get_winsize`      |
| `TTY.vtermState`     | `BaseIO VTermState`                                     | Whether the console can process virtual terminal sequences. Process-wide, not per-handle, on Windows.        | `uv_tty_get_vterm_state`  |

```lean
inductive TTYMode where
  | normal  -- initial/normal mode
  | raw     -- raw input mode
  | rawVT   -- raw input mode; on Windows also sets `ENABLE_VIRTUAL_TERMINAL_INPUT`
  | io      -- binary-safe I/O mode for IPC (POSIX only)
```

**Raw mode must be reset at process exit.** `uv_tty_reset_mode` is process-wide and restores the
terminal's original settings; without it a program that enters raw mode and then crashes leaves the
user's shell unusable. A handler registered when raw mode is first entered calls it on exit.

`Pipe` carries no operations of its own for now. libuv offers `uv_pipe_bind2`, `uv_pipe_connect2`,
`uv_pipe_getsockname`/`getpeername`, `uv_pipe_chmod`, and descriptor passing via
`uv_pipe_pending_count`/`pending_type`, but pipe *servers* overlap with what `Std.Async.Process` and
`Std.Async.TCP` already cover; these are deferred until something needs them.

## Stream

`Stream` is a record of closures over any readable/writable endpoint. It stays a closure record rather
than becoming a `[Read α] [Write α]` abstraction because `IO.setStdout : FS.Stream → BaseIO FS.Stream`
replaces the current standard output at runtime with a value of a *different* type — capturing to a
buffer, for instance, which is how the language server intercepts stdout. That requires an
existential, which the closure record provides and typeclass polymorphism does not.

| Field          | Type                                       | Description                                                     |
| -------------- | ------------------------------------------ | ---------------------------------------------------------------- |
| `Stream.flush` | `IO Unit`                                  | Flush the stream's output buffers.                              |
| `Stream.read`  | `USize → (buf : ByteArray) → IO ByteArray` | Read up to the given number of bytes into `buf`; an empty result signals EOF. |
| `Stream.write` | `ByteArray → IO Unit`                      | Write the provided bytes.                                       |
| `Stream.close` | `IO Unit`                                  | Release the underlying endpoint.                                |

`read` takes a buffer to match `Read.read` and `Handle.read`, so that wrapping a handle in a
`Stream` does not silently give up the buffer-reuse path. `close` is a field rather than an omission,
so a `Stream` over a temporary file or captured pipe can be released; the constructor for a standard
stream supplies a no-op.

| Constructor        | Type                             | Description                                                  |
| ------------------ | -------------------------------- | ------------------------------------------------------------ |
| `Stream.ofHandle`  | `Handle → Stream`                |                                                              |
| `Stream.ofFile`    | `File → Stream`                  | Sequential (cursor-relative) reads and writes only.          |
| `Stream.ofBuffer`  | `IO.Ref ByteArray → Stream`      | In-memory capture; `close` is a no-op.                       |

## Buffering

Buffering is opt-in and layered over the raw types. `BufferedReader` wraps any `Read`able source;
`BufferedWriter` and `LineWriter` wrap any `Write`able sink.

| Function                   | Type                                                              | Description                                                                                                    |
| -------------------------- | ----------------------------------------------------------------- | -------------------------------------------------------------------------------------------------------------- |
| `BufferedReader.new`       | `[Read α] → α → (capacity : USize := 4096) → IO (BufferedReader α)` | Wrap a source with a read buffer of the given capacity.                                                       |
| `BufferedReader.read`      | `[Read α] → BufferedReader α → (n : USize) → IO ByteArray`        | Read `n` bytes, looping until `n` are collected or the source is exhausted. A request of at least `capacity` bytes bypasses the buffer. |
| `BufferedReader.readLine`  | `[Read α] → BufferedReader α → IO (Option String)`                | Read one line including the trailing newline, or `none` at EOF. Fails on invalid UTF-8.                       |
| `BufferedReader.readToEnd` | `[Read α] → BufferedReader α → IO ByteArray`                      | Read the remainder of the source into one `ByteArray`.                                                        |
| `BufferedReader.close`     | `[Close α] → BufferedReader α → IO Unit`                          | Close the underlying source. Bytes still in the read buffer are discarded.                                    |
| `BufferedWriter.new`       | `α → (capacity : USize := 4096) → IO (BufferedWriter α)`          | Wrap a sink with a write buffer of the given capacity.                                                        |
| `BufferedWriter.write`     | `[Write α] → BufferedWriter α → ByteArray → IO Unit`              | Buffer bytes, flushing to the sink when the buffer fills.                                                     |
| `BufferedWriter.flush`     | `[Write α] → BufferedWriter α → IO Unit`                          | Flush any buffered output to the sink.                                                                        |
| `BufferedWriter.close`     | `[Write α] → [Close α] → BufferedWriter α → IO Unit`              | Flush, then close the underlying sink.                                                                        |
| `LineWriter.new`           | `[Write α] → α → IO (LineWriter α)`                               | Wrap a sink in a line-buffered writer.                                                                        |
| `LineWriter.write`         | `[Write α] → LineWriter α → ByteArray → IO Unit`                  | Write bytes, flushing up to and including the last newline.                                                   |
| `LineWriter.flush`         | `[Write α] → LineWriter α → IO Unit`                              | Flush any buffered output to the sink.                                                                        |
| `LineWriter.close`         | `[Write α] → [Close α] → LineWriter α → IO Unit`                  | Flush, then close the underlying sink.                                                                        |

## Dir

`Dir` holds a `uv_dir_t`.

| Function       | Type                                         | Description                                                                                                                                                                                               | libuv                              |
| -------------- | -------------------------------------------- | --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ---------------------------------- |
| `Dir.openExisting` | `Path → IO Dir`                          | Open a directory for iteration.                                                                                                                                                                           | `uv_fs_opendir`                    |
| `Dir.withDir`  | `Path → (Dir → IO α) → IO α`                 | Open a directory, run an action, close in a `finally` block.                                                                                                                                              | `uv_fs_opendir` + `uv_fs_closedir` |
| `Dir.close`    | `Dir → IO Unit`                              | Explicitly close the directory handle.                                                                                                                                                                    | `uv_fs_closedir`                   |
| `Dir.next`     | `Dir → IO (Option DirEntry)`                 | Return the next entry, or `none` when exhausted. Order is filesystem-defined.                                                                                                                             | `uv_fs_readdir`                    |
| `Dir.drain`    | `Dir → IO (Array DirEntry)`                  | Drain every remaining entry via repeated `next`. Backs `readDir` and `FS.walk`.                                                                                                                           | `uv_fs_readdir`                    |
| `Dir.path`     | `Dir → Path`                                 | The path the directory was opened at.                                                                                                                                                                     |                                    |
| `Dir.iter`     | `Dir → IO (IterM (α := DirIterator) IO DirEntry)` | Lazy iterator over directory entries. Each step calls `readdir`. Works with `for entry in dir.iter do` and all `IterM` combinators. | `uv_fs_readdir`                    |
| `Dir.metadata` | `Dir → IO Metadata`                          | Return metadata for the directory itself. `uv_fs_opendir` does not expose a file descriptor, so this stats `dir.path` rather than the open handle.                                                        | `uv_fs_stat`                       |

## DirEntry

`DirEntry` is produced by `Dir.next`. It holds the parent `Dir` so its open methods can construct full paths as `dir.path / entry.fileName`. It already exists as `IO.FS.DirEntry` so it's included here for completeness.

| Function            | Type                     | Description                                                                                                   | libuv                          |
| ------------------- | ------------------------ | ------------------------------------------------------------------------------------------------------------- | ------------------------------ |
| `DirEntry.dir`      | `DirEntry → Dir`         | The directory this entry was read from.                                                                       |                                |
| `DirEntry.fileName` | `DirEntry → Path.Filename` | The entry name within its parent directory.                                                                 |                                |
| `DirEntry.path`     | `DirEntry → Path`        | Full path, constructed as `dir.path / entry.fileName`.                                                        |                                |
| `DirEntry.fileType` | `DirEntry → IO FileType` | Return the file type *without* following symlinks: a symlink reports `.symlink`, not its target's type.       | `uv_fs_lstat`                  |
| `DirEntry.isDir`    | `DirEntry → IO Bool`     | Return `true` if the entry is a directory (not a symlink to one). Convenience wrapper around `fileType`.      | `uv_fs_lstat`                  |
| `DirEntry.metadata` | `DirEntry → IO Metadata` | Return full metadata for the entry, following symlinks. Always issues a `stat` call; use `fileType` when only the type is needed. | `uv_fs_stat`  |

## FS Operations

These functions operate on the filesystem by path. They live in the `FS` namespace rather than `Path` because `Path` is a pure value type for path manipulation; IO operations belong in `FS`.

| Function          | Type                                                              | Description                                                                                                                                                                                                                  | libuv                                                                   |
| ----------------- | ----------------------------------------------------------------- | ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ----------------------------------------------------------------------- |
| `FS.copyFile`     | `Path → Path → IO Unit`                                           | Copy a file.                                                                                                                                                                                                                 | `uv_fs_copyfile`                                                        |
| `FS.removeFile`   | `Path → IO Unit`                                                  | Delete a file.                                                                                                                                                                                                               | `uv_fs_unlink`                                                          |
| `FS.removeDir`    | `Path → IO Unit`                                                  | Remove an empty directory. Fails if the directory is not empty.                                                                                                                                                              | `uv_fs_rmdir`                                                           |
| `FS.removeDirAll` | `Path → (ignoreErrors : Bool := false) → IO Unit`                 | Remove a directory and all its contents recursively. If `ignoreErrors`, entries that fail to remove (e.g. permission denied) are skipped instead of aborting, on a best-effort basis.                                       | `FS.readDir` + `uv_fs_unlink` + `uv_fs_rmdir`                          |
| `FS.createDir`    | `Path → (perm : FileRight := .defaultDir) → IO Unit` | Create a directory. Parent must exist. `perm` sets the initial mode bits (default `0o755`).                                                                                                                                  | `uv_fs_mkdir`                                                           |
| `FS.createDirAll` | `Path → (perm : FileRight := .defaultDir) → IO Unit` | Create a directory and all missing parent directories. No-op if the directory already exists. `perm` is applied to newly created directories only.                                                                           | `uv_fs_mkdir` (repeated)                                                |
| `FS.rename`       | `Path → Path → IO Unit`                                           | Rename or move a file or directory.                                                                                                                                                                                          | `uv_fs_rename`                                                          |
| `FS.hardLink`     | `(orig link : Path) → IO Unit`                                    | Create a hard link at `link` pointing to `orig`. Both paths must be on the same filesystem.                                                                                                                                  | `uv_fs_link`                                                            |
| `FS.copyDir`      | `(src dst : Path) → (ignoreErrors : Bool := false) → IO Unit`     | Recursively copy a directory tree from `src` to `dst`. `dst` must not exist; creates it with the same permission bits as `src`. Files are copied via `uv_fs_copyfile`. Symlinks are recreated verbatim rather than followed. If `ignoreErrors`, entries that fail to copy are skipped instead of aborting, on a best-effort basis. | `uv_fs_copyfile` + `FS.readDir`                                        |
| `FS.chown`        | `Path → (uid gid : UInt32) → IO Unit`                             | Change the owner and group of the file or directory at `path`. Follows symlinks. On Windows this is a no-op.                                                                                                                 | `uv_fs_chown`                                                           |
| `FS.lchown`       | `Path → (uid gid : UInt32) → IO Unit`                             | Like `FS.chown` but operates on the symlink itself rather than its target. On Windows this is a no-op.                                                                                                                       | `uv_fs_lchown`                                                          |
| `FS.truncate`     | `Path → (len : UInt64) → IO Unit`                                 | Truncate or extend the file at `path` to exactly `len` bytes. Follows symlinks. Complement to `File.setLength` for callers that do not have an open fd; libuv has no path-based `truncate`, so this opens the file `.readWrite` internally. | `uv_fs_open` + `uv_fs_ftruncate` + `uv_fs_close`                       |

## Convenience

| Function            | Type                         | Description                                                                                               | libuv                                        |
| ------------------- | ---------------------------- | --------------------------------------------------------------------------------------------------------- | -------------------------------------------- |
| `FS.readFile`       | `Path → IO String`           | Read an entire UTF-8 file into a string. Fails on invalid UTF-8.                                          | `uv_fs_open` + `uv_fs_read` + `uv_fs_close`  |
| `FS.readBinFile`    | `Path → IO ByteArray`        | Read an entire file into a `ByteArray`.                                                                   | `uv_fs_open` + `uv_fs_read` + `uv_fs_close`  |
| `FS.lines`          | `Path → IO (Array String)`   | Read all lines of a UTF-8 file into an array. Implemented via `BufferedReader`.                           | `uv_fs_open` + `uv_fs_read` + `uv_fs_close`  |
| `FS.writeFile`      | `Path → String → IO Unit`    | Write a UTF-8 string to a file, creating or truncating it.                                                | `uv_fs_open` + `uv_fs_write` + `uv_fs_close` |
| `FS.writeBinFile`   | `Path → ByteArray → IO Unit` | Write bytes to a file, creating or truncating it.                                                         | `uv_fs_open` + `uv_fs_write` + `uv_fs_close` |
| `FS.appendFile`     | `Path → ByteArray → IO Unit` | Append bytes to a file, creating it if it does not exist.                                                 | `uv_fs_open` + `uv_fs_write` + `uv_fs_close` |
| `FS.appendTextFile` | `Path → String → IO Unit`    | Append a UTF-8 string to a file, creating it if it does not exist.                                        | `uv_fs_open` + `uv_fs_write` + `uv_fs_close` |
| `FS.readDir`        | `Path → IO (Array DirEntry)` | List all entries in a directory. Order is filesystem-defined; use `FS.readDirSorted` for stable ordering. | `uv_fs_opendir` + `uv_fs_readdir` + `uv_fs_closedir` |
| `FS.readDirSorted`  | `Path → IO (Array DirEntry)` | Like `FS.readDir` but sorted by name.                                                                     | `uv_fs_opendir` + `uv_fs_readdir` + `uv_fs_closedir` |

## Temporary Files

`Std.FS.tempDir` (`IO Path`) resolves the system temp directory (`%TEMP%`/`%TMP%` on Windows, `$TMPDIR` on POSIX, falling back to a platform default), not hardcoded to `"/tmp"`. Following `std::env::temp_dir` + `tempfile`'s `tempdir`/`tempdir_in` split, each operation comes in a plain form (creates in `Std.FS.tempDir`) and an `*In` form (creates inside a caller-supplied `dir`), rather than a single function taking `Option Path`: an always-required `dir` parameter composes with a trailing closure without the caller needing to pass an explicit `none` first.

| Function              | Type                               | Description                                                                       | libuv                               |
| ---------------------- | ---------------------------------- | ---------------------------------------------------------------------------------- | ----------------------------------- |
| `FS.createTempFile`   | `IO (File × Path)`                 | Create a secure temporary file in `Std.FS.tempDir`. Caller is responsible for deleting it. | `uv_fs_mkstemp`                     |
| `FS.createTempFileIn` | `Path → IO (File × Path)`          | Create a secure temporary file inside `dir`. Caller is responsible for deleting it. | `uv_fs_mkstemp`                     |
| `FS.createTempDir`    | `IO Path`                          | Create a secure temporary directory in `Std.FS.tempDir`. Caller is responsible for deleting it. | `uv_fs_mkdtemp`                     |
| `FS.createTempDirIn`  | `Path → IO Path`                   | Create a secure temporary directory inside `dir`. Caller is responsible for deleting it. | `uv_fs_mkdtemp`                     |
| `FS.withTempFile`     | `(File → Path → IO α) → IO α`      | Create a temporary file in `Std.FS.tempDir`, run an action, delete it in a `finally` block. | `uv_fs_mkstemp` + `uv_fs_unlink`    |
| `FS.withTempFileIn`   | `Path → (File → Path → IO α) → IO α` | Create a temporary file inside `dir`, run an action, delete it in a `finally` block. | `uv_fs_mkstemp` + `uv_fs_unlink`    |
| `FS.withTempDir`      | `(Path → IO α) → IO α`             | Create a temporary directory in `Std.FS.tempDir`, run an action, delete it recursively in a `finally` block. | `uv_fs_mkdtemp` + `FS.removeDirAll` |
| `FS.withTempDirIn`    | `Path → (Path → IO α) → IO α`      | Create a temporary directory inside `dir`, run an action, delete it recursively in a `finally` block. | `uv_fs_mkdtemp` + `FS.removeDirAll` |

## Symlinks

The current API has `symlinkMetadata` (reads metadata without following the link), but no way to create symlinks or read their targets. `hardLink` is in FS Operations.

| Function           | Type                                                                | Description                                                                                                                                                                                                                                 | libuv            |
| ------------------ | ------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ---------------- |
| `FS.createSymlink` | `(target : Path) → (link : Path) → (dir : Bool := false) → IO Unit` | Create a symbolic link at `link` pointing to `target`. `target` is stored verbatim and need not exist at creation time. The `dir` flag is required on Windows (`UV_FS_SYMLINK_DIR`) when the target is a directory; on POSIX it is ignored. | `uv_fs_symlink`  |
| `FS.readSymlink`   | `Path → IO Path`                                                    | Read the raw target of a symbolic link without resolving it. Contrast with `Path.canonicalize` which follows the full chain.                                                                                                                      | `uv_fs_readlink` |

## Metadata

Timestamps use `Std.Time.Timestamp`. `creationTime` is `Option Timestamp` because Linux does not expose file creation time; libuv signals absence by falling back to another timestamp rather than reporting it, so the current implementation always produces `some` and the value is best-effort.

```lean
structure Metadata where
  accessed     : Timestamp
  modified     : Timestamp
  creationTime : Option Timestamp
  byteSize     : UInt64
  type         : FileType
  numLinks     : UInt64
  permissions  : FileRight
  inode        : Option UInt64  -- none on FAT32 and some network filesystems
  device       : Option UInt64  -- none on FAT32 and some network filesystems
  uid          : Option UInt32  -- owner user ID; none on Windows
  gid          : Option UInt32  -- owner group ID; none on Windows
```

| Function               | Type                                                               | Description                                                                                                                                                                     | libuv            |
| ---------------------- | ------------------------------------------------------------------ | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ---------------- |
| `FS.metadata`          | `Path → IO Metadata`                                               | Return metadata for a path, following symlinks.                                                                                                                                 | `uv_fs_stat`     |
| `FS.symlinkMetadata`   | `Path → IO Metadata`                                               | Return metadata for a path without following the final symlink.                                                                                                                 | `uv_fs_lstat`    |
| `FS.isDir`             | `Path → BaseIO Bool`                                               | Return `true` if the path exists and is a directory. Returns `false` on any error.                                                                                              | `uv_fs_stat`     |
| `FS.isFile`            | `Path → BaseIO Bool`                                               | Return `true` if the path exists and is a regular file. Returns `false` on any error.                                                                                           | `uv_fs_stat`     |
| `FS.isSymlink`         | `Path → BaseIO Bool`                                               | Return `true` if the path is a symbolic link without following it. Returns `false` on any error.                                                                                | `uv_fs_lstat`    |
| `FS.pathExists`        | `Path → BaseIO Bool`                                               | Return `true` if the path exists (as any file type). Returns `false` on any error.                                                                                              | `uv_fs_stat`     |
| `FS.getPermissions`    | `Path → IO FileRight`                                            | Return permission bits by path. Follows symlinks.                                                                                                                               | `uv_fs_stat`     |
| `FS.setPermissions`    | `Path → FileRight → IO Unit`                                     | Set permission bits by path. Follows symlinks.                                                                                                                                  | `uv_fs_chmod`    |
| `FS.setTimes`          | `Path → (accessed : Timestamp) → (modified : Timestamp) → IO Unit` | Set both access and modification timestamps by path.                                                                                                                            | `uv_fs_utime`    |
| `FS.setSymlinkTimes`   | `Path → (accessed : Timestamp) → (modified : Timestamp) → IO Unit` | Like `FS.setTimes` but operates on the symlink itself rather than its target.                                                                                                   | `uv_fs_lutime`   |
| `File.getPermissions`  | `File → IO FileRight`                                            | Return the open file's current permission bits.                                                                                                                                 | `uv_fs_fstat`    |
| `FS.filesystemStats`   | `Path → IO FilesystemStats`                                        | Return filesystem-level statistics (total/free space, inode counts) for the filesystem containing `path`.                                                                        | `uv_fs_statfs`   |
| `Metadata.sameFile`    | `Metadata → Metadata → Bool`                                       | Return `true` if two `Metadata` values refer to the same underlying file, compared by `inode` and `device`. Returns `false` if either has no inode (e.g. FAT32).               |                  |

### FilesystemStats

```lean
structure FilesystemStats where
  type            : UInt64  -- filesystem type identifier, as reported by the OS
  blockSize       : UInt64  -- fundamental block size, in bytes
  blocks          : UInt64  -- total number of blocks
  blocksFree      : UInt64  -- free blocks
  blocksAvailable : UInt64  -- free blocks available to unprivileged users
  files           : UInt64  -- total number of file nodes (inodes)
  filesFree       : UInt64  -- free file nodes
```

## Directory Utilities

| Function  | Type                                                | Description                       | libuv                                  |
| --------- | --------------------------------------------------- | --------------------------------- | -------------------------------------- |
| `FS.walk` | `Path → (ignoreErrors : Bool := false) → IO (IterM (α := WalkIterator) IO DirEntry)` | Lazy recursive directory walk. If `ignoreErrors`, a subtree that fails to open or read (e.g. permission denied) is skipped instead of aborting the whole walk; the directory entry itself is still yielded. The top-level `dir` is not covered by `ignoreErrors` and still raises on failure. | `uv_fs_opendir` + `uv_fs_readdir` + `uv_fs_closedir` |
| `FS.glob` | `Path → String → (ignoreErrors : Bool := false) → IO (Array DirEntry)` | Recursively list all entries beneath `dir` whose full path matches a `/`-separated glob `pattern` (`Path.matchGlob`). Built on `FS.walk`. | `uv_fs_opendir` + `uv_fs_readdir` + `uv_fs_closedir` |

## Shared Plumbing

A few conversion helpers are public rather than private so that `Std.Async.FS` can reuse them instead
of duplicating the conversion. They are not part of the intended user-facing surface.

| Function                       | Type                                        | Description                                                                 |
| ------------------------------ | ------------------------------------------- | --------------------------------------------------------------------------- |
| `File.ofInternal`              | `Internal.FS.File → File`                   | Wrap an already-open internal file, for the async open/create/temp helpers. |
| `File.toInternal`              | `File → Internal.FS.File`                   | The underlying internal file (read-only; `File.mk` stays private).          |
| `Dir.ofInternal`               | `Internal.FS.Dir → Path → Dir`              | Wrap an internal directory stream already opened at `path`.                 |
| `FS.metadataOfStat`            | `Internal.FS.Stat → Metadata`               | Build a `Metadata` from a raw stat result.                                  |
| `FS.filesystemStatsOfStatFS`   | `Internal.FS.StatFS → FilesystemStats`      | Build a `FilesystemStats` from a raw statfs result.                         |
| `FS.timestampToFloatSeconds`   | `Timestamp → Float`                         | Convert to the `Float` seconds that `uv_fs_utime`/`futime` take.            |

# Async Variants

Everything in `Std.Async.FS` returns `Async α` rather than `IO α`, and lives in the same namespace as
its synchronous counterpart (`Std.FS.File.*Async`, `Std.FS.*Async`). Unless noted, each `*Async`
function has the same signature and semantics as the function it mirrors, with `IO` replaced by
`Async`.

## File

| Function                     | Type                                                                                     | Notes                                                                     |
| ---------------------------- | ---------------------------------------------------------------------------------------- | ------------------------------------------------------------------------- |
| `File.openExistingAsync`     | `Path → (mode : OpenMode := .readOnly) → Async File`                                     |                                                                           |
| `File.createAsync`           | `Path → (mode : OpenMode := .writeCreate) → (perm : FileRight := .default) → Async File` |                                                                           |
| `File.withFileAsync`         | `Path → (mode : OpenMode := .readOnly) → (File → Async α) → Async α`                     |                                                                           |
| `File.closeAsync`            | `File → Async Unit`                                                                      |                                                                           |
| `File.readAtAsync`           | `File → (offset : UInt64) → (n : USize) → (_buf : ByteArray) → Async ByteArray`          | The async primitive has no buffer-reuse fast path, so `_buf` is accepted only for signature parity and is ignored. |
| `File.writeAtAsync`          | `File → (offset : UInt64) → ByteArray → Async Unit`                                      |                                                                           |
| `File.writeAsync`            | `File → ByteArray → Async Unit`                                                          |                                                                           |
| `File.syncAllAsync`          | `File → Async Unit`                                                                      |                                                                           |
| `File.syncDataAsync`         | `File → Async Unit`                                                                      |                                                                           |
| `File.sendFileAsync`         | `(src dst : File) → (offset : Int64) → (length : USize) → Async USize`                   |                                                                           |
| `File.setLengthAsync`        | `File → (len : UInt64) → Async Unit`                                                     |                                                                           |
| `File.metadataAsync`         | `File → Async Metadata`                                                                  |                                                                           |
| `File.getPermissionsAsync`   | `File → Async FileRight`                                                                 |                                                                           |
| `File.setPermissionsAsync`   | `File → FileRight → Async Unit`                                                          |                                                                           |
| `File.setTimesAsync`         | `File → (accessed modified : Timestamp) → Async Unit`                                    |                                                                           |
| `File.chownAsync`            | `File → (uid gid : UInt32) → Async Unit`                                                 | No-op on Windows.                                                         |
| `File.lockAsync`             | `File → (exclusive : Bool := true) → Async Unit`                                         | Runs on a dedicated work thread (`uv_queue_work`); see the note below.    |
| `File.tryLockAsync`          | `File → (exclusive : Bool := true) → Async Bool`                                         | Runs inline; never blocks for an unbounded time.                          |
| `File.unlockAsync`           | `File → Async Unit`                                                                      | Runs inline; never blocks for an unbounded time.                          |
| `File.atomicallyAsync`       | `File → (exclusive : Bool := true) → Async α → Async α`                                  |                                                                           |

`File.putStr`/`File.putStrLn` have no async counterpart; use `writeAsync` with `String.toUTF8`.

## Handle, Pipe, and TTY

| Function            | Type                                                         | Notes                                                                        |
| ------------------- | ------------------------------------------------------------ | ---------------------------------------------------------------------------- |
| `Handle.readAsync`  | `Handle → (n : USize) → Async ByteArray`                     | Resolves with the bytes read; empty at EOF.                                  |
| `Handle.writeAsync` | `Handle → ByteArray → Async Unit`                            |                                                                              |
| `Handle.closeAsync` | `Handle → Async Unit`                                        |                                                                              |
| `Pipe.readAsync`    | `Pipe → (n : USize) → Async ByteArray`                       |                                                                              |
| `Pipe.writeAsync`   | `Pipe → ByteArray → Async Unit`                              |                                                                              |
| `Pipe.closeAsync`   | `Pipe → Async Unit`                                          |                                                                              |
| `TTY.readAsync`     | `TTY → (n : USize) → Async ByteArray`                        |                                                                              |
| `TTY.writeAsync`    | `TTY → ByteArray → Async Unit`                               |                                                                              |
| `TTY.closeAsync`    | `TTY → Async Unit`                                           |                                                                              |

These take no `buf` argument. The synchronous `Handle.read` accepts one because it can hand libuv a
buffer it will fill before the call returns; an async read resolves a `Promise` after the caller has
moved on, so there is no uniquely-owned buffer to reuse and the allocation-avoidance path does not
apply. This matches `File.readAtAsync`, whose `_buf` exists only for signature parity.

For the `tty` and `pipe` kinds these submit `uv_read_start`/`uv_write` directly and resolve on the
completion callback — no semaphore, no blocked thread. For a `file` kind (redirected stdio) they go
through the same `uv_fs_read`/`uv_fs_write` thread-pool path as `File`'s async operations.

`TTY.setMode`, `TTY.getWinSize`, and the kind predicates have no async variants: they are
non-blocking calls against local state.

## Convenience

| Function                | Type                                    |
| ----------------------- | --------------------------------------- |
| `FS.readFileAsync`      | `Path → Async String`                   |
| `FS.readBinFileAsync`   | `Path → Async ByteArray`                |
| `FS.linesAsync`         | `Path → Async (Array String)`           |
| `FS.writeFileAsync`     | `Path → String → Async Unit`            |
| `FS.writeBinFileAsync`  | `Path → ByteArray → Async Unit`         |
| `FS.appendFileAsync`    | `Path → ByteArray → Async Unit`         |
| `FS.appendTextFileAsync`| `Path → String → Async Unit`            |

`readBinFileAsync` reads sequentially at the cursor in 64 KiB chunks until EOF, rather than sizing the
buffer from `stat` up front like the synchronous `readBinFile`.

## FS Operations

| Function                | Type                                                              |
| ----------------------- | ----------------------------------------------------------------- |
| `FS.copyFileAsync`      | `Path → Path → Async Unit`                                        |
| `FS.removeFileAsync`    | `Path → Async Unit`                                               |
| `FS.renameAsync`        | `Path → Path → Async Unit`                                        |
| `FS.hardLinkAsync`      | `(orig link : Path) → Async Unit`                                 |
| `FS.truncateAsync`      | `Path → (len : UInt64) → Async Unit`                              |
| `FS.chownAsync`         | `Path → (uid gid : UInt32) → Async Unit`                          |
| `FS.lchownAsync`        | `Path → (uid gid : UInt32) → Async Unit`                          |
| `FS.createSymlinkAsync` | `(target link : Path) → (dir : Bool := false) → Async Unit`       |
| `FS.readSymlinkAsync`   | `Path → Async Path`                                               |
| `FS.resolveAsync`       | `Path → Async Path`                                               |

`FS.resolveAsync` mirrors `Path.resolve` (make absolute and resolve all symlinks) and is backed by
`uv_fs_realpath`. It lives here because there is no async `Path` module.

## Directories

| Function                 | Type                                                                    |
| ------------------------ | ----------------------------------------------------------------------- |
| `FS.createDirAsync`      | `Path → (perm : FileRight := .defaultDir) → Async Unit`                 |
| `FS.createDirAllAsync`   | `Path → (perm : FileRight := .defaultDir) → Async Unit`                 |
| `FS.removeDirAsync`      | `Path → Async Unit`                                                     |
| `FS.removeDirAllAsync`   | `Path → (ignoreErrors : Bool := false) → Async Unit`                    |
| `FS.copyDirAsync`        | `(src dst : Path) → (ignoreErrors : Bool := false) → Async Unit`        |
| `FS.readDirAsync`        | `Path → Async (Array DirEntry)`                                         |
| `FS.readDirSortedAsync`  | `Path → Async (Array DirEntry)`                                         |
| `FS.walkAsync`           | `Path → (ignoreErrors : Bool := false) → Async (Array DirEntry)`        |
| `FS.globAsync`           | `Path → String → (ignoreErrors : Bool := false) → Async (Array DirEntry)` |

`Dir` itself has no async surface: there is no `Dir.openExistingAsync`/`nextAsync`/`iterAsync`, so
asynchronous traversal goes through the eager path-keyed helpers above. `walkAsync`/`globAsync`
collect into an `Array` rather than returning a lazy `IterM`, since `Async` has no lazy-iterator
integration yet.

## Metadata and Permissions

| Function                     | Type                                                              |
| ---------------------------- | ----------------------------------------------------------------- |
| `FS.metadataAsync`           | `Path → Async Metadata`                                           |
| `FS.symlinkMetadataAsync`    | `Path → Async Metadata`                                           |
| `FS.isFileAsync`             | `Path → Async Bool`                                               |
| `FS.isDirAsync`              | `Path → Async Bool`                                               |
| `FS.isSymlinkAsync`          | `Path → Async Bool`                                               |
| `FS.pathExistsAsync`         | `Path → Async Bool`                                               |
| `FS.getPermissionsAsync`     | `Path → Async FileRight`                                          |
| `FS.setPermissionsAsync`     | `Path → FileRight → Async Unit`                                   |
| `FS.setTimesAsync`           | `Path → (accessed modified : Timestamp) → Async Unit`             |
| `FS.setSymlinkTimesAsync`    | `Path → (accessed modified : Timestamp) → Async Unit`             |
| `FS.filesystemStatsAsync`    | `Path → Async FilesystemStats`                                    |

The four predicates return `Async Bool`, not `BaseIO Bool` as their synchronous counterparts do; they
still swallow every error and answer `false`.

## Temporary Files

| Function                   | Type                                        |
| -------------------------- | ------------------------------------------- |
| `FS.createTempFileAsync`   | `Async (File × Path)`                       |
| `FS.createTempFileInAsync` | `Path → Async (File × Path)`                |
| `FS.withTempFileAsync`     | `(File → Path → Async α) → Async α`         |
| `FS.withTempFileInAsync`   | `Path → (File → Path → Async α) → Async α`  |
| `FS.createTempDirAsync`    | `Async Path`                                |
| `FS.createTempDirInAsync`  | `Path → Async Path`                         |
| `FS.withTempDirAsync`      | `(Path → Async α) → Async α`                |
| `FS.withTempDirInAsync`    | `Path → (Path → Async α) → Async α`         |
