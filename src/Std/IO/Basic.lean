/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Init.System.IO
public import Init.Data.SInt.Basic

public section

/-!
# Byte-stream abstractions

The core interfaces shared by byte-oriented resources such as files, sockets, and in-memory buffers.
`Read` and `Write` move bytes at whatever position the resource itself tracks, while `ReadAt` and
`WriteAt` name an absolute offset on every operation and keep no position of their own. `Seek` moves
the position that `Read` and `Write` resume from, and `Close` releases the resource.

Each class is indexed by the monad its operations run in, so a resource can be driven from `IO`,
from `Std.Async`, or from an `EIO ε` with its own error type. Implementations are free to pick the
monad that suits them; the wrappers in this namespace stay polymorphic over it.
-/

namespace Std.IO

/--
Typeclass for types that support reading bytes.
-/
class Read (m : Type → Type) (α : Type) where

  /--
  Read up to `n` bytes into `buf`, returning the filled slice.
  -/
  read : α → USize → ByteArray → m ByteArray

/--
Typeclass for types that support writing bytes.
-/
class Write (m : Type → Type) (α : Type) where

  /--
  Write all of `bytes`.
  -/
  write : α → ByteArray → m Unit

/--
Typeclass for types that support reading bytes at an absolute offset, independently of any position
the resource may track.
-/
class ReadAt (m : Type → Type) (α : Type) where

  /--
  Read up to `n` bytes starting at `offset` into `buf`, returning the filled slice. Returns fewer
  than `n` bytes when the read reaches the end of the stream, and no bytes once `offset` is at or
  past the end. Never returns more than `n` bytes: `Std.IO.Cursor` advances its position by the size
  of the slice returned.
  -/
  readAt : α → (offset : UInt64) → (n : USize) → ByteArray → m ByteArray

/--
Typeclass for types that support writing bytes at an absolute offset, independently of any position
the resource may track.
-/
class WriteAt (m : Type → Type) (α : Type) where

  /--
  Write all of `bytes` starting at `offset`, extending the stream if it ends before `offset`. Any
  gap left between the old end and `offset` reads back as zeros.
  -/
  writeAt : α → (offset : UInt64) → ByteArray → m Unit

/--
The position that a seek offset is measured from.
-/
inductive SeekFrom where
  /--
  From the start of the stream. The offset is unsigned, so this position is always valid.
  -/
  | start (offset : UInt64)
  /--
  From the end of the stream. A positive offset seeks past the end; reading there yields no bytes,
  while writing there fills the gap with zeros.
  -/
  | «end» (offset : Int64)
  /--
  From the current position.
  -/
  | current (offset : Int64)

/--
Typeclass for types whose extent in bytes is known. Resolving a `SeekFrom.end` needs it.
-/
class Size (m : Type → Type) (α : Type) where

  /--
  The total number of bytes the resource currently holds.
  -/
  size : α → m UInt64

/--
Typeclass for types that track a position which reads and writes resume from.
-/
class Seek (m : Type → Type) (α : Type) where

  /--
  Move the position to `pos`, returning the resulting offset from the start of the stream. Seeking
  before the start fails; seeking past the end succeeds.
  -/
  seek : α → SeekFrom → m UInt64

namespace Seek

/--
Move the position to the start of the stream.
-/
def rewind [Functor m] [Seek m α] (x : α) : m Unit :=
  discard <| Seek.seek x (.start 0)

/--
The current offset from the start of the stream.
-/
def position [Seek m α] (x : α) : m UInt64 :=
  Seek.seek x (.current 0)

end Seek

/--
Typeclass for types that hold a resource that must be released once it is no longer needed, such as
a file descriptor or a socket.
-/
class Close (m : Type → Type) (α : Type) where

  /--
  Release the resource. Idempotent where the underlying type's own `close` is idempotent.
  -/
  close : α → m Unit

end Std.IO
