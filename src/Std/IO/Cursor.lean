/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.IO.Basic

public section

/-!
# Cursor

A `Cursor` adds a position to a resource that is addressed by absolute offset, turning `ReadAt` and
`WriteAt` into the sequential `Read`, `Write`, and `Seek` interfaces.
-/

namespace Std.IO

/--
A sequential view over a resource addressed by absolute offset. The cursor holds the position that
`Read` and `Write` resume from and advances it by the number of bytes transferred.

A cursor is single-consumer: operations sharing one race on its position. Use `ReadAt`/`WriteAt`
against the underlying resource directly when operations need to overlap.
-/
structure Cursor (α : Type) where
  private mk ::

  /--
  The underlying positional resource.
  -/
  private inner : α

  /--
  The offset that the next read or write starts at.
  -/
  private pos : IO.Ref UInt64

namespace Cursor

variable [Monad m] [MonadLiftT (ST IO.RealWorld) m]

/--
Open a cursor over `inner`, starting at `pos`.
-/
def new (inner : α) (pos : UInt64 := 0) : m (Cursor α) := do
  return { inner, pos := ← ST.mkRef pos }

/--
Offset `base` by `delta`, failing rather than wrapping if the result would fall before the start of
the stream.
-/
private def shift [MonadExceptOf IO.Error m] (base : UInt64) (delta : Int64) : m UInt64 := do
  if delta < 0 then
    let back := (-delta).toUInt64
    if back > base then
      throw <| IO.userError "Std.IO.Cursor: seek before the start of the stream"
    return base - back
  else
    return base + delta.toUInt64

/--
Read up to `n` bytes at the current position, advancing it past the bytes returned.
-/
def read [ReadAt m α] (cursor : Cursor α) (n : USize) (buf : ByteArray) : m ByteArray := do
  let pos ← cursor.pos.get
  let data ← ReadAt.readAt cursor.inner pos n buf
  cursor.pos.set (pos + data.size.toUInt64)
  return data

/--
Write `bytes` at the current position, advancing it past them.
-/
def write [WriteAt m α] (cursor : Cursor α) (bytes : ByteArray) : m Unit := do
  let pos ← cursor.pos.get
  WriteAt.writeAt cursor.inner pos bytes
  cursor.pos.set (pos + bytes.size.toUInt64)

/--
Move the position to `pos`, returning the resulting offset from the start of the stream.
-/
def seek [MonadExceptOf IO.Error m] [Size m α] (cursor : Cursor α) (pos : SeekFrom) : m UInt64 := do
  let target ←
    match pos with
    | .start offset => pure offset
    | .current offset => shift (← cursor.pos.get) offset
    | .end offset => shift (← Size.size cursor.inner) offset
  cursor.pos.set target
  return target

/--
Close the underlying resource.
-/
def close [Close m α] (cursor : Cursor α) : m Unit :=
  Close.close cursor.inner

end Cursor

instance [Monad m] [MonadLiftT (ST IO.RealWorld) m] [ReadAt m α] : Read m (Cursor α) where
  read := Cursor.read

instance [Monad m] [MonadLiftT (ST IO.RealWorld) m] [WriteAt m α] : Write m (Cursor α) where
  write := Cursor.write

instance [Monad m] [MonadLiftT (ST IO.RealWorld) m] [MonadExceptOf IO.Error m] [Size m α] :
    Seek m (Cursor α) where
  seek := Cursor.seek

instance [Close m α] : Close m (Cursor α) where
  close := Cursor.close

end Std.IO
