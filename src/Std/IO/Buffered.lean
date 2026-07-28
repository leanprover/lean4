/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Init.System.IO
public import Std.IO.Basic

public section

/-!
# Buffered Readers and Writers

Buffering is opt-in and layered on top of the raw, unbuffered `File`/`Handle` types: `BufferedReader`
wraps any `Read`able type, `BufferedWriter` buffers writes to a `File`, and `LineWriter` flushes
automatically whenever a newline is written (used by stdout).

The buffers themselves are `IO.Ref`s, so these wrappers run in any monad that `ST IO.RealWorld`
lifts into — `IO`, `BaseIO`, `Std.Async`, or an `EIO ε` with its own error type.
-/

namespace Std.IO

variable [Monad m] [MonadLiftT (ST IO.RealWorld) m]

private structure BufReaderState where
  data : ByteArray
  pos : Nat
  cap : Nat

namespace BufReaderState

/--
The currently buffered, not-yet-consumed bytes (`data[pos:cap]`), without consuming them.
-/
private def available (s : BufReaderState) : ByteArray :=
  s.data.extract s.pos s.cap

/--
Take up to `n` bytes from the currently buffered region, advancing `pos`. Returns fewer than `n`
bytes if the buffer holds less; the caller is responsible for writing the returned state back.
-/
private def take (s : BufReaderState) (n : Nat) : ByteArray × BufReaderState :=
  let k := min n (s.cap - s.pos)
  (s.data.extract s.pos (s.pos + k), { s with pos := s.pos + k })

end BufReaderState

/--
A buffered wrapper around any readable type. Reads are served from an in-memory buffer, refilling
from the underlying source as needed.
-/
structure BufferedReader (α : Type) where
  private mk ::

  /--
  The underlying readable source.
  -/
  private inner : α

  /--
  The buffer's state: backing array plus the `pos`/`cap` read window into it.
  -/
  private state : IO.Ref BufReaderState

  /--
  Capacity of the read buffer in bytes.
  -/
  private capacity : USize

namespace BufferedReader

/--
Wrap `inner` in a buffered reader with the given buffer `capacity`.
-/
def new (inner : α) (capacity : USize := 4096) : m (BufferedReader α) := do
  return { inner, state := ← ST.mkRef { data := .empty, pos := 0, cap := 0 }, capacity }

/--
Refill the backing buffer from the source if it is fully consumed (`pos = cap`); a no-op otherwise.
-/
private def fill [Read m α] (reader : BufferedReader α) : m Unit := do
  let s ← reader.state.get

  if s.pos == s.cap then
    let data ← Read.read reader.inner reader.capacity .empty
    reader.state.set { data, pos := 0, cap := data.size }

/--
Read `n` bytes, looping until `n` bytes are collected or the source is exhausted; returns fewer than
`n` bytes only at end-of-file. Bytes are served from the buffer first; once it is empty, a request
for at least `capacity` bytes bypasses the buffer and reads directly from the source, matching
`std::io::BufReader::read`'s fast path for large reads.
-/
partial def read [Read m α] (reader : BufferedReader α) (n : USize) : m ByteArray :=
  go n .empty
where
  go (remaining : USize) (acc : ByteArray) : m ByteArray := do
    if remaining == 0 then
      return acc
    let s ← reader.state.get
    if s.pos < s.cap then
      let (chunk, s') := s.take remaining.toNat
      reader.state.set s'
      go (remaining - chunk.size.toUSize) (acc ++ chunk)
    else if remaining >= reader.capacity then
      let chunk ← Read.read reader.inner remaining .empty
      if chunk.isEmpty then
        return acc
      else
        go (remaining - chunk.size.toUSize) (acc ++ chunk)
    else
      reader.fill
      let s' ← reader.state.get
      if s'.pos == s'.cap then
        return acc
      else
        go remaining acc

/--
Read a single line including the trailing newline, or `none` at end-of-file.
-/
partial def readLine [Read m α] [MonadExceptOf IO.Error m] (reader : BufferedReader α) :
    m (Option String) :=
  go .empty
where
  go (acc : ByteArray) : m (Option String) := do
    reader.fill
    let s ← reader.state.get
    let avail := s.available
    match avail.findIdx? (· == 10) with
    | some idx =>
      let (line, s') := s.take (idx + 1)
      reader.state.set s'
      match String.fromUTF8? (acc ++ line) with
      | some line => return some line
      | none => throw <| IO.userError "Std.IO.BufferedReader.readLine: invalid UTF-8"
    | none =>
      if avail.isEmpty then
        if acc.isEmpty then
          return none
        else
          match String.fromUTF8? acc with
          | some line => return some line
          | none => throw <| IO.userError "Std.IO.BufferedReader.readLine: invalid UTF-8"
      else
        reader.state.set { s with pos := s.cap }
        go (acc ++ avail)

/--
Read the remainder of the source into a single `ByteArray`.
-/
partial def readToEnd [Read m α] (reader : BufferedReader α) : m ByteArray :=
  go .empty
where
  go (acc : ByteArray) : m ByteArray := do
    reader.fill
    let s ← reader.state.get
    if s.pos == s.cap then
      return acc
    else
      let avail := s.available
      reader.state.set { s with pos := s.cap }
      go (acc ++ avail)

/--
Close the underlying source. Any bytes still sitting in the read buffer are discarded.
-/
def close [Close m α] (reader : BufferedReader α) : m Unit :=
  Close.close reader.inner

end BufferedReader

instance [Close m α] : Close m (BufferedReader α) where
  close := BufferedReader.close

/--
A buffered writer over a `File`. Writes accumulate in memory and are flushed to the file on `flush`
or when the buffer fills.
-/
structure BufferedWriter (α : Type) where
  private mk ::

  /--
  The underlying file.
  -/
  private inner : α

  /--
  The in-memory write buffer.
  -/
  private buffer : IO.Ref ByteArray

  /--
  Capacity of the write buffer in bytes.
  -/
  private capacity : USize

namespace BufferedWriter

/--
Wrap `file` in a buffered writer with the given buffer `capacity`.
-/
def new (file : α) (capacity : USize := 4096) : m (BufferedWriter α) := do
  return { inner := file, buffer := ← ST.mkRef .empty, capacity }

/--
Buffer `bytes`, flushing to the file when the buffer fills.
-/
def write [Write m α] (writer : BufferedWriter α) (bytes : ByteArray) : m Unit := do
  let combined := (← writer.buffer.get) ++ bytes
  if combined.size.toUSize >= writer.capacity then
    Write.write writer.inner combined
    writer.buffer.set .empty
  else
    writer.buffer.set combined

/--
Flush any buffered output to the underlying file.
-/
def flush [Write m α] (writer : BufferedWriter α) : m Unit := do
  let buf ← writer.buffer.get
  unless buf.isEmpty do
    Write.write writer.inner buf
    writer.buffer.set .empty

instance [Write m α] : Write m (BufferedWriter α) where
  write := BufferedWriter.write

/--
Flush any buffered output, then close the underlying sink. Flushing first avoids silently
dropping buffered bytes that were never written through.
-/
def close [Write m α] [Close m α] (writer : BufferedWriter α) : m Unit := do
  writer.flush
  Close.close writer.inner

end BufferedWriter

instance [Write m α] [Close m α] : Close m (BufferedWriter α) where
  close := BufferedWriter.close

/--
A writer wrapper that flushes automatically on newline characters (`\n`). Used by stdout so that
line-oriented output is delivered promptly.
-/
structure LineWriter (α : Type) where
  private mk ::

  /--
  The underlying writable sink.
  -/
  private inner : α

  /--
  The pending line buffer.
  -/
  private buffer : IO.Ref ByteArray

namespace LineWriter

/--
The index of the last newline byte in `b`, if any.
-/
private def findLastNewline (b : ByteArray) : Option Nat :=
  go b.size
where
  go : Nat → Option Nat
    | 0 => none
    | n + 1 => if b[n]! == 10 then some n else go n

/--
Wrap `inner` in a line-buffered writer.
-/
def new (inner : α) : m (LineWriter α) := do
  return { inner, buffer := ← ST.mkRef .empty }

/--
Write `bytes`, flushing the buffer up to and including each newline.
-/
def write [Write m α] (writer : LineWriter α) (bytes : ByteArray) : m Unit := do
  let combined := (← writer.buffer.get) ++ bytes
  match findLastNewline combined with
  | some idx =>
    Write.write writer.inner (combined.extract 0 (idx + 1))
    writer.buffer.set (combined.extract (idx + 1) combined.size)
  | none =>
    writer.buffer.set combined

/--
Flush any buffered output to the underlying sink.
-/
def flush [Write m α] (writer : LineWriter α) : m Unit := do
  let buf ← writer.buffer.get
  unless buf.isEmpty do
    Write.write writer.inner buf
    writer.buffer.set .empty

instance [Write m α] : Write m (LineWriter α) where
  write := LineWriter.write

/--
Flush any buffered output, then close the underlying sink. Flushing first avoids silently
dropping a pending partial line that was never terminated with `\n`.
-/
def close [Write m α] [Close m α] (writer : LineWriter α) : m Unit := do
  writer.flush
  Close.close writer.inner

end LineWriter

instance [Write m α] [Close m α] : Close m (LineWriter α) where
  close := LineWriter.close

end Std.IO
