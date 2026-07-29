/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Init.System.IO
public import Init.Data.Iterators.Producers
public import Init.Data.Iterators.Consumers
public import Init.Data.ToString.Macro
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
The number of buffered bytes that have not been consumed yet.
-/
private def remaining (s : BufReaderState) : Nat :=
  s.cap - s.pos

/--
Append the first `n` unconsumed bytes to `acc` and advance past them; `n` must not exceed
`remaining`. The bytes go straight from the buffer into `acc`, so the buffered region is never
materialized on its own. The caller is responsible for writing the returned state back.
-/
private def takeInto (s : BufReaderState) (acc : ByteArray) (n : Nat) : ByteArray × BufReaderState :=
  (s.data.copySlice s.pos acc acc.size n false, { s with pos := s.pos + n })

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
  go (want : USize) (acc : ByteArray) : m ByteArray := do
    if want == 0 then
      return acc
    let s ← reader.state.get
    if s.remaining > 0 then
      let k := min want.toNat s.remaining
      let (acc, s) := s.takeInto acc k
      reader.state.set s
      go (want - k.toUSize) acc
    else if want >= reader.capacity then
      let chunk ← Read.read reader.inner want .empty
      if chunk.isEmpty then
        return acc
      else
        go (want - chunk.size.toUSize) (acc ++ chunk)
    else
      reader.fill
      let s ← reader.state.get
      if s.remaining == 0 then
        return acc
      else
        go want acc

/--
Read a single line as raw bytes, or `none` at end-of-file. The line terminator is included only if
`keepTerminator` is set; dropping it here rather than afterwards keeps the bytes from being copied
again just to shorten them.
-/
private partial def readLineBytes [Read m α] (reader : BufferedReader α) (keepTerminator : Bool) :
    m (Option ByteArray) :=
  go .empty
where
  go (acc : ByteArray) : m (Option ByteArray) := do
    reader.fill
    let s ← reader.state.get
    -- `fill` keeps `cap` equal to `data.size`, so searching from `pos` to the end of `data` covers
    -- exactly the unconsumed window.
    match (s.data.idxOfByte? 10 s.pos.toUSize).map USize.toNat with
    | some nl =>
      let acc := s.data.copySlice s.pos acc acc.size (if keepTerminator then nl + 1 - s.pos else nl - s.pos) false
      reader.state.set { s with pos := nl + 1 }
      if !keepTerminator && acc.size > 0 && acc[acc.size - 1]! == 13 then
        -- The `\r` of a `\r\n`; it is only reachable here once per line, so the copy is not on the
        -- hot path for files with Unix line endings.
        return some (acc.extract 0 (acc.size - 1))
      else
        return some acc
    | none =>
      if s.remaining == 0 then
        return if acc.isEmpty then none else some acc
      else
        let (acc, s) := s.takeInto acc s.remaining
        reader.state.set s
        go acc

private def decodeUtf8 [MonadExceptOf IO.Error m] (caller : String) (bytes : ByteArray) : m String :=
  match String.fromUTF8? bytes with
  | some s => pure s
  | none => throw <| IO.userError s!"{caller}: invalid UTF-8"

/--
Read a single line including the trailing newline, or `none` at end-of-file.
-/
def readLine [Read m α] [MonadExceptOf IO.Error m] (reader : BufferedReader α) :
    m (Option String) := do
  match ← reader.readLineBytes (keepTerminator := true) with
  | none => return none
  | some bytes => return some (← decodeUtf8 "Std.IO.BufferedReader.readLine" bytes)

/--
Read the remainder of the source into a single `ByteArray`.
-/
partial def readToEnd [Read m α] (reader : BufferedReader α) : m ByteArray :=
  go .empty
where
  go (acc : ByteArray) : m ByteArray := do
    reader.fill
    let s ← reader.state.get
    if s.remaining == 0 then
      return acc
    else
      let (acc, s) := s.takeInto acc s.remaining
      reader.state.set s
      go acc

/--
Close the underlying source. Any bytes still sitting in the read buffer are discarded.
-/
def close [Close m α] (reader : BufferedReader α) : m Unit :=
  Close.close reader.inner

end BufferedReader

/--
Implementation detail: the state behind the iterator returned by `BufferedReader.lines`.
-/
structure LineIterator (m : Type → Type) (α : Type) where

  /--
  The reader the lines are pulled from. Its buffer holds all the position state, so stepping the
  iterator leaves this unchanged.
  -/
  private reader : BufferedReader α

namespace LineIterator

@[no_expose]
instance [Read m α] [MonadExceptOf IO.Error m] : Iterator (LineIterator m α) m String where
  IsPlausibleStep _ _ := True
  step it := do
    match ← it.internalState.reader.readLineBytes (keepTerminator := false) with
    | none => return .deflate ⟨.done, trivial⟩
    | some bytes =>
      let line ← BufferedReader.decodeUtf8 "Std.IO.BufferedReader.lines" bytes
      return .deflate ⟨.yield ⟨it.internalState⟩ line, trivial⟩

instance [Monad n] [Read m α] [MonadExceptOf IO.Error m] :
    IteratorLoop (LineIterator m α) m n := .defaultImplementation

end LineIterator

/--
The lines of `reader`, decoded as UTF-8 and pulled one at a time as the iterator is stepped.

Both `"\n"` and `"\r\n"` end a line, and the terminator is not part of the line. A final terminator
does not produce a trailing empty line. Stepping reads from the underlying source and fails if the
bytes are not valid UTF-8.
-/
def BufferedReader.lines [Read m α] (reader : BufferedReader α) :
    IterM (α := LineIterator m α) m String :=
  IterM.mk ⟨reader⟩

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
