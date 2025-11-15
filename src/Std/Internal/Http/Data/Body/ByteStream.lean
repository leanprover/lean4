/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Sync
public import Init.Data.Vector
public import Std.Internal.Async
public import Std.Internal.Async.IO
public import Std.Internal.Http.Internal
public import Std.Internal.Http.Data.Chunk
public import Std.Internal.Http.Data.Body.Length

public section

/-!
# ByteStream

This module defines the `ByteStream` structure, which represents a channel for reading and
writing sequences of bytes. It provides utilities for efficiently processing byte arrays
in a streaming fashion, including support for chunk extensions.
-/

namespace Std.Http.Body

open Std Internal IO Async

set_option linter.all true

/--
A channel for byte arrays with support for chunk extensions.
-/
structure ByteStream where
  private mk ::
  private channel : CloseableChannel Chunk
  private knownSize : Std.Mutex (Option Body.Length)

namespace ByteStream

/--
Creates a new ByteStream with a specified capacity.
-/
def emptyWithCapacity (capacity : Nat := 128) : Async ByteStream := do
  let channel ← CloseableChannel.new (some capacity)
  let knownSize ← Std.Mutex.new none
  return { channel, knownSize }

/--
Creates a new ByteStream with default capacity.
-/
def empty : Async ByteStream :=
  emptyWithCapacity

/--
Tries to receive a chunk from the stream.
Returns `some` with a chunk when data is available, or `none` when the stream is closed
or no data is available.
-/
def tryRecv (stream : ByteStream) : Async (Option Chunk) := do
  stream.channel.tryRecv

/--
Receives (reads) a chunk from the stream.
Returns `none` if the stream is closed and no data is available.
-/
def recv (stream : ByteStream) : Async (Option Chunk) := do
  let task ← stream.channel.recv
  Async.ofTask task

/--
Receives a chunk and returns only its data, discarding extensions.
Returns `none` if the stream is closed and no data is available.
-/
def recvBytes (stream : ByteStream) : Async (Option ByteArray) := do
  let chunk? ← stream.recv
  return chunk?.map (·.data)

/--
Writes data to the stream as a chunk with optional extensions.
Returns `false` if the stream is closed.
-/
def write (stream : ByteStream) (data : ByteArray) (extensions : Array (String × Option String) := #[]) : Async Bool := do
  if data.isEmpty then
    return true

  let chunk : Chunk := { data := data, extensions := extensions }
  let task ← stream.channel.send chunk
  let task : AsyncTask _ := task.map (Except.mapError (fun x => userError (toString x)))
  Async.ofAsyncTask task

  return true

/--
Writes a complete chunk with extensions to the stream.
-/
def writeChunk (stream : ByteStream) (chunk : Chunk) : Async Unit := do
  let task ← stream.channel.send chunk
  let task : AsyncTask _ := task.map (Except.mapError (fun x => userError (toString x)))
  Async.ofAsyncTask task

/--
Gets the known size of the stream if available.
Returns `none` if the size is not known.
-/
def getKnownSize (stream : ByteStream) : Async (Option Body.Length) := do
  stream.knownSize.atomically do
    get

/--
Sets the known size of the stream.
This is typically used when the total expected size is known ahead of time.
-/
def setKnownSize (stream : ByteStream) (size : Option Body.Length) : Async Unit := do
  stream.knownSize.atomically do
    set size

/--
Closes the stream, preventing further writes and causing pending/future
recv operations to return `none` when no data is available.
-/
def close (stream : ByteStream) : Async Unit := do
  stream.channel.close

/--
Checks if the stream is closed.
-/
def isClosed (stream : ByteStream) : Async Bool := do
  stream.channel.isClosed

/--
Creates a `Selector` that resolves once the `ByteStream` has data available and provides that data.
-/
def recvSelector (stream : ByteStream) : Selector (Option Chunk) :=
  stream.channel.recvSelector

/--
Iterate over the body content in chunks, processing each chunk with the given step function.
-/
@[inline]
protected partial def forIn
    {β : Type} (stream : ByteStream) (acc : β)
    (step : Chunk → β → Async (ForInStep β)) : Async β := do

  let rec @[specialize] loop (stream : ByteStream) (acc : β) : Async β := do
    if let some chunk ← stream.recv then
      match ← step chunk acc with
      | .done res => return res
      | .yield res => loop stream res
    else
      return acc

  loop stream acc

instance : ForIn Async ByteStream Chunk where
  forIn := Std.Http.Body.ByteStream.forIn

instance : IO.AsyncRead ByteStream (Option Chunk) where
  read stream := stream.recv

instance : IO.AsyncWrite ByteStream ByteArray where
  write stream data := do discard <| stream.write data

end ByteStream
