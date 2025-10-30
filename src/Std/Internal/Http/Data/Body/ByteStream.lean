/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Sync
public import Std.Internal.Async
public import Std.Internal.Async.IO
public import Std.Internal.Http.Internal
public import Std.Internal.Http.Data.Chunk

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

private structure ByteStream.Consumer (α : Type) where
  promise : IO.Promise Bool
  waiter : Option (Internal.IO.Async.Waiter (Option α))

private def ByteStream.Consumer.resolve (c : ByteStream.Consumer α) (b : Bool) : BaseIO Unit :=
  c.promise.resolve b

private structure ByteStream.State where
  pendingChunks : Array Chunk := #[]
  bufferedSize : Nat := 0
  knownSize : Option Nat := none
  closed : Bool := false
  waiting : Queue (ByteStream.Consumer (Array Chunk)) := .empty
  backpressureWaiting : Queue (IO.Promise Unit) := .empty
  maxBufferSize : Nat := 8 * 1024 * 1024
  highMark : Nat := 4 * 1024 * 1024
  flushRequested : Bool := false

/--
A channel for byte arrays with support for chunk extensions.
-/
structure ByteStream where
  private mk ::
  private state : Std.Mutex ByteStream.State

namespace ByteStream

/--
Creates a new ByteStream with a specified initial capacity and high water mark.
-/
def emptyWithCapacity (maxBufferSize : Nat := 8 * 1024 * 1024) (highMark : Nat := 4 * 1024 * 1024) : Async ByteStream := do
  let state ← Std.Mutex.new { maxBufferSize := maxBufferSize, highMark := highMark }
  return { state }

/--
Creates a new ByteStream with default capacity.
-/
def empty : Async ByteStream :=
  emptyWithCapacity

private def shouldSendData' [MonadState State m] [Monad m] : m Bool := do
  let state ← get
  return state.bufferedSize >= state.highMark ∨ state.closed ∨ state.flushRequested

private def tryRecvFromBuffer'
  [MonadState State (AtomicT State m)] [MonadLiftT BaseIO m] [Monad m] :
  AtomicT State m (Option (Array Chunk)) := do
    let state ← get

    if state.pendingChunks.isEmpty then
      return none
    else
      -- Only send data if highMark is reached, stream is closed, or flush is requested
      if ← shouldSendData' then
        let chunks := state.pendingChunks
        modify fun s => { s with
          pendingChunks := #[],
          bufferedSize := 0,
          flushRequested := false
        }

        if let some (promise, rest) := state.backpressureWaiting.dequeue? then
          discard <| promise.resolve ()
          modify fun s => { s with backpressureWaiting := rest }

        return some chunks
      else
        return none

private def tryRecv' (stream : ByteStream) : Async (Option (Array Chunk)) := do
  stream.state.atomically tryRecvFromBuffer'

/--
Tries to receive all the current available chunks with extensions.
Returns `some` with a non-empty array when data is ready, or `none` when the stream is closed
or no data is available.
Data is only returned when the buffer reaches `highMark`, stream is closed, or `flush` is called.
-/
def tryRecv (stream : ByteStream) : Async (Option (Array Chunk)) := do
  stream.state.atomically do
    tryRecvFromBuffer'

/--
Receives (reads) chunks from the stream when the buffer reaches `highMark` or when flushed.
Returns `none` if the stream is closed and no data is available.
The returned array is always non-empty when `some`.
-/
partial def recv (stream : ByteStream) : Async (Option (Array Chunk)) := do
  let result ← stream.state.atomically do
    if let some chunks ← tryRecvFromBuffer' then
      return Sum.inr (some chunks)
    else
      let state ← get
      if state.closed then
        return Sum.inr none
      else
        -- Wait for more data or until highMark/flush
        let newPromise ← IO.Promise.new
        modify fun s => { s with waiting := s.waiting.enqueue ⟨newPromise, none⟩ }
        return Sum.inl newPromise

  match result with
  | .inr res => return res
  | .inl promise =>
      try
        discard <| await promise
        recv stream
      catch
        _ => return none

/--
Receives chunks and flattens them into a single ByteArray, discarding extensions.
Returns `none` if the stream is closed and no data is available.
-/
def recvBytes (stream : ByteStream) : Async (Option ByteArray) := do
  let chunks? ← stream.recv
  return chunks?.map fun chunks =>
    chunks.foldl (fun acc chunk => acc ++ chunk.data) ByteArray.empty

/--
Writes data to the stream as a chunk with optional extensions.
Only writes up to `maxBufferSize`, keeping any excess for the next write.
Returns `false` if the stream is closed or data is empty.
-/
partial def write (stream : ByteStream) (data : ByteArray) (extensions : Array (String × Option String) := #[]) : Async Bool := do
  if data.isEmpty then
    return true

  let result ← stream.state.atomically do
    let mut state ← get

    if state.closed then
      return Sum.inr (false, data, extensions)

    let availableSpace := state.maxBufferSize - state.bufferedSize

    if availableSpace = 0 then
      let promise ← IO.Promise.new
      modify fun s => { s with backpressureWaiting := s.backpressureWaiting.enqueue promise }
      return Sum.inl (promise, data, extensions)
    else
      let toWrite := min data.size availableSpace
      let dataToAdd := data.extract 0 toWrite
      let remaining := if toWrite < data.size then data.extract toWrite data.size else ByteArray.empty

      let chunk : Chunk := {
        data := dataToAdd,
        extensions := extensions
      }

      state := { state with
        pendingChunks := state.pendingChunks.push chunk,
        bufferedSize := state.bufferedSize + chunk.size
      }

      -- Notify waiting consumers if we've reached highMark
      if state.bufferedSize >= state.highMark then
        if let some (consumer, rest) := state.waiting.dequeue? then
          discard <| consumer.resolve true
          state := { state with waiting := rest }

      set state
      return Sum.inr (true, remaining, extensions)

  match result with
  | .inr (success, remaining, exts) =>
    if remaining.isEmpty ∨ ¬ success
     then
      return success
    else
      write stream remaining exts
  | .inl (backpressurePromise, remainingData, exts) =>
    try
      await backpressurePromise
      write stream remainingData exts
    catch
      _ => return false

/--
Writes a complete chunk with extensions to the stream.
-/
def writeChunk (stream : ByteStream) (chunk : Chunk) : Async Bool := do
  write stream chunk.data chunk.extensions

/--
Flushes the stream, causing any buffered data to be available for `recv`
even if it hasn't reached `highMark`.
-/
def flush (stream : ByteStream) : Async Unit := do
  stream.state.atomically do
    let state ← get
    if ¬ state.pendingChunks.isEmpty then
      modify fun s => { s with flushRequested := true }

      -- Notify waiting consumers
      if let some (consumer, rest) := state.waiting.dequeue? then
        discard <| consumer.resolve true
        modify fun s => { s with waiting := rest }

/--
Gets the known size of the stream if available.
Returns `none` if the size is not known.
-/
def getKnownSize (stream : ByteStream) : Async (Option Nat) := do
  stream.state.atomically do
    let state ← get
    return state.knownSize

/--
Sets the known size of the stream.
This is typically used when the total expected size is known ahead of time.
-/
def setKnownSize (stream : ByteStream) (size : Option Nat) : Async Unit := do
  stream.state.atomically do
    modify fun s => { s with knownSize := size }

/--
Closes the stream, preventing further writes and causing pending/future
recv operations to return `none` when no data is available.
-/
def close (stream : ByteStream) : Async Unit := do
  stream.state.atomically do
    let state ← get
    if ¬ state.closed then
      modify fun s => { s with closed := true }

      for consumer in state.waiting.toArray do
        discard <| consumer.resolve false

      modify fun s => { s with waiting := .empty }

      for promise in state.backpressureWaiting.toArray do
        discard <| promise.resolve ()

      modify fun s => { s with backpressureWaiting := .empty }

/--
Checks if the stream is closed.
-/
def isClosed (stream : ByteStream) : Async Bool := do
  stream.state.atomically do
    let state ← get
    return state.closed

/--
Checks if the stream is empty.
-/
def isEmpty (stream : ByteStream) : Async Bool := do
  stream.state.atomically do
    let state ← get
    return state.pendingChunks.isEmpty

/--
Returns `true` if data is ready to be received without blocking.
-/
private def recvReady' : AtomicT State IO Bool := do
  let state ← get
  return (¬ state.pendingChunks.isEmpty ∧ (← shouldSendData')) ∨ state.closed

/--
Creates a `Selector` that resolves once the `ByteStream` has data available and provides that data.
-/
partial def recvSelector (stream : ByteStream) : Selector (Option (Array Chunk)) where
  tryFn := do
    stream.state.atomically do
      let state ← get
      if (¬ state.pendingChunks.isEmpty ∧ (← shouldSendData')) ∨ state.closed then
        let result ← tryRecvFromBuffer'
        return some result
      else
        return none

  registerFn waiter := registerAux stream waiter

  unregisterFn := do
    stream.state.atomically do
      let state ← get
      let waiters ← state.waiting.filterM fun c => do
        match c.waiter with
        | some waiter => return !(← waiter.checkFinished)
        | none => return true

      modify fun s => { s with waiting := waiters }
where
  registerAux (stream : ByteStream) (waiter : Waiter (Option (Array Chunk))) : IO Unit := do
    stream.state.atomically do
      if ← recvReady' then
        let lose := do
          let state ← get
          if let some (consumer, waiters) := state.waiting.dequeue? then
            discard <| consumer.resolve true
            modify fun s => { s with waiting := waiters }

        let win promise := do
          let val ← tryRecvFromBuffer'
          promise.resolve (.ok val)

        waiter.race lose win
      else
        let promise ← IO.Promise.new
        modify fun s => { s with waiting := s.waiting.enqueue ⟨promise, some waiter⟩ }

        IO.chainTask promise.result? fun res? => do
          match res? with
          | none => return ()
          | some res =>
            if res then
              registerAux stream waiter
            else
              let lose := return ()
              let win promise := promise.resolve (.ok none)
              waiter.race lose win

/--
Iterate over the body content in chunks, processing each ByteArray chunk with the given step function.
-/
@[inline]
protected partial def forIn
  {β : Type} (stream : ByteStream) (acc : β)
  (step : Chunk → β → Async (ForInStep β)) :
  Async β := do
    let rec @[specialize] loop (stream : ByteStream) (acc : β) : Async β := do

      if let some data ← stream.recv then
        let mut acc := acc

        for data in data do
          match ← step data acc with
          | .done res => return res
          | .yield res => acc := res

        loop stream acc
      else
        return acc

    loop stream acc

instance : ForIn Async ByteStream Chunk where
  forIn := Std.Http.Body.ByteStream.forIn

instance : IO.AsyncRead ByteStream (Option (Array Chunk)) where
  read stream := stream.recv

instance : IO.AsyncWrite ByteStream ByteArray where
  write stream data := do discard <| stream.write data

end ByteStream
