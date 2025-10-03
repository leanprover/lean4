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
public import Std.Internal.Http.Util.BufferBuilder

public section

open Std Internal IO Async

namespace Std
namespace Http
namespace Body

set_option linter.all true

/-!
This module defines the `ByteStream` structure that is a channel for byte arrays.
-/

public section

private structure ByteStream.Consumer (α : Type) where
  promise : IO.Promise Bool
  waiter : Option (Internal.IO.Async.Waiter (Option α))

private def ByteStream.Consumer.resolve (c : ByteStream.Consumer α) (b : Bool) : BaseIO Unit :=
  c.promise.resolve b

private structure ByteStream.State where
  buffer : Util.BufferBuilder := .empty
  knownSize : Option Nat := none
  closed : Bool := false
  waiting : Queue (ByteStream.Consumer ByteArray) := .empty
  backpressureWaiting : Queue (IO.Promise Unit) := .empty
  maxBufferSize : Nat := 8 * 1024 * 1024

/--
A channel for byte arrays.
-/
structure ByteStream where
  private mk ::
  private state : Std.Mutex ByteStream.State

namespace ByteStream

/--
Creates a new ByteStream with a specified initial capacity.
-/
def emptyWithCapacity (maxBufferSize : Nat := 8 * 1024 * 1024) : Async ByteStream := do
  let state ← Std.Mutex.new { maxBufferSize := maxBufferSize }
  return { state }

/--
Creates a new ByteStream with default capacity.
-/
def empty : Async ByteStream :=
  emptyWithCapacity

private def tryRecvFromBuffer'
  [MonadState State (AtomicT State m)] [MonadLiftT BaseIO m] [Monad m] :
  AtomicT State m (Option Util.BufferBuilder) := do
    let state ← get

    if state.buffer.isEmpty then
      if state.closed then
        return none
      else
        return some .empty
    else
      modify fun s => { s with buffer := .empty }

      if let some (promise, rest) := state.backpressureWaiting.dequeue? then
        discard <| promise.resolve ()
        modify fun s => { s with backpressureWaiting := rest }

      return some state.buffer

  private def tryRecv' (stream : ByteStream) : Async (Option Util.BufferBuilder) := do
    stream.state.atomically tryRecvFromBuffer'

/--
Tries to receive all the current available data, it returns `some` when the channel is not closed
and contains some data.
-/
def tryRecv (stream : ByteStream) : Async (Option ByteArray) := do
  stream.state.atomically do
    let buf ← tryRecvFromBuffer'
    return Util.BufferBuilder.toByteArray <$> buf

/--
Receives (reads) all currently available data from the stream, emptying it.
Returns `none` if the stream is closed and no data is available.
-/
partial def recv (stream : ByteStream) : Async (Option ByteArray) := do
  let result ← stream.state.atomically do
    if let some bb ← tryRecvFromBuffer' then
      if bb.isEmpty then
        let state ← get
        if state.closed then
          return Sum.inr none
        else
          let newPromise ← IO.Promise.new
          modify fun s => { s with waiting := s.waiting.enqueue ⟨newPromise, none⟩ }
          return Sum.inl newPromise
      else
        return Sum.inr (some bb)
    else
      return Sum.inr none

  match result with
  | .inr res => return Util.BufferBuilder.toByteArray <$> res
  | .inl promise =>
      try
        discard <| await promise
        recv stream
      catch
        _ => return none

/--
Sends (writes) data to the stream, appending it to existing contents.
Returns `false` if the stream is closed or data is empty.
-/
partial def send (stream : ByteStream) (data : ByteArray) : Async Bool := do
  if data.isEmpty then
    return true

  let result ← stream.state.atomically do
    let state ← get

    if state.closed then
      return Sum.inr false

    let newSize := state.buffer.size + data.size

    if newSize >= state.maxBufferSize then
      let promise ← IO.Promise.new
      modify fun s => { s with backpressureWaiting := s.backpressureWaiting.enqueue promise }
      return Sum.inl promise
    else
      modify fun s => { s with buffer := s.buffer.append data }

      if let some (consumer, rest) := state.waiting.dequeue? then
        discard <| consumer.resolve true
        modify fun s => { s with waiting := rest }

      return Sum.inr true

  match result with
  | .inr r => return r
  | .inl backpressurePromise =>
    try
      await backpressurePromise
      send stream data
    catch
      _ => return false

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
    return state.buffer.isEmpty

/--
Returns `true` if data is ready to be received without blocking.
-/
private def recvReady' : AtomicT State IO Bool := do
  let state ← get
  return ¬ state.buffer.isEmpty ∨ state.closed

/--
Creates a `Selector` that resolves once the `ByteStream` has data available and provides that data.
-/
partial def recvSelector (stream : ByteStream) : Selector (Option ByteArray) where
  tryFn := do
    stream.state.atomically do
      let state ← get
      if ¬ state.buffer.isEmpty ∨ state.closed then
        let val ← tryRecvFromBuffer'
        return some (Util.BufferBuilder.toByteArray <$> val)
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
  registerAux (stream : ByteStream) (waiter : Waiter (Option ByteArray)) : IO Unit := do
    stream.state.atomically do
      if ← recvReady' then
        let lose := do
          let state ← get
          if let some (consumer, waiters) := state.waiting.dequeue? then
            discard <| consumer.resolve true
            modify fun s => { s with waiting := waiters }

        let win promise := do
          let val ← tryRecvFromBuffer'
          promise.resolve (.ok (Util.BufferBuilder.toByteArray <$> val))

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

instance : IO.AsyncRead ByteStream (Option ByteArray) where
  read stream := stream.recv

instance : IO.AsyncWrite ByteStream ByteArray where
  write stream data := do discard <| stream.send data

end ByteStream
