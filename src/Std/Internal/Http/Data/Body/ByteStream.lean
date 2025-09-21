/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Sync
public import Std.Internal.Async
public import Std.Internal.Http.Util.BufferBuilder

public section

open Std Internal IO Async

namespace Std
namespace Http
namespace Body

/-!
This module defines the `ByteStream` structure that is a channel for byte arrays.
-/

public section

private structure ByteStream.State where
  buffer : Util.BufferBuilder := .empty
  knownSize : Option Nat := none
  closed : Bool := false
  waiting : IO.Promise Util.BufferBuilder
  backpressureWaiting : Option (IO.Promise Unit) := none
  maxBufferSize : Nat := 8 * 1024 * 1024

/--
Structure representing a byte stream with optional byte slices
-/
structure ByteStream where
  private mk ::
  private state : Std.Mutex ByteStream.State

namespace ByteStream

/--
Creates a new ByteStream with the specified initial capacity and buffer limit.
-/
def emptyWithCapacity (maxBufferSize : Nat := 8 * 1024 * 1024) : Async ByteStream := do
  let waiting ← IO.Promise.new
  waiting.resolve .empty

  let state ← Std.Mutex.new {
    waiting,
    maxBufferSize := maxBufferSize
  }
  return { state }

/--
Creates a new ByteStream with default capacity.
-/
def empty : Async ByteStream := emptyWithCapacity

private def tryRecvFromBuffer' : AtomicT State Async (Option Util.BufferBuilder) := do
  let state ← get
  if state.buffer.isEmpty then
    if state.closed then
      return none
    else
      return some .empty
  else
    modify fun s => { s with buffer := .empty }

    if let some promise := state.backpressureWaiting then
      if ¬ (← promise.isResolved) then
        discard <| promise.resolve ()
        modify fun s => { s with backpressureWaiting := none }

    return some state.buffer

private def tryRecv' (stream : ByteStream) : Async (Option Util.BufferBuilder) := do
  stream.state.atomically tryRecvFromBuffer'

def tryRecv (stream : ByteStream) : Async (Option (Option Util.BufferBuilder)) := do
  stream.state.atomically do
    match ← tryRecvFromBuffer' with
    | some ⟨#[], _⟩ => pure (some none)
    | some res => pure (some (some res))
    | none => pure none

/--
Receives (reads) all currently available data from the stream, emptying it.
Returns `none` if the stream is closed and no data is available.
-/
partial def recv (stream : ByteStream) : Async (Option Util.BufferBuilder) := do
  let result ← stream.state.atomically do
    if let some bb ← tryRecvFromBuffer' then
      if bb.isEmpty then
        let state ← get
        if state.closed then
          return Sum.inr none
        else
          let newPromise ← IO.Promise.new
          modify fun s => { s with waiting := newPromise }
          return Sum.inl newPromise
      else
        return Sum.inr (some bb)
    else
      return Sum.inr none

  match result with
  | .inr res => return res
  | .inl promise =>
      try
        some <$> await promise
      catch
        _ => return none

inductive SendResult
  | backpresure (promise : IO.Promise Unit)
  | result (x : Nat)

/--
Sends (writes) data to the stream, appending it to existing contents.
Returns `false` if the stream is closed or data is empty.
-/
partial def send (stream : ByteStream) (data : Util.BufferBuilder) : Async Bool := do
  if data.isEmpty then
    return true

  -- Check if we need to wait for backpressure relief
  let result ← stream.state.atomically do
    let state ← get

    if state.closed then
      return Sum.inr false

    let newSize := state.buffer.size

    if newSize >= state.maxBufferSize then
      match state.backpressureWaiting with
      | some existing =>
        return Sum.inl existing
      | none =>
        let promise ← IO.Promise.new
        set { state with backpressureWaiting := some promise }
        return Sum.inl promise
    else
      set { state with buffer := state.buffer.append data }
      if ¬ (← state.waiting.isResolved) then
        state.waiting.resolve (← modifyGet (fun s => (s.buffer, { s with buffer := .empty })))
      return Sum.inr true


  match result with
  | .inr r =>
      return r
  | .inl backp =>
     try
      await backp
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

      if ¬ (← state.waiting.isResolved) then
        if state.buffer.isEmpty then
          discard <| state.waiting.resolve .empty
        else
          state.waiting.resolve state.buffer
          modify fun s => { s with buffer := .empty }

      -- Resolve any backpressure waiters to unblock them
      if let some promise := state.backpressureWaiting then
        discard <| promise.resolve ()
        modify fun s => { s with backpressureWaiting := none }

/--
Checks if the stream is closed.
-/
def isClosed (stream : ByteStream) : Async Bool := do
  stream.state.atomically do
    let state ← get
    return state.closed

end ByteStream
