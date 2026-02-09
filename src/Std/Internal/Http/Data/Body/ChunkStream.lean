/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Sync
public import Std.Internal.Async
public import Std.Internal.Http.Data.Chunk
public import Std.Internal.Http.Data.Body.Length
public import Init.Data.Queue

public section

/-!
# ChunkStream

A `ChunkStream` represents an asynchronous channel for streaming data in chunks. It provides an
interface for producers and consumers to exchange chunks with optional metadata (extensions),
making it suitable for HTTP chunked transfer encoding and other streaming scenarios.
-/

namespace Std.Http.Body
open Std Internal IO Async

set_option linter.all true

namespace ChunkStream

open Internal.IO.Async in

private inductive Consumer where
  | normal (promise : IO.Promise (Option Chunk))
  | select (finished : Waiter (Option Chunk))

private def Consumer.resolve (c : Consumer) (x : Option Chunk) : BaseIO Bool := do
  match c with
  | .normal promise =>
    promise.resolve x
    return true
  | .select waiter =>
    let lose := return false
    let win promise := do
      promise.resolve (.ok x)
      return true
    waiter.race lose win

private structure Producer where
  chunk : Chunk
  promise : IO.Promise Bool

private structure State where
  /--
  Chunks pushed into the stream that are waiting to be consumed.
  -/
  values : Std.Queue Chunk

  /--
  Current number of chunks buffered in the stream.
  -/
  amount : Nat

  /--
  Maximum number of chunks allowed in the buffer. Writers block when amount ≥ capacity.
  -/
  capacity : Nat

  /--
  Consumers that are blocked on a producer providing them a chunk. They will be resolved to `none`
  if the stream closes.
  -/
  consumers : Std.Queue Consumer

  /--
  Producers that are blocked waiting for buffer space to become available.
  -/
  producers : Std.Queue Producer

  /--
  Whether the stream is closed already.
  -/
  closed : Bool
  /--
  Known size of the stream if available.
  -/
  knownSize : Option Body.Length
deriving Nonempty

end ChunkStream

/--
A channel for chunks with support for chunk extensions.
-/
structure ChunkStream where
  private mk ::
  private state : Mutex ChunkStream.State
deriving Nonempty

namespace ChunkStream

/--
Creates a new ChunkStream with a specified capacity.
-/
def emptyWithCapacity (capacity : Nat := 128) : Async ChunkStream := do
  return {
    state := ← Mutex.new {
      values := ∅
      consumers := ∅
      producers := ∅
      amount := 0
      capacity
      closed := false
      knownSize := none
    }
  }

/--
Creates a new ChunkStream with default capacity.
-/
@[always_inline, inline]
def empty : Async ChunkStream :=
  emptyWithCapacity

private def decreaseKnownSize (knownSize : Option Body.Length) (chunk : Chunk) : Option Body.Length :=
  match knownSize with
  | some (.fixed res) => some (Body.Length.fixed (res - chunk.wireFormatSize))
  | _ => knownSize

private def tryWakeProducer [Monad m] [MonadLiftT (ST IO.RealWorld) m] [MonadLiftT BaseIO m] :
    AtomicT State m Unit := do
  let st ← get
  -- Try to wake a producer if we have space
  if st.amount < st.capacity then
    if let some (producer, producers) := st.producers.dequeue? then
      let chunk := producer.chunk
      if st.amount + 1 <= st.capacity then
        set { st with
          values := st.values.enqueue chunk,
          amount := st.amount + 1,
          producers
        }
        producer.promise.resolve true
      else
        set { st with producers := producers.enqueue producer }

private def tryRecv' [Monad m] [MonadLiftT (ST IO.RealWorld) m] [MonadLiftT BaseIO m] :
    AtomicT State m (Option Chunk) := do
  let st ← get
  if let some (chunk, values) := st.values.dequeue? then
    let newKnownSize := decreaseKnownSize st.knownSize chunk
    let newAmount := st.amount - 1
    set { st with values, knownSize := newKnownSize, amount := newAmount }
    tryWakeProducer
    return some chunk
  else
    return none

/--
Attempts to receive a chunk from the stream. Returns `some` with a chunk when data is available, or `none`
when the stream is closed or no data is available.
-/
def tryRecv (stream : ChunkStream) : Async (Option Chunk) :=
  stream.state.atomically do
    tryRecv'

private def recv' (stream : ChunkStream) : BaseIO (Task (Option Chunk)) := do
  stream.state.atomically do
    if let some chunk ← tryRecv' then
      return .pure <| some chunk
    else if (← get).closed then
      return .pure none
    else
      let promise ← IO.Promise.new
      modify fun st => { st with consumers := st.consumers.enqueue (.normal promise) }
      return promise.result?.map (sync := true) (·.bind id)

/--
Receives a chunk from the stream. Blocks if no data is available yet. Returns `none` if the stream
is closed and no data is available. The amount parameter is ignored for chunk streams.
-/
def recv (stream : ChunkStream) (_count : Option UInt64) : Async (Option Chunk) := do
  Async.ofTask (← recv' stream)

private def trySend' (chunk : Chunk) : AtomicT State BaseIO Bool := do
  while true do
    let st ← get
    if let some (consumer, consumers) := st.consumers.dequeue? then
      let newKnownSize := decreaseKnownSize st.knownSize chunk
      let success ← consumer.resolve (some chunk)
      set { st with consumers, knownSize := newKnownSize }
      if success then
        break
    else
      if st.amount + 1 <= st.capacity then
        set { st with
          values := st.values.enqueue chunk,
          amount := st.amount + 1
        }
        return true
      else
        return false
  return true

private def trySend (stream : ChunkStream) (chunk : Chunk) : BaseIO Bool := do
  stream.state.atomically do
    if (← get).closed then
      return false
    else
      trySend' chunk

private def send' (stream : ChunkStream) (chunk : Chunk) : BaseIO (Task (Except IO.Error Unit)) := do
  stream.state.atomically do
    if (← get).closed then
      return .pure <| .error (.userError "channel closed")
    else if ← trySend' chunk then
      return .pure <| .ok ()
    else
      let promise ← IO.Promise.new
      let producer : Producer := { chunk, promise }
      modify fun st => { st with producers := st.producers.enqueue producer }
      return promise.result?.map (sync := true) fun res =>
        if res.getD false then .ok () else .error (.userError "channel closed")

/--
Sends a chunk to the stream. Blocks if the buffer is full.
-/
def send (stream : ChunkStream) (chunk : Chunk) : Async Unit := do
  if chunk.data.isEmpty then
    return

  let res : AsyncTask _ ← send' stream chunk
  await res

/--
Gets the known size of the stream if available. Returns `none` if the size is not known.
-/
@[always_inline, inline]
def getKnownSize (stream : ChunkStream) : Async (Option Body.Length) := do
  stream.state.atomically do
    return (← get).knownSize

/--
Sets the known size of the stream. Use this when the total expected size is known ahead of time.
-/
@[always_inline, inline]
def setKnownSize (stream : ChunkStream) (size : Option Body.Length) : Async Unit := do
  stream.state.atomically do
    modify fun st => { st with knownSize := size }

/--
Closes the stream, preventing further sends and causing pending/future
recv operations to return `none` when no data is available.
-/
def close (stream : ChunkStream) : Async Unit := do
  stream.state.atomically do
    let st ← get
    if st.closed then return ()
    for consumer in st.consumers.toArray do
      discard <| consumer.resolve none
    for producer in st.producers.toArray do
      producer.promise.resolve false
    set { st with consumers := ∅, producers := ∅, closed := true }

/--
Checks if the stream is closed.
-/
@[always_inline, inline]
def isClosed (stream : ChunkStream) : Async Bool := do
  stream.state.atomically do
    return (← get).closed

@[inline]
private def recvReady' [Monad m] [MonadLiftT (ST IO.RealWorld) m] :
    AtomicT State m Bool := do
  let st ← get
  return !st.values.isEmpty || st.closed

open Internal.IO.Async in

/--
Creates a `Selector` that resolves once the `ChunkStream` has data available and provides that data.
-/
def recvSelector (stream : ChunkStream) : Selector (Option Chunk) where
  tryFn := do
    stream.state.atomically do
      if ← recvReady' then
        let val ← tryRecv'
        return some val
      else
        return none

  registerFn waiter := do
    stream.state.atomically do
      if ← recvReady' then
        let lose := return ()
        let win promise := do
          promise.resolve (.ok (← tryRecv'))

        waiter.race lose win
      else
        modify fun st => { st with consumers := st.consumers.enqueue (.select waiter) }

  unregisterFn := do
    stream.state.atomically do
      let st ← get
      let consumers ← st.consumers.filterM
        fun
          | .normal .. => return true
          | .select waiter => return !(← waiter.checkFinished)
      set { st with consumers }

/--
Iterate over the stream content in chunks, processing each chunk with the given step function.
-/
@[inline]
protected partial def forIn
    {β : Type} (stream : ChunkStream) (acc : β)
    (step : Chunk → β → Async (ForInStep β)) : Async β := do

  let rec @[specialize] loop (stream : ChunkStream) (acc : β) : Async β := do
    if let some chunk ← stream.recv none then
      match ← step chunk acc with
      | .done res => return res
      | .yield res => loop stream res
    else
      return acc

  loop stream acc

/--
Iterate over the stream content in chunks, processing each chunk with the given step function.
-/
@[inline]
protected partial def forIn'
    {β : Type} (stream : ChunkStream) (acc : β)
    (step : Chunk → β → ContextAsync (ForInStep β)) : ContextAsync β := do

  let rec @[specialize] loop (stream : ChunkStream) (acc : β) : ContextAsync β := do
    let data ← Selectable.one #[
      .case (stream.recvSelector) pure,
      .case (← ContextAsync.doneSelector) (fun _ => pure none),
    ]

    if let some chunk := data then
      match ← step chunk acc with
      | .done res => return res
      | .yield res => loop stream res
    else
      return acc

  loop stream acc

instance : ForIn Async ChunkStream Chunk where
  forIn := Std.Http.Body.ChunkStream.forIn

instance : ForIn ContextAsync ChunkStream Chunk where
  forIn := Std.Http.Body.ChunkStream.forIn'

end Std.Http.Body.ChunkStream
