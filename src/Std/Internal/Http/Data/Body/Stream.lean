/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Sync
public import Std.Internal.Async
public import Std.Internal.Http.Data.Extensions
public import Std.Internal.Http.Data.Request
public import Std.Internal.Http.Data.Response
public import Std.Internal.Http.Data.Chunk
public import Std.Internal.Http.Data.Body.Basic
public import Std.Internal.Http.Data.Body.Length
public import Init.Data.ByteArray

public section

/-!
# Body Channels

This module defines a body channel split into two faces:

- `Body.Outgoing`: producer side (send chunks)
- `Body.Incoming`: consumer side (receive chunks)

Response/request builders produce `Body.Outgoing` because they only write body data.
Consumers and handlers receive `Body.Incoming` because they only read body data.

The channel supports an internal FIFO queue for pre-buffered chunks.
Sends enqueue chunks while buffer capacity is available; when full, one producer may block until
space is freed. At most one blocked producer, one blocked consumer, and one blocked
interest-selector are supported.
-/

namespace Std.Http.Body
open Std Internal IO Async

set_option linter.all true

namespace Channel

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

open Internal.IO.Async in
private def resolveInterestWaiter (waiter : Waiter Bool) (x : Bool) : BaseIO Bool := do
  let lose := return false
  let win promise := do
    promise.resolve (.ok x)
    return true
  waiter.race lose win

private structure State where
  /--
  Single blocked producer slot used when the internal queue is full.
  -/
  pendingProducer : Option Producer := none

  /--
  FIFO chunks waiting to be consumed.
  -/
  queuedChunks : Std.Queue Chunk := ∅

  /--
  Number of chunks currently buffered in `queuedChunks`.
  -/
  queuedSize : Nat := 0

  /--
  Maximum number of buffered chunks allowed before producers block.
  -/
  capacity : Nat

  /--
  A single blocked consumer waiting for a producer
  -/
  pendingConsumer : Option Consumer

  /--
  A waiter for `Outgoing.interestSelector`
  -/
  interestWaiter : Option (Internal.IO.Async.Waiter Bool)

  /--
  Whether the channel is closed
  -/
  closed : Bool

  /--
  Known size of the stream if available
  -/
  knownSize : Option Body.Length

  /--
  Buffered partial chunk data accumulated from `Outgoing.send ... (incomplete := true)`.
  These partial pieces are collapsed and emitted as a single chunk on the next complete send.
  -/
  pendingIncompleteChunk : Option Chunk := none
deriving Nonempty

end Channel

/-- Receive-side face of a body channel. -/
structure Incoming where
  private mk ::
  private state : Mutex Channel.State
deriving Nonempty, TypeName

/-- Send-side face of a body channel. -/
structure Outgoing where
  private mk ::
  private state : Mutex Channel.State
deriving Nonempty, TypeName

/- Internal conversions between channel faces.
Use these only in HTTP internals where body direction must be adapted. -/
namespace Internal

/-- Reinterprets the receive-side handle as a send-side handle over the same channel. -/
@[always_inline, inline]
def incomingToOutgoing (incoming : Incoming) : Outgoing :=
  { state := incoming.state }

/-- Reinterprets the send-side handle as a receive-side handle over the same channel. -/
@[always_inline, inline]
def outgoingToIncoming (outgoing : Outgoing) : Incoming :=
  { state := outgoing.state }

end Internal

/-- Creates a queue-backed body channel. -/
def mkChannel (capacity : Nat := 64) : Async (Outgoing × Incoming) := do
  let capacity := capacity.max 1
  let state ← Mutex.new {
    pendingProducer := none
    queuedChunks := ∅
    queuedSize := 0
    capacity := capacity
    pendingConsumer := none
    interestWaiter := none
    closed := false
    knownSize := none
  }
  return ({ state }, { state })

namespace Channel

private def decreaseKnownSize (knownSize : Option Body.Length) (chunk : Chunk) : Option Body.Length :=
  match knownSize with
  | some (.fixed res) => some (Body.Length.fixed (res - chunk.data.size))
  | _ => knownSize

private def mergeChunks (base : Chunk) (next : Chunk) : Chunk :=
  {
    data := base.data ++ next.data
    extensions := if base.extensions.isEmpty then next.extensions else base.extensions
  }

private def pruneFinishedWaiters [Monad m] [MonadLiftT (ST IO.RealWorld) m] :
    AtomicT State m Unit := do
  let st ← get

  let pendingConsumer ←
    match st.pendingConsumer with
    | some (.select waiter) =>
      if ← waiter.checkFinished then
        pure none
      else
        pure st.pendingConsumer
    | _ =>
      pure st.pendingConsumer

  let interestWaiter ←
    match st.interestWaiter with
    | some waiter =>
      if ← waiter.checkFinished then
        pure none
      else
        pure st.interestWaiter
    | none =>
      pure none

  set { st with pendingConsumer, interestWaiter }

private def signalInterest [Monad m] [MonadLiftT (ST IO.RealWorld) m] [MonadLiftT BaseIO m] :
    AtomicT State m Unit := do
  let st ← get
  if let some waiter := st.interestWaiter then
    discard <| resolveInterestWaiter waiter true
    set { st with interestWaiter := none }

private def recvReady' [Monad m] [MonadLiftT (ST IO.RealWorld) m] :
    AtomicT State m Bool := do
  let st ← get
  return st.queuedSize > 0 || st.pendingProducer.isSome || st.closed

private def hasInterest' [Monad m] [MonadLiftT (ST IO.RealWorld) m] :
    AtomicT State m Bool := do
  let st ← get
  return st.pendingConsumer.isSome

private def tryRecv' [Monad m] [MonadLiftT (ST IO.RealWorld) m] [MonadLiftT BaseIO m] :
    AtomicT State m (Option Chunk) := do
  let st ← get
  if let some (chunk, queuedChunks) := st.queuedChunks.dequeue? then
    let mut next := {
      st with
      queuedChunks
      queuedSize := st.queuedSize - 1
      knownSize := decreaseKnownSize st.knownSize chunk
    }

    if let some producer := st.pendingProducer then
      producer.promise.resolve true
      next := {
        next with
        pendingProducer := none
        queuedChunks := next.queuedChunks.enqueue producer.chunk
        queuedSize := next.queuedSize + 1
      }

    set next
    return some chunk
  else if let some producer := st.pendingProducer then
    producer.promise.resolve true
    set {
      st with
      pendingProducer := none
      knownSize := decreaseKnownSize st.knownSize producer.chunk
    }
    return some producer.chunk
  else
    return none

private def close' [Monad m] [MonadLiftT (ST IO.RealWorld) m] [MonadLiftT BaseIO m] :
    AtomicT State m Unit := do
  let st ← get
  if st.closed then
    return ()

  if let some consumer := st.pendingConsumer then
    discard <| consumer.resolve none

  if let some producer := st.pendingProducer then
    producer.promise.resolve false

  if let some waiter := st.interestWaiter then
    discard <| resolveInterestWaiter waiter false

  set {
    st with
    pendingProducer := none
    pendingConsumer := none
    interestWaiter := none
    pendingIncompleteChunk := none
    closed := true
  }

end Channel

namespace Incoming

/--
Attempts to receive a chunk from the channel without blocking.
Returns `some chunk` only when data is already queued.
-/
def tryRecv (incoming : Incoming) : Async (Option Chunk) :=
  incoming.state.atomically do
    Channel.pruneFinishedWaiters
    Channel.tryRecv'

private def recv' (incoming : Incoming) : BaseIO (AsyncTask (Option Chunk)) := do
  incoming.state.atomically do
    Channel.pruneFinishedWaiters

    if let some chunk ← Channel.tryRecv' then
      return AsyncTask.pure (some chunk)

    let st ← get
    if st.closed then
      return AsyncTask.pure none

    if st.pendingConsumer.isSome then
      return Task.pure (.error (IO.Error.userError "only one blocked consumer is allowed"))

    let promise ← IO.Promise.new
    set { st with pendingConsumer := some (.normal promise) }
    Channel.signalInterest
    return promise.result?.map (sync := true) fun
      | none => .error (IO.Error.userError "the promise linked to the consumer was dropped")
      | some res => .ok res

/--
Receives a chunk from the channel. Blocks until data is available or the channel closes.
Returns `none` if the channel is closed and no queued data remains.
-/
def recv (incoming : Incoming) (_count : Option UInt64) : Async (Option Chunk) :=
  do Async.ofAsyncTask (← recv' incoming)

/--
Closes the channel.
-/
def close (incoming : Incoming) : Async Unit :=
  incoming.state.atomically do
    Channel.close'

/--
Checks whether the channel is closed.
-/
@[always_inline, inline]
def isClosed (incoming : Incoming) : Async Bool :=
  incoming.state.atomically do
    return (← get).closed

/--
Gets the known size if available.
-/
@[always_inline, inline]
def getKnownSize (incoming : Incoming) : Async (Option Body.Length) :=
  incoming.state.atomically do
    return (← get).knownSize

/--
Sets known size metadata.
-/
@[always_inline, inline]
def setKnownSize (incoming : Incoming) (size : Option Body.Length) : Async Unit :=
  incoming.state.atomically do
    modify fun st => { st with knownSize := size }

open Internal.IO.Async in
/--
Creates a selector that resolves when queued data is available (or the channel closes).
-/
def recvSelector (incoming : Incoming) : Selector (Option Chunk) where
  tryFn := do
    incoming.state.atomically do
      Channel.pruneFinishedWaiters
      if ← Channel.recvReady' then
        return some (← Channel.tryRecv')
      else
        return none

  registerFn waiter := do
    incoming.state.atomically do
      Channel.pruneFinishedWaiters
      if ← Channel.recvReady' then
        let lose := return ()
        let win promise := do
          promise.resolve (.ok (← Channel.tryRecv'))
        waiter.race lose win
      else
        let st ← get
        if st.pendingConsumer.isSome then
          throw (.userError "only one blocked consumer is allowed")

        set { st with pendingConsumer := some (.select waiter) }
        Channel.signalInterest

  unregisterFn := do
    incoming.state.atomically do
      Channel.pruneFinishedWaiters

/--
Iterates over chunks until the channel closes.
-/
@[inline]
protected partial def forIn
    {β : Type} (incoming : Incoming) (acc : β)
    (step : Chunk → β → Async (ForInStep β)) : Async β := do

  let rec @[specialize] loop (incoming : Incoming) (acc : β) : Async β := do
    if let some chunk ← incoming.recv none then
      match ← step chunk acc with
      | .done res => return res
      | .yield res => loop incoming res
    else
      return acc

  loop incoming acc

/--
Context-aware iteration over chunks until the channel closes.
-/
@[inline]
protected partial def forIn'
    {β : Type} (incoming : Incoming) (acc : β)
    (step : Chunk → β → ContextAsync (ForInStep β)) : ContextAsync β := do

  let rec @[specialize] loop (incoming : Incoming) (acc : β) : ContextAsync β := do
    let data ← Selectable.one #[
      .case incoming.recvSelector pure,
      .case (← ContextAsync.doneSelector) (fun _ => pure none),
    ]

    if let some chunk := data then
      match ← step chunk acc with
      | .done res => return res
      | .yield res => loop incoming res
    else
      return acc

  loop incoming acc

/--
Reads all remaining chunks and decodes them into `α`.
-/
partial def readAll
    [FromByteArray α]
    (incoming : Incoming)
    (maximumSize : Option UInt64 := none) :
    ContextAsync α := do
  let rec loop (result : ByteArray) : ContextAsync ByteArray := do
    let data ← Selectable.one #[
      .case incoming.recvSelector pure,
      .case (← ContextAsync.doneSelector) (fun _ => pure none),
    ]

    match data with
    | none => return result
    | some chunk =>
      let result := result ++ chunk.data
      if let some max := maximumSize then
        if result.size.toUInt64 > max then
          throw (.userError s!"body exceeded maximum size of {max} bytes")
      loop result

  let result ← loop ByteArray.empty

  match FromByteArray.fromByteArray result with
  | .ok a => return a
  | .error msg => throw (.userError msg)

end Incoming

namespace Outgoing

private def collapseForSend
    (outgoing : Outgoing)
    (chunk : Chunk)
    (incomplete : Bool) : BaseIO (Except IO.Error (Option Chunk)) := do
  outgoing.state.atomically do
    Channel.pruneFinishedWaiters
    let st ← get

    if st.closed then
      return .error (.userError "channel closed")

    let merged := match st.pendingIncompleteChunk with
      | some pending => Channel.mergeChunks pending chunk
      | none => chunk

    if incomplete then
      set { st with pendingIncompleteChunk := some merged }
      return .ok none
    else
      set { st with pendingIncompleteChunk := none }
      return .ok (some merged)

private def send' (outgoing : Outgoing) (chunk : Chunk) : BaseIO (AsyncTask Unit) := do
  outgoing.state.atomically do
    Channel.pruneFinishedWaiters
    while true do
      let st ← get

      if st.closed then
        return Task.pure (.error (IO.Error.userError "channel closed"))

      if let some consumer := st.pendingConsumer then
        let success ← consumer.resolve (some chunk)
        if success then
          set {
            st with
            pendingConsumer := none
            knownSize := Channel.decreaseKnownSize st.knownSize chunk
          }
          return AsyncTask.pure ()
        else
          set { st with pendingConsumer := none }
      else if st.queuedSize < st.capacity then
        set {
          st with
          queuedChunks := st.queuedChunks.enqueue chunk
          queuedSize := st.queuedSize + 1
        }
        return AsyncTask.pure ()
      else
        if st.pendingProducer.isSome then
          return Task.pure (.error (IO.Error.userError "only one blocked producer is allowed"))

        let promise ← IO.Promise.new
        set { st with pendingProducer := some { chunk, promise } }
        return promise.result?.map (sync := true) fun
          | none => .error (IO.Error.userError "the promise linked to the producer was dropped")
          | some true => .ok ()
          | some false => .error (IO.Error.userError "channel closed")
    return Task.pure (.error (IO.Error.userError "unreachable"))

/--
Sends a chunk.

If `incomplete := true`, the chunk is buffered and collapsed with subsequent chunks, and is not
delivered to the receiver yet.
If `incomplete := false`, any buffered incomplete pieces are collapsed with this chunk and the
single merged chunk is sent.
-/
def send (outgoing : Outgoing) (chunk : Chunk) (incomplete : Bool := false) : Async Unit := do
  if chunk.data.isEmpty ∧ chunk.extensions.isEmpty then
    return

  match (← collapseForSend outgoing chunk incomplete) with
  | .error err =>
      throw err
  | .ok none =>
      pure ()
  | .ok (some toSend) =>
      let res ← send' outgoing toSend
      await res

/--
Alias for `send`.
-/
def writeChunk (outgoing : Outgoing) (chunk : Chunk) : Async Unit :=
  outgoing.send chunk

/--
Closes the channel.
-/
def close (outgoing : Outgoing) : Async Unit :=
  outgoing.state.atomically do
    Channel.close'

/--
Checks whether the channel is closed.
-/
@[always_inline, inline]
def isClosed (outgoing : Outgoing) : Async Bool :=
  outgoing.state.atomically do
    return (← get).closed

/--
Returns true when a consumer is currently blocked waiting for data.
-/
def hasInterest (outgoing : Outgoing) : Async Bool :=
  outgoing.state.atomically do
    Channel.pruneFinishedWaiters
    Channel.hasInterest'

/--
Gets the known size if available.
-/
@[always_inline, inline]
def getKnownSize (outgoing : Outgoing) : Async (Option Body.Length) :=
  outgoing.state.atomically do
    return (← get).knownSize

/--
Sets known size metadata.
-/
@[always_inline, inline]
def setKnownSize (outgoing : Outgoing) (size : Option Body.Length) : Async Unit :=
  outgoing.state.atomically do
    modify fun st => { st with knownSize := size }

open Internal.IO.Async in
/--
Creates a selector that resolves when consumer interest is present.
Returns `true` when a consumer is waiting, `false` when the channel closes first.
-/
def interestSelector (outgoing : Outgoing) : Selector Bool where
  tryFn := do
    outgoing.state.atomically do
      Channel.pruneFinishedWaiters
      let st ← get
      if st.pendingConsumer.isSome then
        return some true
      else if st.closed then
        return some false
      else
        return none

  registerFn waiter := do
    outgoing.state.atomically do
      Channel.pruneFinishedWaiters
      let st ← get

      if st.pendingConsumer.isSome then
        let lose := return ()
        let win promise := do
          promise.resolve (.ok true)
        waiter.race lose win
      else if st.closed then
        let lose := return ()
        let win promise := do
          promise.resolve (.ok false)
        waiter.race lose win
      else if st.interestWaiter.isSome then
        throw (.userError "only one blocked interest selector is allowed")
      else
        set { st with interestWaiter := some waiter }

  unregisterFn := do
    outgoing.state.atomically do
      Channel.pruneFinishedWaiters

end Outgoing

/--
Creates a body from a producer function.
Returns the receive-side handle immediately and runs `gen` in a detached task.
The channel is always closed when `gen` returns or throws.
Errors from `gen` are not rethrown here; consumers observe end-of-stream via `recv = none`.
-/
def stream (gen : Outgoing → Async Unit) : Async Incoming := do
  let (outgoing, incoming) ← mkChannel
  background <| do
    try
      gen outgoing
    finally
      outgoing.close
  return incoming

/--
Creates a body from a fixed byte array.
-/
def fromBytes (content : ByteArray) : Async Incoming := do
  let (outgoing, incoming) ← mkChannel
  outgoing.setKnownSize (some (.fixed content.size))
  if content.size > 0 then
    outgoing.state.atomically do
      let st ← get
      set {
        st with
        queuedChunks := st.queuedChunks.enqueue (Chunk.ofByteArray content)
        queuedSize := st.queuedSize + 1
      }
  outgoing.close
  return incoming

/--
Creates an empty body.
-/
def empty : Async Incoming := do
  let (outgoing, incoming) ← mkChannel
  outgoing.setKnownSize (some (.fixed 0))
  outgoing.close
  return incoming

instance : ForIn Async Incoming Chunk where
  forIn := Incoming.forIn

instance : ForIn ContextAsync Incoming Chunk where
  forIn := Incoming.forIn'

end Std.Http.Body

namespace Std.Http.Request.Builder
open Internal.IO.Async

/--
Builds a request with a streaming body generator.
-/
def stream
    (builder : Builder)
    (gen : Body.Outgoing → Async Unit) :
    Async (Request Body.Outgoing) := do
  let incoming ← Body.stream gen
  return builder.body (Body.Internal.incomingToOutgoing incoming)

end Std.Http.Request.Builder

namespace Std.Http.Response.Builder
open Internal.IO.Async

/--
Builds a response with a streaming body generator.
-/
def stream
    (builder : Builder)
    (gen : Body.Outgoing → Async Unit) :
    Async (Response Body.Outgoing) := do
  let incoming ← Body.stream gen
  return builder.body (Body.Internal.incomingToOutgoing incoming)

end Std.Http.Response.Builder
