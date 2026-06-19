/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Sync
public import Std.Async
public import Std.Http.Data.Request
public import Std.Http.Data.Response
public import Std.Http.Data.Chunk
public import Std.Http.Data.Body.Basic
public import Std.Http.Data.Body.Any
public import Init.Data.ByteArray

public section

/-!
# Body.Stream

This module defines a zero-buffer rendezvous body channel (`Body.Stream`) that supports
both sending and receiving chunks.

There is no queue and no capacity. A send waits for a receiver and a receive waits for a sender.
At most one blocked producer and one blocked consumer are supported.
-/

namespace Std.Http

namespace Body

open Std Async

set_option linter.all true

namespace Channel

open Async in
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

  /--
  Resolved with `true` when consumed by a receiver, `false` when the channel closes.
  -/
  done : IO.Promise Bool

open Async in
private def resolveInterestWaiter (waiter : Waiter Bool) (x : Bool) : BaseIO Bool := do
  let lose := return false
  let win promise := do
    promise.resolve (.ok x)
    return true
  waiter.race lose win

private structure State where
  /--
  A single blocked producer waiting for a receiver.
  -/
  pendingProducer : Option Producer

  /--
  A single blocked consumer waiting for a producer.
  -/
  pendingConsumer : Option Consumer

  /--
  A waiter for `Stream.interestSelector`.
  -/
  interestWaiter : Option (Async.Waiter Bool)

  /--
  Whether the channel is closed.
  -/
  closed : Bool

  /--
  Known size of the stream if available.
  -/
  knownSize : Option Body.Length

  /--
  Buffered partial chunk data accumulated from `Stream.send ... (incomplete := true)`.
  These partial pieces are collapsed and emitted as a single chunk on the next complete send.
  -/
  pendingIncompleteChunk : Option Chunk := none
deriving Nonempty

end Channel

/--
A zero-buffer rendezvous body channel that supports both sending and receiving chunks.
-/
structure Stream where
  private mk ::
  private state : Mutex Channel.State
deriving Nonempty, TypeName

/--
Creates a rendezvous body stream.
-/
def mkStream : Async Stream := do
  let state ← Mutex.new {
    pendingProducer := none
    pendingConsumer := none
    interestWaiter := none
    closed := false
    knownSize := none
  }
  return { state }

namespace Channel

private def decreaseKnownSize (knownSize : Option Body.Length) (chunk : Chunk) : Option Body.Length :=
  match knownSize with
  | some (.fixed res) => some (Body.Length.fixed (res - chunk.data.size))
  | _ => knownSize

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
  return st.pendingProducer.isSome || st.closed

private def hasInterest' [Monad m] [MonadLiftT (ST IO.RealWorld) m] :
    AtomicT State m Bool := do
  let st ← get
  return st.pendingConsumer.isSome

private def tryRecv' [Monad m] [MonadLiftT (ST IO.RealWorld) m] [MonadLiftT BaseIO m] :
    AtomicT State m (Option Chunk) := do
  let st ← get
  if let some producer := st.pendingProducer then
    set {
      st with
      pendingProducer := none
      knownSize := decreaseKnownSize st.knownSize producer.chunk
    }
    discard <| producer.done.resolve true
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

  if let some waiter := st.interestWaiter then
    discard <| resolveInterestWaiter waiter false

  if let some producer := st.pendingProducer then
    discard <| producer.done.resolve false

  set {
    st with
    pendingProducer := none
    pendingConsumer := none
    interestWaiter := none
    pendingIncompleteChunk := none
    closed := true
  }

end Channel

namespace Stream

/--
Attempts to receive a chunk from the channel without blocking.
Returns `some chunk` only when a producer is already waiting.
-/
def tryRecv (stream : Stream) : Async (Option Chunk) :=
  stream.state.atomically do
    Channel.pruneFinishedWaiters
    Channel.tryRecv'

/--
Non-blocking receive for the `Body` typeclass. Returns `none` when no producer is
waiting and the channel is still open, `some (some chunk)` when data is ready,
or `some none` at end-of-stream (channel closed with no pending producer).
-/
def tryRecvBody (stream : Stream) : Async (Option (Option Chunk)) :=
  stream.state.atomically do
    Channel.pruneFinishedWaiters
    if ← Channel.recvReady' then
      return some (← Channel.tryRecv')
    else
      return none

private def recv' (stream : Stream) : BaseIO (AsyncTask (Option Chunk)) := do
  stream.state.atomically do
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
Receives a chunk from the channel. Blocks until a producer sends one.
Returns `none` if the channel is closed and no producer is waiting.
-/
def recv (stream : Stream) : Async (Option Chunk) := do
  Async.ofAsyncTask (← recv' stream)

/--
Closes the channel.
-/
def close (stream : Stream) : Async Unit :=
  stream.state.atomically do
    Channel.close'

/--
Checks whether the channel is closed.
-/
@[always_inline, inline]
def isClosed (stream : Stream) : Async Bool :=
  stream.state.atomically do
    return (← get).closed

/--
Gets the known size if available.
-/
@[always_inline, inline]
def getKnownSize (stream : Stream) : Async (Option Body.Length) :=
  stream.state.atomically do
    return (← get).knownSize

/--
Sets known size metadata.
-/
@[always_inline, inline]
def setKnownSize (stream : Stream) (size : Option Body.Length) : Async Unit :=
  stream.state.atomically do
    modify fun st => { st with knownSize := size }

open Async in

/--
Creates a selector that resolves when a producer is waiting (or the channel closes).
-/
def recvSelector (stream : Stream) : Selector (Option Chunk) where
  tryFn := do
    stream.state.atomically do
      Channel.pruneFinishedWaiters
      if ← Channel.recvReady' then
        return some (← Channel.tryRecv')
      else
        return none

  registerFn waiter := do
    stream.state.atomically do
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
    stream.state.atomically do
      Channel.pruneFinishedWaiters

/--
Iterates over chunks until the channel closes.
-/
@[inline]
protected partial def forIn
    {β : Type} (stream : Stream) (acc : β)
    (step : Chunk → β → Async (ForInStep β)) : Async β := do

  let rec @[specialize] loop (stream : Stream) (acc : β) : Async β := do
    if let some chunk ← stream.recv then
      match ← step chunk acc with
      | .done res => return res
      | .yield res => loop stream res
    else
      return acc

  loop stream acc

/--
Context-aware iteration over chunks until the channel closes.
-/
@[inline]
protected partial def forIn'
    {β : Type} (stream : Stream) (acc : β)
    (step : Chunk → β → ContextAsync (ForInStep β)) : ContextAsync β := do

  let rec @[specialize] loop (stream : Stream) (acc : β) : ContextAsync β := do
    let data ← Selectable.one #[
      .case stream.recvSelector pure,
      .case (← ContextAsync.doneSelector) (fun _ => pure none),
    ]

    if let some chunk := data then
      match ← step chunk acc with
      | .done res => return res
      | .yield res => loop stream res
    else
      return acc

  loop stream acc

/--
Abstracts over how the next chunk is received, allowing `readAll` to work in both `Async`
(no cancellation) and `ContextAsync` (races with cancellation via `doneSelector`).
-/
class NextChunk (m : Type → Type) where
  /--
  Receives the next chunk, stopping at EOF or (in `ContextAsync`) when the context is cancelled.
  -/
  nextChunk : Stream → m (Option Chunk)

instance : NextChunk Async where
  nextChunk := Stream.recv

instance : NextChunk ContextAsync where
  nextChunk stream := do
    Selectable.one #[
      .case stream.recvSelector pure,
      .case (← ContextAsync.doneSelector) (fun _ => pure none),
    ]

/--
Reads all remaining chunks and decodes them into `α`.

Works in both `Async` (reads until EOF, no cancellation) and `ContextAsync` (also stops if the
context is cancelled).
-/
partial def readAll
    [FromByteArray α]
    [Monad m] [MonadExceptOf IO.Error m] [NextChunk m]
    (stream : Stream)
    (maximumSize : Option UInt64 := none) :
    m α := do

  let rec loop (result : ByteArray) : m ByteArray := do
    match ← NextChunk.nextChunk stream with
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

private def collapseForSend
    (stream : Stream)
    (chunk : Chunk)
    (incomplete : Bool) : BaseIO (Except IO.Error (Option Chunk)) := do

  stream.state.atomically do
    Channel.pruneFinishedWaiters
    let st ← get

    if st.closed then
      return .error (.userError "channel closed")

    let merged := match st.pendingIncompleteChunk with
      | some pending =>
        {
          data := pending.data ++ chunk.data
          extensions := if pending.extensions.isEmpty then chunk.extensions else pending.extensions
        }
      | none => chunk

    if incomplete then
      set { st with pendingIncompleteChunk := some merged }
      return .ok none
    else
      set { st with pendingIncompleteChunk := none }
      return .ok (some merged)

/--
Sends a chunk, retrying if a select-mode consumer races and loses. If no consumer is ready,
installs the chunk as a pending producer and awaits acknowledgement from the receiver.
-/
private partial def send' (stream : Stream) (chunk : Chunk) : Async Unit := do
  let done ← IO.Promise.new
  let result : Except IO.Error (Option Bool) ← stream.state.atomically do
    Channel.pruneFinishedWaiters
    let st ← get

    if st.closed then
      return .error (IO.Error.userError "channel closed")

    if let some consumer := st.pendingConsumer then
      let success ← consumer.resolve (some chunk)

      if success then
        set {
          st with
          pendingConsumer := none
          knownSize := Channel.decreaseKnownSize st.knownSize chunk
        }
        return .ok (some true)
      else
        set { st with pendingConsumer := none }
        return .ok (some false)
    else if st.pendingProducer.isSome then
      return .error (IO.Error.userError "only one blocked producer is allowed")
    else
      set { st with pendingProducer := some { chunk, done } }
      return .ok none

  match result with
  | .error err =>
    throw err
  | .ok (some true) =>
    return ()
  | .ok (some false) =>
    -- The select-mode consumer raced and lost; recurse to allocate a fresh `done` promise.
    send' stream chunk
  | .ok none =>
    match ← await done.result? with
    | some true => return ()
    | _ => throw (IO.Error.userError "channel closed")

/--
Sends a chunk.

If `incomplete := true`, the chunk is buffered and collapsed with subsequent chunks, and is not
delivered to the receiver yet.
If `incomplete := false`, any buffered incomplete pieces are collapsed with this chunk and the
single merged chunk is sent.
-/
def send (stream : Stream) (chunk : Chunk) (incomplete : Bool := false) : Async Unit := do
  match (← collapseForSend stream chunk incomplete) with
  | .error err => throw err
  | .ok none => pure ()
  | .ok (some toSend) =>
    if toSend.data.isEmpty ∧ toSend.extensions.isEmpty then
      return ()

    send' stream toSend

/--
Returns `true` when a consumer is currently blocked waiting for data.
-/
def hasInterest (stream : Stream) : Async Bool :=
  stream.state.atomically do
    Channel.pruneFinishedWaiters
    Channel.hasInterest'

open Async in
/--
Creates a selector that resolves when consumer interest is present.
Returns `true` when a consumer is waiting, `false` when the channel closes first.
-/
def interestSelector (stream : Stream) : Selector Bool where
  tryFn := do
    stream.state.atomically do
      Channel.pruneFinishedWaiters
      let st ← get
      if st.pendingConsumer.isSome then
        return some true
      else if st.closed then
        return some false
      else
        return none

  registerFn waiter := do
    stream.state.atomically do
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
    stream.state.atomically do
      Channel.pruneFinishedWaiters

end Stream

/--
Creates a body from a producer function.
Returns the stream immediately and runs `gen` in a detached task.
The channel is always closed when `gen` returns or throws.
Errors from `gen` are not rethrown here; consumers observe end-of-stream via `recv = none`.
-/
def stream (gen : Stream → Async Unit) : Async Stream := do
  let s ← mkStream
  background <| do
    try
      gen s
    finally
      s.close
  return s

/--
Creates a body from a fixed byte array.
-/
def fromBytes (content : ByteArray) : Async Stream := do
  stream fun s => do
    s.setKnownSize (some (.fixed content.size))
    if content.size > 0 then
      s.send (Chunk.ofByteArray content)

/--
Creates an empty `Stream` body channel (already closed, no data).

Prefer `Body.Empty` when you need a concrete zero-cost type. Use this when the calling
context requires a `Stream` specifically.
-/
def empty : Async Stream := do
  let s ← mkStream
  s.setKnownSize (some (.fixed 0))
  s.close
  return s

instance : ForIn Async Stream Chunk where
  forIn := Stream.forIn

instance : ForIn ContextAsync Stream Chunk where
  forIn := Stream.forIn'

instance : Http.Body Stream where
  recv := Stream.recv
  close := Stream.close
  isClosed := Stream.isClosed
  recvSelector := Stream.recvSelector
  tryRecv := Stream.tryRecvBody
  getKnownSize := Stream.getKnownSize
  setKnownSize := Stream.setKnownSize

instance : Coe Stream Any := ⟨Any.ofBody⟩

instance : Coe (Response Stream) (Response Any) where
  coe f := { f with }

instance : Coe (ContextAsync (Response Stream)) (ContextAsync (Response Any)) where
  coe action := do
    let response ← action
    pure (response : Response Any)

instance : Coe (Async (Response Stream)) (ContextAsync (Response Any)) where
  coe action := do
    let response ← action
    pure (response : Response Any)

end Body

namespace Request.Builder

open Async

/--
Builds a request with a streaming body generator.
-/
def stream
    (builder : Builder)
    (gen : Body.Stream → Async Unit) :
    Async (Request Body.Stream) := do
  let s ← Body.stream gen
  return Request.Builder.body builder s

end Request.Builder

namespace Response.Builder
open Async

/--
Builds a response with a streaming body generator.
-/
def stream
    (builder : Builder)
    (gen : Body.Stream → Async Unit) :
    Async (Response Body.Stream) := do
  let s ← Body.stream gen
  return Response.Builder.body builder s

end Response.Builder
