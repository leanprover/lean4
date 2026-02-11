/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Sync
public import Std.Internal.Async
public import Std.Internal.Http.Data.Request
public import Std.Internal.Http.Data.Response
public import Std.Internal.Http.Data.Chunk
public import Std.Internal.Http.Data.Body.Basic
public import Std.Internal.Http.Data.Body.Length
public import Init.Data.Queue
public import Init.Data.ByteArray

public section

/-!
# Body.Stream

A `Stream` represents an asynchronous channel for streaming data in chunks. It provides an
interface for producers and consumers to exchange chunks with optional metadata (extensions),
making it suitable for HTTP chunked transfer encoding and other streaming scenarios.
-/

namespace Std.Http.Body
open Std Internal IO Async

set_option linter.all true

namespace Stream

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

end Stream

/--
A channel for chunks with support for chunk extensions.
-/
structure Stream where
  private mk ::
  private state : Mutex Stream.State
deriving Nonempty, TypeName

namespace Stream

/--
Creates a new Stream with a specified capacity.
-/
def emptyWithCapacity (capacity : Nat := 128) : Async Stream := do
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
Creates a new Stream with default capacity.
-/
@[always_inline, inline]
def empty : Async Stream :=
  emptyWithCapacity

private def decreaseKnownSize (knownSize : Option Body.Length) (chunk : Chunk) : Option Body.Length :=
  match knownSize with
  | some (.fixed res) => some (Body.Length.fixed (res - chunk.data.size))
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
def tryRecv (stream : Stream) : Async (Option Chunk) :=
  stream.state.atomically do
    tryRecv'

private def recv' (stream : Stream) : BaseIO (Task (Option Chunk)) := do
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
def recv (stream : Stream) (_count : Option UInt64) : Async (Option Chunk) := do
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

private def trySend (stream : Stream) (chunk : Chunk) : BaseIO Bool := do
  stream.state.atomically do
    if (← get).closed then
      return false
    else
      trySend' chunk

private def send' (stream : Stream) (chunk : Chunk) : BaseIO (Task (Except IO.Error Unit)) := do
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
def send (stream : Stream) (chunk : Chunk) : Async Unit := do
  if chunk.data.isEmpty then
    return

  let res : AsyncTask _ ← send' stream chunk
  await res

/--
Gets the known size of the stream if available. Returns `none` if the size is not known.
-/
@[always_inline, inline]
def getKnownSize (stream : Stream) : Async (Option Body.Length) := do
  stream.state.atomically do
    return (← get).knownSize

/--
Sets the known size of the stream. Use this when the total expected size is known ahead of time.
-/
@[always_inline, inline]
def setKnownSize (stream : Stream) (size : Option Body.Length) : Async Unit := do
  stream.state.atomically do
    modify fun st => { st with knownSize := size }

/--
Closes the stream, preventing further sends and causing pending/future
recv operations to return `none` when no data is available.
-/
def close (stream : Stream) : Async Unit := do
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
def isClosed (stream : Stream) : Async Bool := do
  stream.state.atomically do
    return (← get).closed

@[inline]
private def recvReady' [Monad m] [MonadLiftT (ST IO.RealWorld) m] :
    AtomicT State m Bool := do
  let st ← get
  return !st.values.isEmpty || st.closed

open Internal.IO.Async in

/--
Creates a `Selector` that resolves once the `Stream` has data available and provides that data.
-/
def recvSelector (stream : Stream) : Selector (Option Chunk) where
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
Sends data to the stream and writes a chunk to it.
-/
def writeChunk (stream : Stream) (chunk : Chunk) : Async Unit :=
  stream.send chunk

/--
Iterate over the stream content in chunks, processing each chunk with the given step function.
-/
@[inline]
protected partial def forIn
    {β : Type} (stream : Stream) (acc : β)
    (step : Chunk → β → Async (ForInStep β)) : Async β := do

  let rec @[specialize] loop (stream : Stream) (acc : β) : Async β := do
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
    {β : Type} (stream : Stream) (acc : β)
    (step : Chunk → β → ContextAsync (ForInStep β)) : ContextAsync β := do

  let rec @[specialize] loop (stream : Stream) (acc : β) : ContextAsync β := do
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

instance : ForIn Async Stream Chunk where
  forIn := Std.Http.Body.Stream.forIn

instance : ForIn ContextAsync Stream Chunk where
  forIn := Std.Http.Body.Stream.forIn'

/--
Reads all remaining chunks from the stream and returns their concatenated data as a `ByteArray`.
Blocks until the stream is closed.
-/
partial def readAll (stream : Stream) : ContextAsync ByteArray := do
  let mut result := ByteArray.empty
  for chunk in stream do
    result := result ++ chunk.data
  return result

/--
Reads all remaining chunks from the stream and returns their concatenated data as a `String`.
Blocks until the stream is closed. The data is interpreted as UTF-8.
-/
partial def readAllString (stream : Stream) : ContextAsync String := do
  return String.fromUTF8! (← stream.readAll)

end Std.Http.Body.Stream

namespace Std.Http.Request.Builder
open Internal.IO.Async

/--
Builds a request with a streaming body. The generator function receives the `Stream` and
can write chunks to it asynchronously.
-/
def stream (builder : Builder) (gen : Body.Stream → Async Unit) : Async (Request Body.Stream) := do
  let body ← Body.Stream.empty
  background (gen body)
  return { head := builder.head, body }

/--
Builds a request with an empty body.
-/
def blank (builder : Builder) : Async (Request Body.Stream) := do
  let body ← Body.Stream.empty
  body.setKnownSize (some (.fixed 0))
  body.close
  return { head := builder.head, body }

/--
Builds a request with a text body. Sets Content-Type to text/plain and Content-Length automatically.
-/
def text (builder : Builder) (content : String) : Async (Request Body.Stream) := do
  let bytes := content.toUTF8
  let body ← Body.Stream.empty
  body.setKnownSize (some (.fixed bytes.size))
  body.send (Chunk.ofByteArray bytes)
  body.close
  let headers := builder.head.headers
    |>.insert Header.Name.contentType (Header.Value.ofString! "text/plain; charset=utf-8")
    |>.insert Header.Name.contentLength (Header.Value.ofString! (toString bytes.size))
  return { head := { builder.head with headers }, body }

/--
Builds a request with a binary body. Sets Content-Type to application/octet-stream and Content-Length automatically.
-/
def bytes (builder : Builder) (content : ByteArray) : Async (Request Body.Stream) := do
  let body ← Body.Stream.empty
  body.setKnownSize (some (.fixed content.size))
  body.send (Chunk.ofByteArray content)
  body.close
  let headers := builder.head.headers
    |>.insert Header.Name.contentType (Header.Value.ofString! "application/octet-stream")
    |>.insert Header.Name.contentLength (Header.Value.ofString! (toString content.size))
  return { head := { builder.head with headers }, body }

/--
Builds a request with a JSON body. Sets Content-Type to application/json and Content-Length automatically.
-/
def json (builder : Builder) (content : String) : Async (Request Body.Stream) := do
  let bytes := content.toUTF8
  let body ← Body.Stream.empty
  body.setKnownSize (some (.fixed bytes.size))
  body.send (Chunk.ofByteArray bytes)
  body.close
  let headers := builder.head.headers
    |>.insert Header.Name.contentType (Header.Value.ofString! "application/json")
    |>.insert Header.Name.contentLength (Header.Value.ofString! (toString bytes.size))
  return { head := { builder.head with headers }, body }

/--
Builds a request with an HTML body. Sets Content-Type to text/html and Content-Length automatically.
-/
def html (builder : Builder) (content : String) : Async (Request Body.Stream) := do
  let bytes := content.toUTF8
  let body ← Body.Stream.empty
  body.setKnownSize (some (.fixed bytes.size))
  body.send (Chunk.ofByteArray bytes)
  body.close
  let headers := builder.head.headers
    |>.insert Header.Name.contentType (Header.Value.ofString! "text/html; charset=utf-8")
    |>.insert Header.Name.contentLength (Header.Value.ofString! (toString bytes.size))
  return { head := { builder.head with headers }, body }

/--
Builds a request with an empty body (alias for blank).
-/
def noBody (builder : Builder) : Async (Request Body.Stream) :=
  builder.blank

end Std.Http.Request.Builder

namespace Std.Http.Response.Builder
open Internal.IO.Async

/--
Builds a response with a streaming body. The generator function receives the `Stream` and
can write chunks to it asynchronously.
-/
def stream (builder : Builder) (gen : Body.Stream → Async Unit) : Async (Response Body.Stream) := do
  let body ← Body.Stream.empty
  background (gen body)
  return { head := builder.head, body }

/--
Builds a response with an empty body.
-/
def blank (builder : Builder) : Async (Response Body.Stream) := do
  let body ← Body.Stream.empty
  body.setKnownSize (some (.fixed 0))
  body.close
  return { head := builder.head, body }

/--
Builds a response with a text body. Sets Content-Type to text/plain and Content-Length automatically.
-/
def text (builder : Builder) (content : String) : Async (Response Body.Stream) := do
  let bytes := content.toUTF8
  let body ← Body.Stream.empty
  body.setKnownSize (some (.fixed bytes.size))
  body.send (Chunk.ofByteArray bytes)
  body.close
  let headers := builder.head.headers
    |>.insert Header.Name.contentType (Header.Value.ofString! "text/plain; charset=utf-8")
    |>.insert Header.Name.contentLength (Header.Value.ofString! (toString bytes.size))
  return { head := { builder.head with headers }, body }

/--
Builds a response with a binary body. Sets Content-Type to application/octet-stream and Content-Length automatically.
-/
def bytes (builder : Builder) (content : ByteArray) : Async (Response Body.Stream) := do
  let body ← Body.Stream.empty
  body.setKnownSize (some (.fixed content.size))
  body.send (Chunk.ofByteArray content)
  body.close
  let headers := builder.head.headers
    |>.insert Header.Name.contentType (Header.Value.ofString! "application/octet-stream")
    |>.insert Header.Name.contentLength (Header.Value.ofString! (toString content.size))
  return { head := { builder.head with headers }, body }

/--
Builds a response with a JSON body. Sets Content-Type to application/json and Content-Length automatically.
-/
def json (builder : Builder) (content : String) : Async (Response Body.Stream) := do
  let bytes := content.toUTF8
  let body ← Body.Stream.empty
  body.setKnownSize (some (.fixed bytes.size))
  body.send (Chunk.ofByteArray bytes)
  body.close
  let headers := builder.head.headers
    |>.insert Header.Name.contentType (Header.Value.ofString! "application/json")
    |>.insert Header.Name.contentLength (Header.Value.ofString! (toString bytes.size))
  return { head := { builder.head with headers }, body }

/--
Builds a response with an HTML body. Sets Content-Type to text/html and Content-Length automatically.
-/
def html (builder : Builder) (content : String) : Async (Response Body.Stream) := do
  let bytes := content.toUTF8
  let body ← Body.Stream.empty
  body.setKnownSize (some (.fixed bytes.size))
  body.send (Chunk.ofByteArray bytes)
  body.close
  let headers := builder.head.headers
    |>.insert Header.Name.contentType (Header.Value.ofString! "text/html; charset=utf-8")
    |>.insert Header.Name.contentLength (Header.Value.ofString! (toString bytes.size))
  return { head := { builder.head with headers }, body }

/--
Builds a response with an empty body (alias for blank).
-/
def noBody (builder : Builder) : Async (Response Body.Stream) :=
  builder.blank

end Std.Http.Response.Builder
