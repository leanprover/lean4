/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Internal.Async.TCP
public import Std.Internal.Async.ContextAsync
public import Std.Internal.Http.Transport
public import Std.Internal.Http.Protocol.H1
public import Std.Internal.Http.Client.Config

public section

namespace Std
namespace Http
namespace Client

open Std Internal IO Async TCP
open Time

/-!
# Connection

This module defines a `Client.Connection` that is a structure used to handle a single HTTP connection with
possibly multiple requests/responses from the client side.
-/

set_option linter.all true

/--
A single HTTP client connection.
-/
public structure Connection (α : Type) where
  /--
  The server connection.
  -/
  socket : α

  /--
  The processing machine for HTTP 1.1
  -/
  machine : Protocol.H1.Machine .sending

/--
A request packet to be sent through the persistent connection channel.
-/
structure RequestPacket where
  /--
  The request to send
  -/
  request : Request Body

  /--
  Promise to resolve with the response
  -/
  responsePromise : IO.Promise (Except Error (Response Body))

  /--
  Cancellation token for this request
  -/
  cancellationToken : Std.CancellationToken

namespace RequestPacket

/--
Resolve the response promise with an error.
-/
def onError (packet : RequestPacket) (error : Error) : BaseIO Unit :=
  discard <| packet.responsePromise.resolve (.error error)

/--
Resolve the response promise with a successful response.
-/
def onResponse (packet : RequestPacket) (response : Response Body) : BaseIO Unit :=
  discard <| packet.responsePromise.resolve (.ok response)

end RequestPacket

/--
A persistent HTTP client connection that handles multiple sequential requests.
-/
public structure PersistentConnection (α : Type) where
  /--
  The underlying connection.
  -/
  connection : Connection α

  /--
  Channel for sending new requests.
  -/
  requestChannel : CloseableChannel RequestPacket

  /--
  Shutdown Future, resolves when the connection shuts down.
  -/
  shutdown : Std.Future Unit

namespace PersistentConnection

/--
Send a request through the persistent connection.
-/
def send [Transport α] (pc : PersistentConnection α) (request : Request Body) : Async (Response Body) := do
  let responsePromise ← IO.Promise.new
  let cancellationToken ← Std.CancellationToken.new

  let task ← pc.requestChannel.send { request, responsePromise, cancellationToken }

  let .ok _ ← await task
    | throw (.userError "connection closed, cannot send more requests")

  let result ← await (responsePromise.result!)

  match result with
  | .ok response => pure response
  | .error e => throw e

/--
Close the persistent connection by closing the request channel.
-/
def close (pc : PersistentConnection α) : Async Unit := do
  pc.requestChannel.close

end PersistentConnection

namespace Connection

private inductive Recv (t : Type)
  | bytes (x : Option ByteArray)
  | channel (x : Option Chunk)
  | packet (x : Option RequestPacket)
  | timeout
  | shutdown
  | close
deriving Repr

private def receiveWithTimeout
    [Transport α]
    [Body t Chunk]
    (socket : Option α)
    (expect : UInt64)
    (requestStream : Option t)
    (response : Option (Std.Channel (Except Error (Response t))))
    (timeoutMs : Millisecond.Offset)
    (keepAliveTimeoutMs : Option Millisecond.Offset)
    (connectionContext : CancellationContext) : Async (Recv t) : Async Recv := do

  let mut baseSelectables := #[
    .case connectionContext.doneSelector (fun _ => do
      let reason ← connectionContext.getCancellationReason
      match reason with
      | some .deadline => pure .timeout
      | _ => pure .shutdown)
  ]

  baseSelectables := baseSelectables.push (.case (Transport.recvSelector socket expect) (Recv.bytes · |> pure))

  -- Add timeout for waiting on socket data
  baseSelectables := baseSelectables.push (.case (← Selector.sleep timeoutMs) (fun _ => pure .timeout))

  if let some stream := requestStream then
    baseSelectables := baseSelectables.push (.case stream.recvSelector (Recv.channel · |> pure))

  if let some channel := requestChannel then
    baseSelectables := baseSelectables.push (.case channel.recvSelector (Recv.packet · |> pure))

  Selectable.one baseSelectables

private def processNeedMoreData
    [Transport α]
    (config : Config)
    (socket : α)
    (expect : Option Nat)
    (requestStream : Option Body.ByteStream)
    (requestChannel : Option (CloseableChannel RequestPacket))
    (timeout : Millisecond.Offset)
    (connectionContext : CancellationContext) : Async Recv := do
  try
    let expectedBytes := expect
      |>.getD config.defaultRequestBufferSize
      |>.min config.maxRecvChunkSize
      |>.toUInt64

    receiveWithTimeout socket expectedBytes requestStream requestChannel timeout connectionContext
  catch _ =>
    pure .close

private def handleError (machine : Protocol.H1.Machine .sending) (currentRequest : Option RequestPacket) : BaseIO (Protocol.H1.Machine .sending) := do
  let machine := machine.closeWriter.closeReader.noMoreInput
  if let some packet := currentRequest then
    packet.onError (.userError "timeout")

  return machine

private def handle
    [Transport α]
    (connection : Connection α)
    (config : Config)
    (connectionContext : CancellationContext)
    (requestChannel : CloseableChannel RequestPacket) : Async Unit := do

  let mut machine := connection.machine
  let socket := connection.socket

  let mut responseStream ← Body.ByteStream.emptyWithCapacity
  let mut currentTimeout := config.keepAliveTimeout.val

  let mut currentRequest : Option RequestPacket := none
  let mut reqStream := none
  let mut requiresData := false
  let mut expectData := none
  let mut waitingForRequest := true

  while ¬machine.halted do
    let (newMachine, step) := machine.step

    machine := newMachine

    if step.output.size > 0 then
      try Transport.sendAll socket step.output.data catch _ => break

    for event in step.events do
      match event with
      | .needMoreData expect => do
        requiresData := true
        expectData := expect

      | .needBody => do
        pure ()

      | .needAnswer =>
        pure ()

      | .endHeaders head => do
        currentTimeout := config.readTimeout

        if let some length := Protocol.H1.Machine.getMessageSize head then
          responseStream.setKnownSize (some length)

        if let some packet := currentRequest then
          packet.onResponse { head, body := (.stream responseStream) }

      | .gotData final ext data =>
        try
          responseStream.writeChunk { data := data.toByteArray, extensions := ext }

          if final then
            responseStream.close

        catch _ =>
          pure ()

      | .next => do
        responseStream ← Body.ByteStream.emptyWithCapacity
        reqStream := none
        currentRequest := none
        waitingForRequest := true
        currentTimeout := config.keepAliveTimeout.val

      | .failed e =>
        if let some packet := currentRequest then
          packet.onError (.userError (toString e))

      | .close =>
        pure ()

    if requiresData ∨ waitingForRequest ∨ reqStream.isSome then
      let requestChannelOpt := if waitingForRequest then some requestChannel else none

      requiresData := false

      let event ← processNeedMoreData config socket expectData reqStream requestChannelOpt currentTimeout connectionContext

      match event with
      | .bytes (some bs) =>
        machine := machine.feed bs

      | .bytes none =>
        machine := machine.noMoreInput

      | .channel (some chunk) =>
        machine := machine.sendData #[chunk]

      | .channel none =>
        machine := machine.closeWriter

        if let some stream := reqStream then
          if ¬(← stream.isClosed) then stream.close

        reqStream := none

      | .packet (some packet) =>
        currentRequest := some packet
        waitingForRequest := false
        currentTimeout := config.requestTimeout

        machine := machine.send packet.request.head

        match packet.request.body with
        | .bytes data =>

          machine := machine.sendData #[Chunk.mk data #[]]
          |>.userClosedBody
        | .zero => machine := machine.userClosedBody
        | .stream stream => do
          if let some size ← stream.getKnownSize then
            machine := machine.setKnownSize size
          reqStream := some stream

      | .packet none =>
        break

      | .close =>
        break

      | .timeout =>
        machine ← handleError machine currentRequest

      | .shutdown =>
        machine ← handleError machine currentRequest

  if ¬ (← responseStream.isClosed) then
    responseStream.close

  if let some stream := reqStream then
    if ¬(← stream.isClosed) then
      stream.close

end Connection

/--
Create a persistent connection that can handle multiple sequential requests.

This is the entry point for creating a client connection. It can be used with a `TCP.Socket` or any
other type that implements `Transport` to create an HTTP client capable of handling multiple
sequential requests on a single connection.

# Example

```lean
-- Connect to a server
let socket ← Socket.mk
socket.connect serverAddr

-- Create persistent connection
let pc ← createPersistentConnection socket config

-- Spawn the connection handler in the background
background (pc.connection.handle pc.config (← ContextAsync.getContext) pc.requestChannel)

-- Send multiple requests
let response1 ← pc.send request1
IO.println s!"Response 1: {response1.head.status}"

let response2 ← pc.send request2
IO.println s!"Response 2: {response2.head.status}"

-- Close when done
pc.close
```
-/
def createPersistentConnection [Transport t] (client : t) (config : Config := {}) : Async (PersistentConnection t) := do
  let requestChannel ← CloseableChannel.new
  let connection := Connection.mk client { config := config.toH1Config }
  let shutdown ← Std.Future.new

  let ctx ← CancellationContext.new

  background (Std.Http.Client.Connection.handle connection config ctx requestChannel)

  pure { connection, requestChannel, shutdown }

end Std.Http.Client
