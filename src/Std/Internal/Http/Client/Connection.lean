/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Internal.Async.TCP
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
  The server connection
  -/
  socket : α

  /--
  The processing machine for HTTP 1.1
  -/
  machine : Protocol.H1.Machine .response

/--
A request packet to be sent through the persistent connection channel
-/
structure RequestPacket where

  /--
  The HTTP request to be sent
  -/
  request : Request Body

  /--
  A promise that resolves to the HTTP response once received
  -/
  responsePromise : IO.Promise (Except IO.Error (Response Body))

  /--
  A token used to cancel the request if needed
  -/
  cancellationToken : Std.CancellationToken

namespace RequestPacket

/--
Resolve the response promise with an error.
-/
def onError (packet : RequestPacket) (error : IO.Error) : IO Unit :=
  packet.responsePromise.resolve (.error error)

/--
Resolve the response promise with a successful response.
-/
def onResponse (packet : RequestPacket) (response : Response Body) : IO Unit :=
  packet.responsePromise.resolve (.ok response)

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
  Shutdown Promise, resolves when the connection shuts down.
  -/
  shutdown : IO.Promise Unit

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

  Async.ofPromise (pure responsePromise)

/--
Close the persistent connection by closing the request channel.
-/
def close (pc : PersistentConnection α) : Async Unit := do
  pc.requestChannel.close

end PersistentConnection

namespace Connection

private inductive Recv
  | bytes (x : Option ByteArray)
  | timeout

private def receiveWithTimeout [Transport α] (socket : α) (expect : UInt64)
    (timeoutMs : Millisecond.Offset) :
  Async Recv := do
    Selectable.one #[
      .case (Transport.recvSelector socket expect) (fun x => pure <| .bytes x),
      .case (← Selector.sleep timeoutMs) (fun _ => pure <| .timeout)]

private def processNeedMoreData
    [Transport α] (config : Client.Config) (socket : α) (expect : Option Nat) :
    Async (Except Protocol.H1.Machine.Error (Option ByteArray)) := do
  try
    let expect := expect
      |>.getD config.defaultRequestBufferSize
      |>.min config.maxRecvChunkSize

    let data ← receiveWithTimeout socket expect.toUInt64 config.readTimeout

    match data with
    | .bytes (some bytes) => pure (.ok <| some bytes)
    | .bytes none => pure (.ok <| none)
    | .timeout => pure (.error Protocol.H1.Machine.Error.timeout)

  catch _ =>
    pure (.error Protocol.H1.Machine.Error.timeout)

private def handle [Transport α] (connection : Connection α) (config : Client.Config)
    (requestChannel : CloseableChannel RequestPacket) : Async Unit := do

  let mut machine := connection.machine
  let mut running := true
  let socket := connection.socket

  let mut responseStream ← Body.ByteStream.emptyWithCapacity
  let mut requestTimer ← Interval.mk config.requestTimeout.val config.requestTimeout.property
  let mut connectionTimer ← Sleep.mk config.keepAliveTimeout

  let mut currentRequest : Option RequestPacket := none
  let mut receivedResponse := false
  let mut reqStream := none
  let mut waitingForRequest := true

  -- Wait for the first tick that is immediate
  requestTimer.tick

  let mut requestTimerTask ← async requestTimer.tick
  let connectionTimerTask ← async connectionTimer.wait

  while running do

    if waitingForRequest then
      match ← await (← requestChannel.recv) with
      | some packet =>
        currentRequest := some packet
        waitingForRequest := false

        machine := machine.sendMessage packet.request.head

        match packet.request.body with
        | .bytes data => machine := machine.writeUserData data |>.closeWriter
        | .zero => machine := machine.closeWriter
        | .stream stream => do
          if let some size ← stream.getKnownSize then
            machine := machine.setKnownSize size
          reqStream := some stream

        requestTimer.reset

      | none =>
        running := false
        continue

    machine := machine.processRead.processWrite

    let (newMachine, events) := machine.takeEvents
    machine := newMachine

    -- Sends the output of the machine to the socket in a vectored write.
    if let some (newMachine, data) := machine.takeOutput then
      machine := newMachine

      if data.size > 0 then
        try
          Transport.sendAll socket data.data
        catch e =>
          if let some packet := currentRequest then
            packet.onError e
          running := false

    for event in events do
      match event with
      | .needMoreData expect => do
        try
          match ← processNeedMoreData config socket expect with
          | .ok (some bs) =>
            machine := machine.feed bs
          | .ok none =>
            machine := machine.setFailure .connectionClosed
          | .error _ => do
            machine := machine.setFailure .timeout
        catch e =>
          if let some packet := currentRequest then
            packet.onError e
          running := false

      | .endHeaders head => do
        if let some (.fixed n) := Protocol.H1.Machine.getMessageSize head then
          responseStream.setKnownSize (some n)

        receivedResponse := true

        if let some packet := currentRequest then
          let response := { head := machine.reader.messageHead, body := some (.stream responseStream) }
          packet.onResponse response

      | .gotData final data =>
        discard <| responseStream.send data.toByteArray

        if final then
          responseStream.close

      | .chunkExt _ =>
        pure ()

      | .failed e =>
        if let some packet := currentRequest then
          packet.onError (.userError (toString e))
        pure ()

      | .close =>
        running := false

      | .next =>
        -- Request/response cycle complete, ready for next request
        requestTimer.reset
        responseStream ← Body.ByteStream.emptyWithCapacity
        reqStream := none
        receivedResponse := false
        currentRequest := none
        waitingForRequest := true

    -- Sends data from the request body.
    if let some stream := reqStream then
      if machine.isWriterOpened then
        if machine.isReaderComplete ∧ events.isEmpty then
          if let some data ← stream.recv then
            machine := machine.writeUserData data
          else
            machine := machine.closeWriter
        else
          if ← stream.isClosed then
            pure ()
          else
            match ← stream.tryRecv with
            | some res => machine := machine.writeUserData res
            | none => machine := machine.closeWriter

    -- Checks for things that can close the connection.
    if ¬ waitingForRequest then
      if (← requestTimerTask.isFinished) ∨ (← connectionTimerTask.isFinished) then
        machine := machine.setFailure .timeout
        if let some packet := currentRequest then
          packet.onError (.userError "timeout")
        running := false

  -- End of the connection
  connectionTimer.stop
  requestTimer.stop

  requestChannel.close

  while true do
    if let some x ← requestChannel.tryRecv then
      x.onError (.userError "connection closed, cannot send more requests")
    else
      break



end Connection

/--
Create a persistent connection that can handle multiple sequential requests.

# Example

```lean
-- Connect to a server
let socket ← Socket.mk
socket.connect serverAddr

-- Create persistent connection
let pc ← createPersistentConnection socket config

-- Spawn the connection handler
async (pc.connection.handlePersistent pc.config pc.requestChannel)

-- Send multiple requests
pc.send request1 (fun response => IO.println s!"Response 1: {response.head.status}")
pc.send request2 (fun response => IO.println s!"Response 2: {response.head.status}")

-- Close when done
pc.close
```
-/
def createPersistentConnection [Transport t] (client : t) (config : Client.Config := {}) : Async (PersistentConnection t) := do
  let requestChannel ← CloseableChannel.new
  let connection := Connection.mk client { config := config.toH1Config }
  let shutdown ← IO.Promise.new

  let conn := { connection, requestChannel, shutdown }

  background (Connection.handle connection config requestChannel)

  return conn


end Std.Http.Client
