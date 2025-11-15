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
  machine : Protocol.H1.Machine .sending

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
def send (pc : PersistentConnection α) (request : Request Body) : Async (Response Body) := do
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
    (timeoutMs : Millisecond.Offset) (req : Timestamp) (all : Timestamp) :
  Async Recv := do
    Selectable.one #[
      .case (Transport.recvSelector socket expect) (fun x => pure <| .bytes x),
      .case (← Selector.sleep timeoutMs) (fun _ => pure <| .timeout),
      .case (← Selector.sleep (req - (← Timestamp.now) |>.toMilliseconds)) (fun _ => pure <| .timeout),
      .case (← Selector.sleep (all - (← Timestamp.now) |>.toMilliseconds)) (fun _ => pure <| .timeout)]

private def processNeedMoreData
    [Transport α] (config : Config) (socket : α) (expect : Option Nat)
    (req : Timestamp) (all : Timestamp):
    Async (Except Protocol.H1.Error (Option ByteArray)) := do
  try
    let expect := expect
      |>.getD config.defaultRequestBufferSize
      |>.min config.maxRecvChunkSize

    let data ← receiveWithTimeout socket expect.toUInt64 config.readTimeout req all

    match data with
    | .bytes (some bytes) => pure (.ok <| some bytes)
    | .bytes none => pure (.ok <| none)
    | .timeout => pure (.error .timeout)

  catch _ =>
    pure (.error .timeout)

private def handle [Transport α] (connection : Connection α) (config : Client.Config) (requestChannel : CloseableChannel RequestPacket) : Async Unit := do
  let mut machine := connection.machine
  let socket := connection.socket

  let mut responseStream ← Body.ByteStream.emptyWithCapacity
  let mut waitingForRequest := true
  let mut reqStream := none
  let mut requestTimer := (← Timestamp.now) + config.requestTimeout.val
  let mut connectionTimer := (← Timestamp.now) + config.keepAliveTimeout.val

  let mut currentRequest := none

  while ¬machine.halted do
    if waitingForRequest then
      match ← await (← requestChannel.recv) with
      | some packet =>
        currentRequest := some packet
        waitingForRequest := false

        machine := machine.send packet.request.head

        match packet.request.body with
        | .bytes data => machine := machine.sendData #[Chunk.mk data #[]] |>.userClosedBody
        | .zero => machine := machine.userClosedBody
        | .stream stream =>
          let size ← stream.getKnownSize
          machine := machine.setKnownSize (size.getD .chunked)

          reqStream := some stream

      | none =>
        break

    let (newMachine, step) := machine.step
    machine := newMachine

    if step.output.size > 0 then
      try
        Transport.sendAll socket step.output.data
      catch e =>
        if let some packet := currentRequest then
          packet.onError e

    for event in step.events do
      match event with
      | .needMoreData expect => do
        try
          match ← processNeedMoreData config socket expect requestTimer connectionTimer with
          | .ok (some bs) =>
            machine := machine.feed bs
          | .ok none =>
            machine := machine.noMoreInput
          | .error _ =>
            machine := machine.closeWriter.closeReader.userClosedBody

        catch e =>
          if let some packet := currentRequest then
            packet.onError e

      | .endHeaders head => do
        if let some length := Protocol.H1.Machine.getMessageSize head then
          responseStream.setKnownSize (some length)

        if let some packet := currentRequest then
          let response := { head := machine.reader.messageHead, body := some (.stream responseStream) }
          packet.onResponse response

      | .gotData final data =>
        discard <| responseStream.write data.toByteArray

        if final then
          responseStream.close

      | .chunkExt _ =>
        pure ()

      | .failed e =>
        if let some packet := currentRequest then
          packet.onError (.userError (toString e))

      | .close =>
        pure ()

      | .next =>
        requestTimer := (← Timestamp.now) + config.requestTimeout.val
        responseStream ← Body.ByteStream.emptyWithCapacity
        reqStream := none
        currentRequest := none
        waitingForRequest := true

    if let some stream := reqStream then
      if ¬machine.writer.isClosed then
        if machine.isReaderComplete then
          if let some data ← stream.recv then
            machine := machine.sendData #[data]
          else
            machine := machine.userClosedBody
        else
          if ← stream.isClosed then
            pure ()
          else
            match ← stream.tryRecv with
            | some res => machine := machine.sendData #[res]
            | none => machine := machine.userClosedBody

  responseStream.close
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
let client ← TCP.Socket.Client.mk
client.connect addr

let persistent ← Client.createPersistentConnection client

let res1 ← persistent.send req1
let res2 ← persistent.send req2

persistent.close
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
