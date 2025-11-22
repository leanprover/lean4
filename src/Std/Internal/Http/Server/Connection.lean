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
public import Std.Internal.Http.Server.Config
public import Std.Internal.Http.Server.ClientConnection

public section

namespace Std
namespace Http
namespace Server

open Std Internal IO Async TCP Protocol
open Time

/-!
# Connection

This module defines a `Server.Connection` that is a structure used to handle a single HTTP connection with
possibly multiple requests.
-/

set_option linter.all true

/--
A single HTTP connection.
-/
public structure Connection (α : Type) where
  /--
  The client connection.
  -/
  socket : α

  /--
  The processing machine for HTTP 1.1
  -/
  machine : H1.Machine .receiving

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
    Async (Except H1.Error (Option ByteArray)) := do
  try
    let expect := expect
      |>.getD config.defaultPayloadBytes
      |>.min config.maximumRecvSize

    let data ← receiveWithTimeout socket expect.toUInt64 config.lingeringTimeout req all

    match data with
    | .bytes (some bytes) => pure (.ok <| some bytes)
    | .bytes none => pure (.ok <| none)
    | .timeout => pure (.error H1.Error.timeout)

  catch _ =>
    pure (.error H1.Error.timeout)

private def handle
    [Transport α]
    (connection : Connection α)
    (config : Config)
    (handler : Request Body → Async (Response Body)) : Async Unit := do

  let mut machine := connection.machine
  let socket := connection.socket

  let mut requestStream ← Body.ByteStream.emptyWithCapacity
  let mut requestTimer := (← Timestamp.now) + config.requestTimeout.val
  let mut connectionTimer := (← Timestamp.now) + config.keepAliveTimeout.val

  let mut response ← IO.Promise.new
  let mut errored ← IO.Promise.new
  let mut respStream := none

  let mut waitingResponse := false

  while ¬machine.halted do
    let (newMachine, step) := machine.step
    machine := newMachine

    if machine.reader.state == .closed ∧ ¬waitingResponse then
      machine := machine.closeWriter

    for event in step.events do
      match event with
      | .needMoreData expect => do
        match ← processNeedMoreData config socket expect requestTimer connectionTimer with
        | .ok (some bs) =>
          machine := machine.feed bs
        | .ok none => do
          machine := machine.noMoreInput
        | .error _ =>
          machine := machine.closeReader

          if machine.isWaitingMessage ∧ waitingResponse then
            waitingResponse := false
            machine := machine.send { status := .requestTimeout }
            machine := machine.userClosedBody
          else
            machine := machine.closeWriter

      | .endHeaders head =>
        waitingResponse := true

        if let some length := Protocol.H1.Machine.getMessageSize head then
          requestStream.setKnownSize (some length)

        let newResponse := handler { head, body := (.stream requestStream) }
        let task ← newResponse.asTask

        BaseIO.chainTask task fun x => do
          match x with
          | .error res => errored.resolve res
          | .ok res => response.resolve res

      | .gotData final data =>
        discard <| requestStream.write data.toByteArray

        if final then
          requestStream.close

      | .next => do
        requestTimer := (← Timestamp.now) + config.requestTimeout.val
        requestStream ← Body.ByteStream.emptyWithCapacity
        response ← IO.Promise.new
        errored ← IO.Promise.new
        respStream := none

      | .failed _ => do pure ()
      | .close => do pure ()
      | .chunkExt _ => do pure ()

    if let some stream := respStream then
      if ¬machine.writer.isClosed then
        if machine.isReaderComplete then
          if let some data ← stream.recv
            then machine := machine.sendData #[data]
            else machine := machine.userClosedBody
        else
          if let some res ← stream.tryRecv then
            machine := machine.sendData #[res]
          else if ← stream.isClosed then
              machine := machine.userClosedBody

    if ¬machine.writer.sentMessage ∧ (← response.isResolved) ∧ machine.isWaitingMessage ∧ waitingResponse then
      let res ← await response.result!

      waitingResponse := false
      machine := machine.send res.head

      match res.body with
      | .bytes data => machine := machine.sendData #[Chunk.mk data #[]] |>.userClosedBody
      |  .zero => machine := machine.userClosedBody
      | .stream stream => do
        let size ← stream.getKnownSize
        machine := machine.setKnownSize (size.getD .chunked)

        respStream := some stream

    if ← errored.isResolved then
      let _ ← await errored.result!

      if machine.isWaitingMessage ∧ waitingResponse then
        waitingResponse := false
        machine := machine.send { status := .internalServerError }
        machine := machine.userClosedBody
        machine := machine.closeReader

    if step.output.size > 0 then
      Transport.sendAll socket step.output.data

  let (_, output) := machine.takeOutput
  if output.size > 0 then
    Transport.sendAll socket output.data

  if let some res := respStream then
    res.close


end Connection

/--
This is the entry point of the library. It is used to receive and send requests using an `Async`
handler for a single connection. It can be used with a `TCP.Socket` or any other type that implements
`Transport` to create a simple HTTP server capable of handling multiple connections concurrently.

# Example

```lean
-- Create a TCP socket server instance
let server ← Socket.Server.mk
server.bind addr
server.listen backlog

-- Enter an infinite loop to handle incoming client connections
while true do
  -- Accept a new client connection.
  let client ← server.accept

  -- Handle the client connection concurrently in the background `serveConnection` will process requests
  -- and handle failures using the provided callbacks and config
  background (serveConnection client onRequest onFailure config)
```
-/
def serveConnection [Transport t] (client : t) (onRequest : Request Body → Async (Response Body)) (config : Config) : Async Unit := do
  Connection.mk client { config := config.toH1Config }
  |>.handle config onRequest

end Std.Http.Server
