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

open Std Internal IO Async TCP
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
  machine : Protocol.H1.Machine .request

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
    [Transport α] (config : Config) (socket : α) (expect : Option Nat) :
    Async (Except Protocol.H1.Machine.Error (Option ByteArray)) := do
  try
    let expect := expect
      |>.getD config.defaultPayloadBytes
      |>.min config.maximumRecvSize

    let data ← receiveWithTimeout socket expect.toUInt64 config.lingeringTimeout

    match data with
    | .bytes (some bytes) => pure (.ok <| some bytes)
    | .bytes none => pure (.ok <| none)
    | .timeout => pure (.error Protocol.H1.Machine.Error.timeout)

  catch _ =>
    pure (.error Protocol.H1.Machine.Error.timeout)

private def handle
    [Transport α]
    (connection : Connection α)
    (config : Config)
    (handler : Request Body → Async (Response Body)) : Async Unit := do

  let mut machine := connection.machine
  let mut running := true
  let socket := connection.socket

  let mut requestStream ← Body.ByteStream.emptyWithCapacity
  let mut requestTimer ← Interval.mk config.requestTimeout.val config.requestTimeout.property
  let mut connectionTimer ← Sleep.mk config.keepAliveTimeout

  let mut response ← IO.Promise.new
  let mut errored ← IO.Promise.new
  let mut respStream := none
  let mut sentResponse := false
  let mut closing := false

  -- Wait for the first tick that is immediate
  requestTimer.tick

  let mut requestTimerTask ← async requestTimer.tick
  let connectionTimerTask ← async connectionTimer.wait

  while running do
    machine := machine.processRead.processWrite

    let (newMachine, events) := machine.takeEvents
    machine := newMachine

    -- Process events like receiving data from the socket.
    for event in events do
      match event with
      | .needMoreData expect => do
        try
          match ← processNeedMoreData config socket expect with
          | .ok (some bs) =>
            machine := machine.feed bs
          | .ok none =>
            machine := machine.forcefullyTerminate
          | .error _ => do
            if let .needStartLine := machine.reader.state then
              continue
            else
              machine := machine.setFailure .timeout
        catch _ =>
          running := false

      | .endHeaders head => do
        if let some (.fixed n) := Protocol.H1.Machine.getMessageSize head then
          requestStream.setKnownSize (some n)

        let newResponse := handler { head, body := (.stream requestStream) }
        let task ← newResponse.asTask

        BaseIO.chainTask task fun
          | .error res => errored.resolve res
          | .ok res => response.resolve res

      | .gotData final data =>
        discard <| requestStream.write data.toByteArray

        if final then
          requestStream.close

      | .chunkExt _ =>
        pure ()

      | .failed _ =>
        pure ()

      | .close =>
        machine := machine.forcefullyTerminate

      | .next =>
        requestTimer.reset
        requestStream ← Body.ByteStream.emptyWithCapacity
        response ← IO.Promise.new
        errored ← IO.Promise.new
        respStream := none
        sentResponse := false

    -- Sends the response head and starts to receive the response body.
    if not sentResponse ∧ (← response.isResolved) then
      sentResponse := true
      let res ← await response.result!

      if machine.isWaitingMessage then
        machine := machine.sendMessage res.head
        match res.body with
        | some (.bytes data) => machine := machine.writeUserData #[Chunk.mk data #[]] |>.closeWriter
        | some ( .zero) | none => machine := machine.closeWriter
        | some (.stream res) => do
          if let some size ← res.getKnownSize then
            machine := machine.setKnownSize size

          respStream := some res

    -- Sends data from the response body.
    if let some stream := respStream then
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
            if let some res ← stream.tryRecv then
              machine := machine.writeUserData res
            else if ← stream.isClosed then
               machine := machine.closeWriter


    -- Checks for things that can close the connection.
    if ¬ closing then
      if (← requestTimerTask.isFinished) ∨ (← connectionTimerTask.isFinished) then
        machine := machine.forcefullyTerminate

        closing := true

      if ← errored.isResolved then
        let _ ← await errored.result!
        machine := machine.setFailure (.other "Internal Error")
        closing := true

    -- Sends the output of the machine to the socket in a vectored write.
    if let some (newMachine, data) := machine.takeOutput then
      machine := newMachine

      if data.size > 0 then
        try
          Transport.sendAll socket data.data
        catch _ =>
          running := false

    running := running && ¬machine.isFullyShutDown

  -- End of the connection
  connectionTimer.stop
  requestTimer.stop

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
def serveConnection [Transport t] (client : t)
    (onRequest : Request Body → Async (Response Body)) (config : Config) : Async Unit := do
  Connection.mk client { config := config.toH1Config }
  |>.handle config onRequest

end Std.Http.Server
