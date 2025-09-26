/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Internal.Async.TCP
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
  machine : Protocol.H1.Machine

namespace Connection

private inductive Recv
  | bytes (x : Option ByteArray)
  | timeout

private def receiveWithTimeout
  [ClientConnection α] (socket : α) (expect : UInt64)
  (timeoutMs : Millisecond.Offset) :
  Async Recv := do
    Selectable.one #[
      .case (← ClientConnection.recvSelector socket expect) (fun x => pure <| .bytes x),
      .case (← Selector.sleep timeoutMs) (fun _ => pure <| .timeout)]

private def processNeedMoreData
  [ClientConnection α] (machine : Protocol.H1.Machine) (socket : α) (expect : Option Nat) :
  Async (Except Protocol.H1.Machine.Error (Option ByteArray)) := do
    try
      let expect := expect.getD machine.config.defaultPayloadBytes
      let data ← receiveWithTimeout socket expect.toUInt64 machine.config.timeoutMilliseconds

      match data with
      | .bytes (some bytes) => pure (.ok <| some bytes)
      | .bytes none => pure (.ok <| none)
      | .timeout => pure (.error Protocol.H1.Machine.Error.timeout)

    catch _ =>
      pure (.error Protocol.H1.Machine.Error.timeout)

private def handle
  [ClientConnection α]
  (connection : Connection α)
  (handler : Request Body → Async (Response Body))
  (onFailure : Error → Async Unit)
  : Async Unit := do
    let mut machine := connection.machine
    let mut running := true
    let socket := connection.socket

    let mut requestStream ← Body.ByteStream.emptyWithCapacity

    let mut response ← IO.Promise.new
    let mut errored ← IO.Promise.new
    let mut respStream := none
    let mut sentResponse := false

    try
      while running do
        machine := machine.processRead
        machine := machine.processWrite

        let (newMachine, events) := machine.takeEvents
        machine := newMachine

        for event in events do
          match event with
          | .needMoreData expect => do
            match ← processNeedMoreData machine socket expect with
            | .ok (some bs) =>
              machine := machine.feed bs
            | .ok none =>
              running := false;
              break
            | .error _ => do
              if let .needStartLine := machine.reader.state then
                running := false; break
              else
                machine := machine.setFailure .timeout .requestTimeout

          | .endHeaders head => do
            if let some (.fixed n) := Protocol.H1.Machine.getRequestSize head then
              requestStream.setKnownSize (some n)

            let newResponse := handler { head, body := (.stream requestStream) }
            let task ← newResponse.asTask

            BaseIO.chainTask task fun
              | .error res => errored.resolve res
              | .ok res => response.resolve res

          | .gotData final data =>
            discard <| requestStream.send data.toByteArray

            if final then
              requestStream.close

          | .chunkExt _ =>
            pure ()

          | .failed =>
            pure ()

          | .close =>
            running := false

          | .next =>
            requestStream ← Body.ByteStream.emptyWithCapacity
            response ← IO.Promise.new
            errored ← IO.Promise.new
            respStream := none
            sentResponse := false

        if not sentResponse ∧ (← response.isResolved) then
          sentResponse := true
          let res ← await response.result!

          if machine.isWaitingResponse then
            machine := machine.sendResponse res.head
            match res.body with
            | some (.bytes data) => machine := machine.writeUserData data |>.closeWriter
            | some ( .zero) | none => machine := machine.closeWriter
            | some (.stream res) => do
              if let some size ← res.getKnownSize then
                machine := machine.setKnownSize size

              respStream := some res

        if let some stream := respStream then
          if machine.isWriterOpened then
            if machine.isReaderComplete ∧ events.isEmpty then
              if let some data ← stream.recv then
                machine := machine.writeUserData data
              else
                machine := machine.closeWriter
            else
              if (← stream.isClosed) ∧ (← stream.isClosed) then
                pure ()
              else
                match ← stream.tryRecv with
                | some res => machine := machine.writeUserData res
                | none => machine := machine.closeWriter

        if ← errored.isResolved then
          let _ ← await errored.result!
          machine := machine.setFailure (.other "Internal Error") .internalServerError

        if let some (newMachine, data) := machine.takeOutput then
          machine := newMachine

          if data.size > 0 then
            ClientConnection.sendAll socket data.data

    catch err =>
      onFailure err
end Connection

/--
This is the entry point of the library. It is used to receive and send requests using an `Async`
handler for a single connection. It can be used with a `TCP.Socket` or any other type that implements
`ClientConnection` to create a simple HTTP server capable of handling multiple connections concurrently.

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
def serveConnection
  [ClientConnection t]
  (client : t)
  (onRequest : Request Body → Async (Response Body))
  (onFailure : Error → Async Unit := fun _ => pure ())
  (config : Config := {}) : Async Unit := do
    Connection.mk client { config := config.toH1Config }
    |>.handle onRequest onFailure
