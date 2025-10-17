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
  The server connection.
  -/
  socket : α

  /--
  The processing machine for HTTP 1.1
  -/
  machine : Protocol.H1.Machine .response

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

private def handle
    [Transport α]
    (connection : Connection α)
    (config : Client.Config)
    (request : Request Body)
    (responseHandler : Response Body → Async Unit)
    (breakAfterFirst := false) : Async Unit := do

  let mut machine := connection.machine
  let mut running := true
  let socket := connection.socket

  let mut responseStream ← Body.ByteStream.emptyWithCapacity
  let mut requestTimer ← Interval.mk config.requestTimeout.val config.requestTimeout.property
  let mut connectionTimer ← Sleep.mk config.keepAliveTimeout

  let mut receivedResponse := false
  let mut reqStream := none
  let mut sentRequest := false
  let mut closing := false

  -- Wait for the first tick that is immediate
  requestTimer.tick

  let mut requestTimerTask ← async requestTimer.tick
  let connectionTimerTask ← async connectionTimer.wait

  -- Send the request immediately
  machine := machine.sendMessage request.head

  match request.body with
  | .bytes data => machine := machine.writeUserData data |>.closeWriter
  | .zero => machine := machine.closeWriter
  | .stream stream => do
    if let some size ← stream.getKnownSize then
      machine := machine.setKnownSize size
    reqStream := some stream

  while running do

    machine := machine
      |> Protocol.H1.Machine.Client.processRead
      |> Protocol.H1.Machine.Client.processWrite

    let (newMachine, events) := machine.takeEvents
    machine := newMachine

    -- Sends the output of the machine to the socket in a vectored write.
    if let some (newMachine, data) := machine.takeOutput then
      machine := newMachine

      if data.size > 0 then
        try
          Transport.sendAll socket data.data
        catch _ =>
          running := false

    for event in events do
      match event with
      | .needMoreData expect => do
        try
          match ← processNeedMoreData config socket expect with
          | .ok (some bs) =>
            machine := machine.feed bs
          | .ok none =>
            running := false
            break
          | .error _ => do
            if let .needStartLine := machine.reader.state then
              running := false
              break
            else
              machine := machine.setFailure .timeout
        catch _ =>
          running := false

      | .endHeaders head => do
        if let some (.fixed n) := Protocol.H1.Machine.getMessageSize head then
          responseStream.setKnownSize (some n)

        receivedResponse := true

        let response := { head := machine.reader.messageHead, body := some (.stream responseStream) }
        responseHandler response

      | .gotData final data =>
        discard <| responseStream.send data.toByteArray

        if final then
          responseStream.close

      | .chunkExt _ =>
        pure ()

      | .failed =>
        pure ()

      | .close =>
        running := false

      | .next =>
        requestTimer.reset
        responseStream ← Body.ByteStream.emptyWithCapacity
        reqStream := none
        sentRequest := false
        receivedResponse := false

        if breakAfterFirst then
          closing := true
          break

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
    if ¬ closing then
      if (← requestTimerTask.isFinished) ∨ (← connectionTimerTask.isFinished) then
        machine := machine.setFailure .timeout
        closing := true

  -- End of the connection
  connectionTimer.stop
  requestTimer.stop

end Connection

/--
This is the client entry point. It is used to send requests and receive responses using an `Async`
handler for a single connection. It can be used with a `TCP.Socket` or any other type that implements
`Transport` to create a simple HTTP client capable of handling multiple requests concurrently.

# Example

```lean
-- Connect to a server
let socket ← Socket.mk
socket.connect serverAddr

-- Send a request and handle the response
let request : Request Body := {
  head := {
    method := .get,
    target := "/api/data",
    version := .v11,
    headers := Headers.empty.insert "Host" (.new "example.com")
  },
  body := none
}

sendRequest socket request (fun response => do
  -- Process the response
  IO.println s!"Status: {response.head.status}"
  pure ()
) config
```
-/
def sendRequest [Transport t] (client : t)
    (request : Request Body)
    (config : Client.Config := {}) : Async (Response Body) := do

  let result ← IO.Promise.new

  Connection.mk client { config := config.toH1Config }
  |>.handle config request (breakAfterFirst := true) fun r => result.resolve (.ok r)

  Async.ofPromise (pure result)

end Std.Http.Client
