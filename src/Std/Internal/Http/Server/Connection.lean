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

This module defines `Server.Connection`, a structure used to handle a single HTTP connection with
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
  | channel (x : Option Chunk)
  | response (x : (Except Error (Response Body)))
  | timeout

private def receiveWithTimeout
    [Transport α]
    (socket : Option α)
    (expect : UInt64)
    (channel : Option Body.ByteStream)
    (response : Option (Std.Promise (Except Error (Response Body))))
    (timeoutMs : Millisecond.Offset)
    (req : Timestamp)
    (all : Timestamp) : Async Recv := do

  let now ← Timestamp.now
  let timeToRequest := (req - now).toMilliseconds
  let timeToAll := (all - now).toMilliseconds

  let mut baseSelectables := #[
    .case (← Selector.sleep timeoutMs) (fun _ => pure .timeout),
    .case (← Selector.sleep timeToRequest) (fun _ => pure .timeout),
    .case (← Selector.sleep timeToAll) (fun _ => pure .timeout)
  ]

  if let some socket := socket then
    baseSelectables := baseSelectables.push (.case (Transport.recvSelector socket expect) (Recv.bytes · |> pure))

  if let some channel := channel then
    baseSelectables := baseSelectables.push (.case channel.recvSelector (Recv.channel · |> pure))

  if let some response := response then
    baseSelectables := baseSelectables.push (.case response.selector (Recv.response · |> pure))

  Selectable.one baseSelectables

private def processNeedMoreData
    [Transport α]
    (config : Config)
    (socket : Option α)
    (expect : Option Nat)
    (response : Option (Std.Promise (Except Error (Response Body))))
    (channel : Option Body.ByteStream)
    (req : Timestamp)
    (all : Timestamp) : Async Recv := do
  try
    let expectedBytes := expect
      |>.getD config.defaultPayloadBytes
      |>.min config.maximumRecvSize
      |>.toUInt64

    receiveWithTimeout socket expectedBytes channel response config.lingeringTimeout req all
  catch _ =>
    pure .timeout

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

  let mut response ← Std.Promise.new
  let mut respStream := none
  let mut requiresData := false
  let mut needAnswer := false
  let mut needBody := false

  let mut expectData := none
  let mut waitingResponse := false

  while ¬machine.halted do
    let (newMachine, step) := machine.step
    machine := newMachine

    if step.output.size > 0 then
      Transport.sendAll socket step.output.data

    if machine.reader.state == .closed ∧ ¬waitingResponse then
      machine := machine.closeWriter

    for event in step.events do
      match event with
      | .needMoreData expect => do
        requiresData := true
        expectData := expect

      | .needBody => do
        needBody := true

      | .needAnswer =>
        needAnswer := true

      | .endHeaders head =>
        waitingResponse := true

        if let some length := Protocol.H1.Machine.getMessageSize head then
          requestStream.setKnownSize (some length)

        let newResponse := handler { head, body := (.stream requestStream) }
        let task ← newResponse.asTask

        BaseIO.chainTask task fun x => discard <| response.resolve x

      | .gotData final data =>
        discard <| requestStream.write data.toByteArray

        if final then
          requestStream.close

      | .next => do
        requestTimer := (← Timestamp.now) + config.requestTimeout.val
        requestStream ← Body.ByteStream.emptyWithCapacity
        response ← Std.Promise.new
        respStream := none

      | .failed _ =>
        do pure ()

      | .close =>
        do pure ()

      | .chunkExt _=>
        do pure ()

    if requiresData ∨ needAnswer ∨ respStream.isSome then
      let socket := if requiresData then some socket else none
      let answer := if needAnswer then some response else none

      requiresData := false
      needAnswer := false
      needBody := false

      match ← processNeedMoreData config socket expectData answer respStream requestTimer connectionTimer with
      | .bytes (some bs) =>
        machine := machine.feed bs

      | .bytes none =>
        machine := machine.noMoreInput

      | .channel (some chunk) =>
        machine := machine.sendData #[chunk]

      | .channel none =>
        machine := machine.userClosedBody
        respStream := none

      | .timeout =>
        machine := machine.closeReader
        if machine.isWaitingMessage ∧ waitingResponse then
          waitingResponse := false
          machine := machine.send { status := .requestTimeout }
          machine := machine.userClosedBody
          respStream := none
        else
          machine := machine.closeWriter

      | .response (.error _) =>
        if machine.isWaitingMessage ∧ waitingResponse then
          waitingResponse := false
          machine := machine.send { status := .internalServerError }
          machine := machine.userClosedBody
          machine := machine.closeReader

      | .response (.ok res) =>
        machine := machine.send res.head
        match res.body with
        | .bytes data => machine := machine.sendData #[Chunk.mk data #[]] |>.userClosedBody
        | .zero => machine := machine.userClosedBody
        | .stream stream => do
          let size ← stream.getKnownSize
          machine := machine.setKnownSize (size.getD .chunked)
          respStream := some stream

  let (_, output) := machine.takeOutput

  if output.size > 0 then
    Transport.sendAll socket output.data

  if let some res := respStream then
    if ¬ (← res.isClosed) then
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
