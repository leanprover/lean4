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

deriving instance Repr for ByteArray
deriving instance Repr for Chunk
deriving instance Repr for Response
deriving instance Repr for Error

instance : Repr Body where
  reprPrec _ n := reprPrec () n

private inductive Recv
  | bytes (x : Option ByteArray)
  | channel (x : Option Chunk)
  | response (x : (Except Error (Response Body)))
  | timeout
  | shutdown
  | close
deriving Repr

private def receiveWithTimeout
    [Transport α]
    (socket : Option α)
    (expect : UInt64)
    (channel : Option Body.ByteStream)
    (response : Option (Std.Future (Except Error (Response Body))))
    (timeoutMs : Millisecond.Offset)
    (keepAliveTimeoutMs : Option Millisecond.Offset)
    (connectionContext : CancellationContext) : Async Recv := do

  let mut baseSelectables := #[
    .case connectionContext.doneSelector (fun _ => do
      let reason ← connectionContext.getCancellationReason
      match reason with
      | some .deadline => pure .timeout
      | _ => pure .shutdown)
  ]

  if let some socket := socket then
    baseSelectables := baseSelectables.push (.case (Transport.recvSelector socket expect) (Recv.bytes · |> pure))

    -- Timeouts are only applied if we are not expecting data from the user.
    if channel.isNone ∧ response.isNone then
      if let some keepAliveTimeout := keepAliveTimeoutMs then
        baseSelectables := baseSelectables.push (.case (← Selector.sleep keepAliveTimeout) (fun _ => pure .timeout))

      baseSelectables := baseSelectables.push (.case (← Selector.sleep timeoutMs) (fun _ => pure .timeout))

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
    (response : Option (Std.Future (Except Error (Response Body))))
    (channel : Option Body.ByteStream)
    (timeout : Millisecond.Offset)
    (keepAliveTimeout : Option Millisecond.Offset)
    (connectionContext : CancellationContext) : Async Recv := do
  try
    let expectedBytes := expect
      |>.getD config.defaultPayloadBytes
      |>.min config.maximumRecvSize
      |>.toUInt64

    receiveWithTimeout socket expectedBytes channel response timeout keepAliveTimeout connectionContext
  catch _ =>
    pure .close

private def handleError (machine : H1.Machine .receiving) (status : Status) (waitingResponse : Bool) : H1.Machine .receiving × Bool :=
  if machine.isWaitingMessage ∧ waitingResponse then
    let machine := machine.send { status, headers := .empty |>.insert (.new "connection") (.new "close") }
      |>.userClosedBody
      |>.closeReader
      |>.noMoreInput
    (machine, false)
  else
    (machine.closeWriter.noMoreInput, waitingResponse)

private def handle
    [Transport α]
    (connection : Connection α)
    (config : Config)
    (connectionContext : CancellationContext)
    (handler : Request Body → ContextAsync (Response Body)) : Async Unit := do

  let mut machine := connection.machine
  let socket := connection.socket

  let mut requestStream ← Body.ByteStream.emptyWithCapacity
  let mut keepAliveTimeout := some config.keepAliveTimeout.val
  let mut currentTimeout := config.keepAliveTimeout.val

  let mut response ← Std.Future.new
  let mut respStream := none
  let mut requiresData := false
  let mut needBody := false

  let mut expectData := none
  let mut waitingResponse := false

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
        needBody := true

      | .needAnswer =>
        pure ()

      | .endHeaders head =>
        waitingResponse := true
        currentTimeout := config.lingeringTimeout
        keepAliveTimeout := none

        if let some length := Protocol.H1.Machine.getMessageSize head then
          requestStream.setKnownSize (some length)

        let newResponse := handler { head, body := (.stream requestStream) } connectionContext
        let task ← newResponse.asTask

        BaseIO.chainTask task fun x => discard <| response.resolve x

      | .gotData final ext data =>
        try
          requestStream.writeChunk { data := data.toByteArray, extensions := ext }

          if final then
            requestStream.close

        catch _ =>
          pure ()

      | .next => do
        requestStream ← Body.ByteStream.emptyWithCapacity
        response ← Std.Future.new

        if let some res := respStream then
          if ¬ (← res.isClosed) then res.close

        respStream := none

        keepAliveTimeout := some config.keepAliveTimeout.val
        currentTimeout := config.keepAliveTimeout.val
        waitingResponse := false

      | .failed _ =>
        pure ()

      | .close =>
        pure ()

    if requiresData ∨ waitingResponse ∨ respStream.isSome then
      let socket := some socket
      let answer := if waitingResponse then some response else none

      requiresData := false
      needBody := false

      let event ← processNeedMoreData config socket expectData answer respStream currentTimeout keepAliveTimeout connectionContext

      match event with
      | .bytes (some bs) =>
        machine := machine.feed bs

      | .bytes none =>
        machine := machine.noMoreInput

      | .channel (some chunk) =>
        machine := machine.sendData #[chunk]

      | .channel none =>
        machine := machine.userClosedBody

        if let some res := respStream then
          if ¬(← res.isClosed) then res.close

        respStream := none

      | .close =>
        break

      | .timeout =>
        machine := machine.closeReader
        let (newMachine, newWaitingResponse) := handleError machine .requestTimeout waitingResponse
        machine := newMachine
        waitingResponse := newWaitingResponse

      | .shutdown =>
        let (newMachine, newWaitingResponse) := handleError machine .serviceUnavailable waitingResponse
        machine := newMachine
        waitingResponse := newWaitingResponse

      | .response (.error _) =>
        let (newMachine, newWaitingResponse) := handleError machine .internalServerError waitingResponse
        machine := newMachine
        waitingResponse := newWaitingResponse

      | .response (.ok res) =>
        machine := machine.send res.head
        waitingResponse := false

        match res.body with
        | .bytes data => machine := machine.sendData #[Chunk.mk data #[]] |>.userClosedBody
        | .zero => machine := machine.userClosedBody
        | .stream stream => do
          let size ← stream.getKnownSize
          machine := machine.setKnownSize (size.getD .chunked)
          respStream := some stream

  if ¬ (← requestStream.isClosed) then
    requestStream.close

  if let some res := respStream then
    if ¬(← res.isClosed) then
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
def serveConnection [Transport t] (client : t) (onRequest : Request Body → ContextAsync (Response Body)) (config : Config) : ContextAsync Unit := do
  Connection.mk client { config := config.toH1Config }
  |>.handle config (← ContextAsync.getContext) onRequest

end Std.Http.Server
