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


instance : Repr (Response t) where
  reprPrec t := reprPrec t.head

deriving instance Repr for Error
deriving instance Repr for ByteArray
deriving instance Repr for Chunk

private inductive Recv (t : Type)
  | bytes (x : Option ByteArray)
  | channel (x : Option Chunk)
  | response (x : (Except Error (Response t)))
  | timeout
  | shutdown
  | close

private instance : Repr (Recv t) where
  reprPrec
    | .bytes b  => reprPrec ("bytes", b)
    | .channel b => reprPrec ("channel", b)
    | .response b => reprPrec ("response", b)
    | .timeout => reprPrec "timeout"
    | .shutdown => reprPrec "shutdown"
    | .close => reprPrec "close"

private def receiveWithTimeout {α t}
    [Transport α]
    [Body t Chunk]
    (socket : Option α)
    (expect : UInt64)
    (ch : Option t)
    (response : Option (Std.Channel (Except Error (Response t))))
    (timeoutMs : Millisecond.Offset)
    (keepAliveTimeoutMs : Option Millisecond.Offset)
    (connectionContext : CancellationContext) : Async (Recv t) := do

  let mut baseSelectables : Array (Selectable (Recv t)) := #[
    .case connectionContext.doneSelector (fun _ => do
      let reason ← connectionContext.getCancellationReason
      match reason with
      | some .deadline => pure .timeout
      | _ => pure .shutdown)
  ]

  if let some socket := socket then
    baseSelectables := baseSelectables.push (.case (Transport.recvSelector socket expect) (Recv.bytes · |> pure))

    -- Timeouts are only applied if we are not expecting data from the user.
    if ch.isNone ∧ response.isNone then
      if let some keepAliveTimeout := keepAliveTimeoutMs then
        baseSelectables := baseSelectables.push (.case (← Selector.sleep keepAliveTimeout) (fun _ => pure .timeout))
      else
        baseSelectables := baseSelectables.push (.case (← Selector.sleep timeoutMs) (fun _ => pure .timeout))

  if let some ch := ch then
    baseSelectables := baseSelectables.push (.case (Body.recvSelector ch) (Recv.channel · |> pure))

  if let some response := response then
    baseSelectables := baseSelectables.push (.case response.recvSelector (Recv.response · |> pure))

  Selectable.one baseSelectables

private def processNeedMoreData
    [Transport α]
    [Body t Chunk]
    (config : Config)
    (socket : Option α)
    (expect : Option Nat)
    (response : Option (Std.Channel (Except Error (Response t))))
    (channel : Option t)
    (timeout : Millisecond.Offset)
    (keepAliveTimeout : Option Millisecond.Offset)
    (connectionContext : CancellationContext) : Async (Recv t) := do
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
    let machine := machine.send { status, headers := .empty |>.insert .connection .close }
      |>.userClosedBody
      |>.closeReader
      |>.noMoreInput
    (machine, false)
  else
    (machine.closeWriter.noMoreInput, waitingResponse)

private def handle
    [Transport α]
    [Body t Chunk]
    (connection : Connection α)
    (config : Config)
    (connectionContext : CancellationContext)
    (onError : Error → Async Unit)
    (handler : Request Body.ChunkStream → ContextAsync (Response t)) : Async Unit := do

  let mut machine := connection.machine
  let socket := connection.socket

  let mut requestStream ← Body.ChunkStream.emptyWithCapacity
  let mut keepAliveTimeout := some config.keepAliveTimeout.val
  let mut currentTimeout := config.keepAliveTimeout.val

  let mut response ← Std.Channel.new
  let mut respStream : Option t := none
  let mut requiresData := false
  let mut needBody := false

  let mut expectData := none
  let mut waitingResponse := false

  while ¬machine.halted do
    let (newMachine, step) := machine.step

    machine := newMachine

    if step.output.size > 0 then
      try Transport.sendAll socket #[step.output.toByteArray] catch _ => break

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

        if let some length := head.getSize true then
          requestStream.setKnownSize (some length)

        let newResponse := handler { head, body := requestStream } connectionContext
        let task ← newResponse.asTask

        BaseIO.chainTask task fun x => discard <| response.send x

      | .gotData final ext data =>
        try
          Body.send requestStream { data := data.toByteArray, extensions := ext }

          if final then
            requestStream.close

        catch _ =>
          pure ()

      | .next => do
        requestStream ← Body.ChunkStream.emptyWithCapacity
        response ← Std.Channel.new

        if let some res := respStream then
          if ¬ (← Body.isClosed res) then Body.close res

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
          if ¬(←  Body.isClosed res) then Body.close res

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

      | .response (.error err) =>
        onError err
        let (newMachine, newWaitingResponse) := handleError machine .internalServerError waitingResponse
        machine := newMachine
        waitingResponse := newWaitingResponse

      | .response (.ok res) =>
        machine := machine.send res.head
        waitingResponse := false

        let size ← Body.size? res.body
        machine := machine.setKnownSize (size.getD .chunked)
        respStream := some res.body

  if ¬ (← requestStream.isClosed) then
    requestStream.close

  if let some res := respStream then
    if ¬(← Body.isClosed res) then
      Body.close res

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
  let client ← server.accept
  background (serveConnection client onRequest onError config)
```
-/
def serveConnection
    [Transport t] (client : t) [Body u Chunk] (onRequest : Request Body.ChunkStream → ContextAsync (Response u))
    (onError : Error → Async Unit) (config : Config) : ContextAsync Unit := do
  Connection.mk client { config := config.toH1Config }
  |>.handle config (← ContextAsync.getContext) onError onRequest

end Std.Http.Server
