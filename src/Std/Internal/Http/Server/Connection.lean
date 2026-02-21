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
public import Std.Internal.Http.Server.Handler

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
Represents the remote address of a client connection.
-/
public structure RemoteAddr where
  /--
  The socket address of the remote client.
  -/
  addr : Net.SocketAddress
deriving TypeName

instance : ToString RemoteAddr where
  toString addr := toString addr.addr.ipAddr ++ ":" ++ toString addr.addr.port

/--
A single HTTP connection.
-/
public structure Connection (α : Type) where
  /--
  The client connection.
  -/
  socket : α

  /--
  The processing machine for HTTP/1.1.
  -/
  machine : H1.Machine .receiving

  /--
  Extensions to attach to each request (e.g., remote address).
  -/
  extensions : Extensions := .empty

namespace Connection

private inductive Recv (β : Type)
  | bytes (x : Option ByteArray)
  | responseBody (x : Option Chunk)
  | bodyInterest (x : Bool)
  | response (x : (Except Error (Response β)))
  | timeout
  | shutdown
  | close

private def receiveWithTimeout {α : Type} {β : Type}
    [Transport α] [Body.Reader β]
    (socket : Option α)
    (expect : UInt64)
    (responseBody : Option β)
    (requestBody : Option Body.Outgoing)
    (response : Option (Std.Channel (Except Error (Response β))))
    (timeoutMs : Millisecond.Offset)
    (keepAliveTimeoutMs : Option Millisecond.Offset)
    (connectionContext : CancellationContext) : Async (Recv β) := do

  let mut baseSelectables : Array (Selectable (Recv β)) := #[
    .case connectionContext.doneSelector (fun _ => do
      let reason ← connectionContext.getCancellationReason
      match reason with
      | some .deadline => pure .timeout
      | _ => pure .shutdown)
  ]

  if let some socket := socket then
    baseSelectables := baseSelectables.push (.case (Transport.recvSelector socket expect) (Recv.bytes · |> pure))

    -- Always keep a timeout active while waiting on socket progress to avoid
    -- pinning the connection during slow/incomplete transfers.
    if let some keepAliveTimeout := keepAliveTimeoutMs then
      baseSelectables := baseSelectables.push (.case (← Selector.sleep keepAliveTimeout) (fun _ => pure .timeout))
    else
      baseSelectables := baseSelectables.push (.case (← Selector.sleep timeoutMs) (fun _ => pure .timeout))

  if let some responseBody := responseBody then
    baseSelectables := baseSelectables.push (.case (Body.Reader.recvSelector responseBody) (Recv.responseBody · |> pure))

  if let some requestBody := requestBody then
    baseSelectables := baseSelectables.push (.case (Body.Writer.interestSelector requestBody) (Recv.bodyInterest · |> pure))

  if let some response := response then
    baseSelectables := baseSelectables.push (.case response.recvSelector (Recv.response · |> pure))

  Selectable.one baseSelectables

private def processNeedMoreData
    {σ : Type} {β : Type} [Transport α] [Handler σ] [Body.Reader β]
    (config : Config)
    (handler : σ)
    (socket : Option α)
    (expect : Option Nat)
    (response : Option (Std.Channel (Except Error (Response β))))
    (responseBody : Option β)
    (requestBody : Option Body.Outgoing)
    (timeout : Millisecond.Offset)
    (keepAliveTimeout : Option Millisecond.Offset)
    (connectionContext : CancellationContext) : Async (Recv β) := do
  try
    let expectedBytes := expect
      |>.getD config.defaultPayloadBytes
      |>.min config.maximumRecvSize
      |>.toUInt64

    receiveWithTimeout socket expectedBytes responseBody requestBody response timeout keepAliveTimeout connectionContext
  catch e =>
    Handler.onFailure handler e
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
    {σ : Type} [Transport α] [h : Handler σ]
    (connection : Connection α)
    (config : Config)
    (connectionContext : CancellationContext)
    (handler : σ) : Async Unit := do
  let _ : Body.Reader (Handler.ResponseBody σ) := Handler.responseBodyReader
  let _ : Body.Writer (Handler.ResponseBody σ) := Handler.responseBodyWriter

  let mut machine := connection.machine
  let socket := connection.socket

  let (initRequestOut, initRequestIn) ← Body.mkChannel
  let mut requestOutgoing := initRequestOut
  let mut requestIncoming := initRequestIn
  let mut keepAliveTimeout := some config.keepAliveTimeout.val
  let mut currentTimeout := config.keepAliveTimeout.val

  let mut response : Std.Channel (Except Error (Response (Handler.ResponseBody σ))) ← Std.Channel.new
  let mut respStream : Option (Handler.ResponseBody σ) := none
  let mut requiresData := false

  let mut expectData := none
  let mut waitingResponse := false
  let mut pendingHead : Option Request.Head := none

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

      | .needAnswer =>
        pure ()

      | .endHeaders head =>
        currentTimeout := config.lingeringTimeout
        keepAliveTimeout := none

        if let some length := head.getSize true then
          Body.Writer.setKnownSize requestOutgoing (some length)

        pendingHead := some head

      | .«continue» =>
        if let some head := pendingHead then
          let canContinue ← Handler.onContinue handler head
          let status := if canContinue then Status.«continue» else Status.expectationFailed
          machine := machine.canContinue status
          if ¬canContinue then
            pendingHead := none

      | .next => do
        if ¬(← Body.Writer.isClosed requestOutgoing) then
          Body.Writer.close requestOutgoing

        let (newRequestOutgoing, newRequestIncoming) ← Body.mkChannel
        requestOutgoing := newRequestOutgoing
        requestIncoming := newRequestIncoming

        response ← Std.Channel.new

        if let some res := respStream then
          if ¬(← Body.Reader.isClosed res) then Body.Reader.close res

        respStream := none

        keepAliveTimeout := some config.keepAliveTimeout.val
        currentTimeout := config.keepAliveTimeout.val
        waitingResponse := false

      | .failed _ =>
        pendingHead := none
        requiresData := false
        if ¬(← Body.Writer.isClosed requestOutgoing) then
          Body.Writer.close requestOutgoing
        break

      | .closeBody =>
        if ¬(← Body.Writer.isClosed requestOutgoing) then
          Body.Writer.close requestOutgoing

      | .close =>
        pure ()

    if let some head := pendingHead then
      waitingResponse := true
      let newResponse := Handler.onRequest handler { head, body := requestIncoming, extensions := connection.extensions } connectionContext
      let task ← newResponse.asTask
      BaseIO.chainTask task fun x => discard <| response.send x
      pendingHead := none

    if requiresData ∨ waitingResponse ∨ respStream.isSome ∨ machine.canPullBody then
      let socket := some socket
      let answer := if waitingResponse then some response else none

      let requestBody ←
        if machine.canPullBodyNow then
          if ← Body.Writer.isClosed requestOutgoing then
            pure none
          else
            pure (some requestOutgoing)
        else
          pure none

      requiresData := false

      let event ← processNeedMoreData
        config handler socket expectData answer respStream requestBody currentTimeout keepAliveTimeout connectionContext

      match event with
      | .bytes (some bs) =>
        machine := machine.feed bs

      | .bytes none =>
        machine := machine.noMoreInput

      | .responseBody (some chunk) =>
        machine := machine.sendData #[chunk]

      | .responseBody none =>
        machine := machine.userClosedBody

        if let some res := respStream then
          if ¬(← Body.Reader.isClosed res) then Body.Reader.close res

        respStream := none

      | .bodyInterest interested =>
        if interested then
          let (newMachine, pulledChunk) := machine.pullBody
          machine := newMachine

          if let some pulled := pulledChunk then
            try
              Body.Writer.send requestOutgoing pulled.chunk pulled.incomplete
            catch _ =>
              pure ()

            if pulled.final then
              if ¬(← Body.Writer.isClosed requestOutgoing) then
                Body.Writer.close requestOutgoing
        else
          pure ()

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
        Handler.onFailure handler err
        let (newMachine, newWaitingResponse) := handleError machine .internalServerError waitingResponse
        machine := newMachine
        waitingResponse := newWaitingResponse

      | .response (.ok res) =>
        if machine.failed then
          waitingResponse := false
          if ¬(← Body.Reader.isClosed res.body) then
            Body.Reader.close res.body
        else
          let size ← Body.Writer.getKnownSize res.body
          if let some knownSize := size then
            machine := machine.setKnownSize knownSize

          let head ← do
            if config.generateDate ∧ ¬res.head.headers.contains Header.Name.date then
              let now ← Std.Time.DateTime.now (tz := .UTC)
              pure { res.head with headers := res.head.headers.insert Header.Name.date (Header.Value.ofString! now.toRFC822String) }
            else
              pure res.head
          machine := machine.send head
          waitingResponse := false
          if machine.writer.omitBody then
            if ¬(← Body.Reader.isClosed res.body) then
              Body.Reader.close res.body
            respStream := none
          else
            respStream := some res.body

  if ¬(← Body.Writer.isClosed requestOutgoing) then
    Body.Writer.close requestOutgoing

  if let some res := respStream then
    if ¬(← Body.Reader.isClosed res) then
      Body.Reader.close res

  Transport.close socket

end Connection

/--
Handles request/response processing for a single connection using an `Async` handler.
The library-level entry point for running a server is `Server.serve`.
This function can be used with a `TCP.Socket` or any other type that implements
`Transport` to build custom server loops.

# Example

```lean
-- Create a TCP socket server instance
let server ← Socket.Server.mk
server.bind addr
server.listen backlog

-- Enter an infinite loop to handle incoming client connections
while true do
  let client ← server.accept
  background (serveConnection client handler config)
```
-/
def serveConnection
    {σ : Type} [Transport t] [Handler σ]
    (client : t) (handler : σ)
    (config : Config) (extensions : Extensions := .empty) : ContextAsync Unit := do
  (Connection.mk client { config := config.toH1Config } extensions)
  |>.handle config (← ContextAsync.getContext) handler

end Std.Http.Server
