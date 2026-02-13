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
public import Std.Internal.Http.Client.Config

public section

namespace Std
namespace Http
namespace Client

open Std Internal IO Async TCP Protocol
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
  machine : H1.Machine .sending

/--
A request packet to be sent through the persistent connection channel.
-/
structure RequestPacket where
  /--
  The request to send.
  -/
  request : Request Body.Stream

  /--
  Promise to resolve with the response.
  -/
  responsePromise : IO.Promise (Except Error (Response Body.Stream))

namespace RequestPacket

/--
Resolve the response promise with an error.
-/
def onError (packet : RequestPacket) (error : Error) : BaseIO Unit :=
  discard <| packet.responsePromise.resolve (.error error)

/--
Resolve the response promise with a successful response.
-/
def onResponse (packet : RequestPacket) (response : Response Body.Stream) : BaseIO Unit :=
  discard <| packet.responsePromise.resolve (.ok response)

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
  requestChannel : Std.CloseableChannel RequestPacket

  /--
  Resolves when the connection task exits.
  -/
  shutdown : IO.Promise Unit

namespace PersistentConnection

/--
Send a request through the persistent connection.
-/
def send [Transport α] (pc : PersistentConnection α) (request : Request Body.Stream) : Async (Response Body.Stream) := do
  let responsePromise ← IO.Promise.new

  let task ← pc.requestChannel.send { request, responsePromise }

  let .ok _ ← await task
    | throw (.userError "connection closed, cannot send more requests")

  match ← await responsePromise.result! with
  | .ok response =>
    pure response
  | .error e =>
    throw e

/--
Wait for the background connection task to terminate.
-/
def waitShutdown (pc : PersistentConnection α) : Async Unit := do
  await pc.shutdown.result!

/--
Close the persistent connection by closing the request channel.
-/
def close (pc : PersistentConnection α) : Async Unit := do
  discard <| EIO.toBaseIO pc.requestChannel.close

end PersistentConnection

namespace Connection

private inductive Recv
  | bytes (x : Option ByteArray)
  | channel (x : Option Chunk)
  | packet (x : Option RequestPacket)
  | timeout
  | shutdown
  | close

private def receiveWithTimeout
    [Transport α]
    (socket : Option α)
    (expect : UInt64)
    (requestStream : Option Body.Stream)
    (requestChannel : Option (Std.CloseableChannel RequestPacket))
    (timeoutMs : Millisecond.Offset)
    (keepAliveTimeoutMs : Option Millisecond.Offset)
    (connectionContext : CancellationContext) : Async Recv := do

  let mut baseSelectables : Array (Selectable Recv) := #[
    .case connectionContext.doneSelector (fun _ => do
      let reason ← connectionContext.getCancellationReason
      match reason with
      | some .deadline => pure .timeout
      | _ => pure .shutdown)
  ]

  if let some socket := socket then
    baseSelectables := baseSelectables.push (.case (Transport.recvSelector socket expect) (Recv.bytes · |> pure))

    -- Timeouts are only applied if we are not waiting on the user.
    if requestStream.isNone ∧ requestChannel.isNone then
      if let some keepAliveTimeout := keepAliveTimeoutMs then
        baseSelectables := baseSelectables.push (.case (← Selector.sleep keepAliveTimeout) (fun _ => pure .timeout))
      else
        baseSelectables := baseSelectables.push (.case (← Selector.sleep timeoutMs) (fun _ => pure .timeout))

  if let some requestStream := requestStream then
    baseSelectables := baseSelectables.push (.case requestStream.recvSelector (Recv.channel · |> pure))

  if let some requestChannel := requestChannel then
    baseSelectables := baseSelectables.push (.case requestChannel.recvSelector (Recv.packet · |> pure))

  Selectable.one baseSelectables

private def processNeedMoreData
    [Transport α]
    (config : Config)
    (socket : Option α)
    (expect : Option Nat)
    (requestChannel : Option (Std.CloseableChannel RequestPacket))
    (requestStream : Option Body.Stream)
    (timeout : Millisecond.Offset)
    (keepAliveTimeout : Option Millisecond.Offset)
    (connectionContext : CancellationContext) : Async Recv := do
  try
    let expectedBytes := expect
      |>.getD config.defaultRequestBufferSize
      |>.min config.maxRecvChunkSize
      |>.toUInt64

    receiveWithTimeout socket expectedBytes requestStream requestChannel timeout keepAliveTimeout connectionContext
  catch _ =>
    pure .close

private def handleError
    (machine : H1.Machine .sending)
    (currentRequest : Option RequestPacket)
    (error : Error) : BaseIO (H1.Machine .sending × Option RequestPacket) := do
  if let some packet := currentRequest then
    packet.onError error

  pure (machine.closeWriter.closeReader.noMoreInput, none)

private def handle
    [Transport α]
    (connection : Connection α)
    (config : Config)
    (connectionContext : CancellationContext)
    (requestChannel : Std.CloseableChannel RequestPacket) : Async Unit := do

  let mut machine := connection.machine
  let socket := connection.socket

  let mut currentTimeout := config.keepAliveTimeout.val
  let mut keepAliveTimeout := some config.keepAliveTimeout.val

  let mut currentRequest : Option RequestPacket := none
  let mut requestStream : Option Body.Stream := none
  let mut responseStream : Option Body.Stream := none

  let mut requiresData := false
  let mut expectData := none
  let mut waitingForRequest := true

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

      | .needBody =>
        pure ()

      | .needAnswer =>
        pure ()

      | .«continue» =>
        pure ()

      | .endHeaders head => do
        currentTimeout := config.readTimeout
        keepAliveTimeout := none

        if let some stream := responseStream then
          if let some length := head.getSize true then
            stream.setKnownSize (some length)

          if let some packet := currentRequest then
            packet.onResponse { head, body := stream }

      | .gotData final ext data =>
        if let some stream := responseStream then
          try
            stream.send { data := data.toByteArray, extensions := ext }

            if final then
              stream.close
          catch _ =>
            pure ()

      | .closeBody =>
        if let some stream := requestStream then
          if ¬(← stream.isClosed) then stream.close

      | .next => do
        if let some stream := requestStream then
          if ¬(← stream.isClosed) then stream.close

        requestStream := none
        responseStream := none
        currentRequest := none

        waitingForRequest := true
        keepAliveTimeout := some config.keepAliveTimeout.val
        currentTimeout := config.keepAliveTimeout.val

      | .failed err =>
        if let some packet := currentRequest then
          packet.onError (.userError (toString err))

      | .close =>
        pure ()

    if requiresData ∨ waitingForRequest ∨ requestStream.isSome then
      let socket := some socket
      let nextRequest := if waitingForRequest then some requestChannel else none

      requiresData := false

      let event ← processNeedMoreData
        config socket expectData nextRequest requestStream currentTimeout keepAliveTimeout connectionContext

      match event with
      | .bytes (some bs) =>
        machine := machine.feed bs

      | .bytes none =>
        machine := machine.noMoreInput

      | .channel (some chunk) =>
        machine := machine.sendData #[chunk]

      | .channel none =>
        machine := machine.userClosedBody

        if let some stream := requestStream then
          if ¬(← stream.isClosed) then stream.close

        requestStream := none

      | .packet (some packet) =>
        currentRequest := some packet
        waitingForRequest := false
        currentTimeout := config.requestTimeout.val
        keepAliveTimeout := none

        machine := machine.send packet.request.head

        let stream := packet.request.body
        if let some size ← stream.getKnownSize then
          machine := machine.setKnownSize size

        requestStream := some stream
        responseStream := some (← Body.Stream.emptyWithCapacity)

      | .packet none =>
        break

      | .close =>
        break

      | .timeout =>
        let (newMachine, newCurrentRequest) ← handleError machine currentRequest (.userError "request timeout")
        machine := newMachine
        currentRequest := newCurrentRequest

      | .shutdown =>
        let (newMachine, newCurrentRequest) ← handleError machine currentRequest (.userError "connection shutdown")
        machine := newMachine
        currentRequest := newCurrentRequest

  if let some packet := currentRequest then
    packet.onError (.userError "connection closed")

  if let some stream := responseStream then
    if ¬(← stream.isClosed) then
      stream.close

  if let some stream := requestStream then
    if ¬(← stream.isClosed) then
      stream.close

  discard <| EIO.toBaseIO requestChannel.close

  let mut keepDraining := true
  while keepDraining do
    match ← requestChannel.tryRecv with
    | some packet =>
      packet.onError (.userError "connection closed")
    | none =>
      keepDraining := false

  Transport.close socket

end Connection

/--
Create a persistent connection that can handle multiple sequential requests.

This is the entry point for creating a client connection. It can be used with a `TCP.Socket` or any
other type that implements `Transport` to create an HTTP client capable of handling multiple
sequential requests on a single connection.
-/
def createPersistentConnection [Transport t] (client : t) (config : Config := {}) : Async (PersistentConnection t) := do
  let requestChannel ← Std.CloseableChannel.new
  let shutdown ← IO.Promise.new
  let connection := Connection.mk client { config := config.toH1Config }

  let ctx ← CancellationContext.new

  background do
    try
      Std.Http.Client.Connection.handle connection config ctx requestChannel
    finally
      discard <| shutdown.resolve ()

  pure { connection, requestChannel, shutdown }

end Std.Http.Client
