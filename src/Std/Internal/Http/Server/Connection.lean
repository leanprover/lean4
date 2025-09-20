/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Init
public import Std.Internal.Async.TCP
public import Std.Internal.Http.Protocol.H1
public import Std.Internal.Http.Server.Config

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
public structure Connection where
  /--
  The client connection.
  -/
  socket : Socket.Client

  /--
  The processing machine for HTTP 1.1
  -/
  machine : Protocol.H1.Machine

namespace Connection

private inductive Recv
  | bytes (x : Option ByteArray)
  | timeout

private def receiveWithTimeout
  (socket : Socket.Client) (expect : UInt64) (timeoutMs : Millisecond.Offset := 5000)
  :
  Async Recv := do
    Selectable.one #[
      .case (← socket.recvSelector expect) (fun x => pure <| .bytes x),
      .case (← (← Sleep.mk timeoutMs).selector) (fun _ => pure <| .timeout)]

private def processNeedMoreData
  (machine : Protocol.H1.Machine) (socket : Socket.Client) (expect : Option Nat) :
  Async (Except Protocol.H1.Machine.Error (Option ByteArray)) := do
    try
      let expect := expect.getD machine.config.defaultPayloadBytes
      let data ← receiveWithTimeout socket expect.toUInt64

      match data with
      | .bytes (some bytes) => pure (.ok <| some bytes)
      | .bytes none => pure (.ok <| none)
      | .timeout => pure (.error Protocol.H1.Machine.Error.timeout)

    catch _ =>
      pure (.error Protocol.H1.Machine.Error.timeout)

private def handle
  (connection : Connection)
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

        if let some (newMachine, data) := machine.takeOutput then
          machine := newMachine

          if data.size > 0 then
            socket.sendAll data.data

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
              match ← stream.tryRecv with
              | some (some res) => machine := machine.writeUserData res
              | some none => pure ()
              | none => machine := machine.closeWriter

        if ← errored.isResolved then
          let _ ← await errored.result!
          machine := machine.setFailure (.other "Internal Error") .internalServerError

        for event in events do
          match event with
          | .needMoreData expect => do
            match ← processNeedMoreData machine socket expect with
            | .ok (some bs) => machine := machine.feed bs
            | .ok none =>
              running := false
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
            running := false

          | .close =>
            running := false

          | .next =>
            requestStream ← Body.ByteStream.emptyWithCapacity
            response ← IO.Promise.new
            errored ← IO.Promise.new
            respStream := none
            sentResponse := false

    catch err =>
      onFailure err
end Connection

/--
Serve conection
-/
def serve
  (addr : Net.SocketAddress)
  (onRequest : Request Body  → Async (Response Body))
  (onReady : Async Unit := pure ())
  (onFailure : Error → Async Unit := fun _ => pure ())
  (config : Config := {})
  (backlog : UInt32 := 128) : Async Unit := do
    let server ← Socket.Server.mk
    server.bind addr
    server.listen backlog

    onReady

    while true do
      let client ← server.accept
      background (prio := .max) <|
        Connection.mk client { config := config.toH1Config }
        |>.handle onRequest onFailure
