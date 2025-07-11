/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Init
import Std.Internal.Async.Select
import Std.Internal.Async.TCP
import Std.Internal.Http.V11.Machine
import Std.Internal.Http.Data.Body
import Std.Internal.Http.Data.Request
import Std.Internal.Http.Data.Response

open Std Internal IO Async TCP
open Std Http V11
open Std Http Data

namespace Std
namespace Http

set_option linter.all true

/--
The connection object that carries a socket and the machine
-/
structure Connection where
  /--
  The client socket
  -/
  socket : Socket.Client

  /--
  The state machine
  -/
  machine : Machine .request

namespace Connection

-- TODO : Guard type for IO.Promise
-- TODO : Convert all the types of the Async itnerfaces to Async
-- TODO : Easync.ofTask type is wrong.
-- TODO : exception on while probasbly creates a promise not resolved error?

-- Event Handlers
private def handleEndHeaders (connection : Connection) (fn : Request Body → Async (Response Body))
    (stream : ByteStream) : Async (Response Body) := do
  if let some (method, uri, version) := connection.machine.inputStatusLine then
    fn (Request.mk method version uri connection.machine.inputHeaders (.stream stream))
  else
    panic! "Invalid State"

private def handleGotData (stream : ByteStream) (final : Bool) (data : ByteArray) : Async Unit := do
  await (← stream.data.send data)
  if final then
    await (← stream.data.send none)

private def handleNeedMoreData (connection : Connection) : Async (Connection × Bool) := do
  let data ← do
    try
      let data := await (← Selectable.one #[
        .case (← Selector.sleep 1500) fun _ => return AsyncTask.pure none,
        .case (← connection.socket.recvSelector 4096) fun data => return AsyncTask.pure data,
      ]) | pure (.empty, true)

      pure (data, false)
    catch err =>
      IO.println s!"err: {err}"
      pure (.empty, true)

  if .empty == data.1 then
    pure (connection, true)
  else
    pure ({ connection with machine := connection.machine.incomeFeed data.1 }, false)

private def handleAwaitingAnswer (connection : Connection) (response : Response Body) : Async (Connection × Bool) := do
  match response.body with
  | .zero =>
    pure ({ connection with machine := connection.machine.close }, true)
  | .bytes bytes =>
    pure ({ connection with machine := connection.machine.writeData bytes |>.close }, true)
  | .stream st =>
    match ← await (← st.data.recv) with
    | some data =>
      pure ({ connection with machine := connection.machine.writeData data }, false)
    | none =>
      pure ({ connection with machine := connection.machine.close }, true)

private def handleReadyToRespond (connection : Connection) (response : Response Body) : Connection :=
  { connection with machine := connection.machine.answer response }

private def handleClose (stream : ByteStream) : Async Unit := do
  await (← stream.data.send none)

private def handleNext (stream : ByteStream) : Async Unit := do
  await (← stream.data.send none)

private def handleFailed (stream : ByteStream) (connection : Connection) : Async Connection := do
  await (← stream.data.send none)
  pure { connection with machine := connection.machine.advance }

private def processEvent (connection : Connection) (stream : ByteStream) (response : Response Body)
    (fn : Request Body → Async (Response Body)) : Async (Connection × ByteStream × Response Body × Bool) := do
  match connection.machine.event with
  | some event =>
    match event with
    | .chunkExt _ =>
      pure (connection, stream, response, false)
    | .endHeaders _ =>
      let newStream := { data := (← Channel.new) }
      let newResponse ← handleEndHeaders connection fn newStream
      pure (connection, newStream, newResponse, false)
    | .gotData final data =>
      handleGotData stream final data
      pure (connection, stream, response, false)
    | .needMoreData =>
      let (newConnection, shouldBreak) ← handleNeedMoreData connection
      pure (newConnection, stream, response, shouldBreak)
    | .awaitingAnswer =>
      let (newConnection, shouldBreak) ← handleAwaitingAnswer connection response
      pure (newConnection, stream, response, shouldBreak)
    | .readyToRespond =>
      let newConnection := handleReadyToRespond connection response
      pure (newConnection, stream, response, false)
    | .close =>
      handleClose stream
      pure (connection, stream, response, true)
    | .next =>
      handleNext stream
      pure (connection, stream, response, false)
    | .failed _ =>
      let newConnection ← handleFailed stream connection
      pure (newConnection, stream, response, true)
  | none =>
    pure (connection, stream, response, false)

private def flushConnection (connection : Connection) : Async Connection := do
  if connection.machine.needsFlush then
    let (machine, ba) := connection.machine.flush
    await (← connection.socket.send ba)
    pure { connection with machine }
  else
    pure connection

private def finalFlush (connection : Connection) : Async Unit := do
  let (_, ba) := connection.machine.flush
  if ba.size > 0 then
    await (← connection.socket.send ba)
  IO.println "end"

private partial def start (connection : Connection) (fn : Request Body → Async (Response Body)) : Async Unit := do
  let mut connection := connection
  let mut stream : ByteStream := { data := (← Channel.new) }
  let mut response : Response Body := Inhabited.default

  while true do
    let (newConnection, newStream, newResponse, shouldBreak) ←
      processEvent connection stream response fn

    connection := newConnection
    stream := newStream
    response := newResponse

    if shouldBreak then break

    connection := { connection with machine := connection.machine.resetEvent.advance }
    connection ← flushConnection connection

  finalFlush connection

/--

-/
def serve (addr : Net.SocketAddress) (fn : Request Body → Async (Response Body)) : Async Unit := do
  let socket ← Socket.Server.mk
  socket.bind addr
  socket.listen 12

  while true do
    let clientTask ← socket.accept
    let client ← await clientTask
    let conn := Connection.mk client {}
    background .default (start conn fn)

end Connection
