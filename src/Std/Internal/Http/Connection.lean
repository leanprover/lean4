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
-- TODO : cancelrecv must be fixed

-- Event Handlers
private def handleEndHeaders
  (connection : Connection)
  (fn : Request Body → Async (Response Body))
  (promise : IO.Ref (ETask IO.Error (Response Body)))
  (stream : ByteStream)
  : Async Unit := do
    if let some (method, uri, version) := connection.machine.inputStatusLine then
      let res := fn (Request.mk method version uri connection.machine.inputHeaders (.stream stream))
      promise.set (← res.asTask)
    else
      panic! "Invalid State"

private def handleGotData (stream : ByteStream) (final : Bool) (data : ByteSlice) : Async Unit := do
  await (← stream.data.send data)
  if final then
    await (← stream.data.send none)

private def timeoutRecv (socket : Socket.Client) : Async (Option ByteArray) := do
  let result := Selectable.one #[
    .case (← Selector.sleep 5000) fun _ => return AsyncTask.pure none,
    .case (← socket.recvSelector 4096) fun data => return AsyncTask.pure data,
  ]
  let result ← result
  await result

private def handleNeedMoreData (connection : Connection) : Async (Connection × Bool) := do
  let data ← do
    try
      let size := connection.machine.size.getD 4096
      let some data ← await (← connection.socket.recv? size)
        | return ({connection with machine := connection.machine.setError .timeout |>.advance}, true)
      pure (data, false)
    catch _ =>
      pure (.empty, true)

  if .empty == data.1 then
    pure (connection, true)
  else
    pure ({ connection with machine := connection.machine.feed data.1 }, false)

private def handleAwaitingAnswer (connection : Connection) (response : Response Body) : Async (Connection × Bool) := do
  match response.body with
  | .zero =>
    pure ({ connection with machine := connection.machine.close }, false)
  | .bytes bytes =>
    pure ({ connection with machine := connection.machine.writeData bytes.toByteArray |>.close }, false)
  | .stream st =>
    let ba ← await (← st.data.recv)
    let connection := { connection with machine := { connection.machine with chunkedAnswer := true } }
    match ba with
    | some data =>
      pure ({ connection with machine := connection.machine.writeData data.toByteArray }, false)
    | none =>
      pure ({ connection with machine := connection.machine.close }, false)

private def handleReadyToRespond (connection : Connection) (response : Response Body) : Connection :=
  { connection with machine := connection.machine.answer response }

private def handleClose (stream : ByteStream) : Async Unit := do
  await (← stream.data.send none)

private def handleNext (stream : ByteStream) : Async Unit := do
  await (← stream.data.send none)

private def handleFailed (stream : ByteStream) (connection : Connection) : Async Connection := do
  await (← stream.data.send none)
  pure { connection with machine := connection.machine.advance }

private def processEvent (connection : Connection)
  (stream : ByteStream)
  (fn : Request Body → Async (Response Body))
  (promise : IO.Ref (ETask IO.Error (Response Body)))
  : Async (Connection × ByteStream × Bool) := do
  match connection.machine.event with
  | some event =>
    match event with
    | .chunkExt _ =>
      pure (connection, stream, false)
    | .endHeaders _ =>
      let newStream := { data := (← Channel.new) }
      handleEndHeaders connection fn promise newStream
      pure (connection, newStream, false)
    | .gotData final data =>
      handleGotData stream final data
      pure (connection, stream, false)
    | .needMoreData =>
      let (newConnection, shouldBreak) ← handleNeedMoreData connection
      pure (newConnection, stream, shouldBreak)
    | .awaitingAnswer =>
      let response ← EAsync.ofETask (← promise.get)
      let (newConnection, shouldBreak) ← handleAwaitingAnswer connection response
      pure (newConnection, stream, shouldBreak)
    | .readyToRespond =>
      let response ← EAsync.ofETask (← promise.get)
      let newConnection := handleReadyToRespond connection response
      pure (newConnection, stream, false)
    | .next =>
      handleNext stream
      pure (connection, stream, false)
    | .close =>
      handleClose stream
      pure (connection, stream, true)
    | .failed _ =>
      let newConnection ← handleFailed stream connection
      pure (newConnection, stream, true)
  | none =>
    pure (connection, stream, false)

private def flushConnection (connection : Connection) (force : Bool) : Async Connection := do
  if connection.machine.needsFlush || force then
    let machine := connection.machine
    let (machine, ba) := machine.flush force
    await (← connection.socket.send ba)
    pure { connection with machine }
  else
    pure connection

private def finalFlush (connection : Connection) : Async Unit := do
  let machine := connection.machine
  let (_, ba) := machine.flush true
  if ba.size > 0 then
    await (← connection.socket.send ba)

private partial def start (connection : Connection) (fn : Request Body → Async (Response Body)) : Async Unit := do
  try
    let mut connection := connection
    let mut stream : ByteStream := { data := (← Channel.new) }

    let respPromise ← IO.mkRef (← IO.asTask default)

    while true do
      let (newConnection, newStream, shouldBreak) ←
        processEvent connection stream fn respPromise

      connection := newConnection
      stream := newStream

      if shouldBreak then
        break

      connection := { connection with machine := connection.machine.advance }
      connection ← flushConnection connection true

    finalFlush connection
  catch err =>
    IO.println s!"ERR: {err}"

/--

-/
def serve (addr : Net.SocketAddress) (fn : Request Body → Async (Response Body)) : Async Unit := do
  let socket ← Socket.Server.mk
  socket.bind addr
  socket.listen 128

  while true do
    let clientTask ← socket.accept
    let client ← await clientTask
    let conn := Connection.mk client {}
    background .default (start conn fn)

end Connection
