/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Init
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

private def handleResponse (connection : Connection) (response : Response Body) : Async Connection := do
  match response.body with
  | .zero =>
    pure { connection with machine := connection.machine.close }
  | .bytes bytes =>
    pure { connection with machine := connection.machine.writeData bytes |>.close }
  | .stream st => do
    match ← await (← st.data.recv) with
    | some data =>
      pure { connection with machine := connection.machine.writeData data }
    | none =>
      pure { connection with machine := connection.machine.close }

private def receiveData (socket : Socket.Client) : Async ByteArray := do
  try
    let some data ← await (← socket.recv? 4096) | pure .empty
    pure data
  catch err =>
    IO.println s!"Network error: {err}"
    pure .empty

private def handleRequest
  (connection : Connection)
  (fn : Request Body → Async (Response Body))
  (stream : ByteStream)
  : Async (Response Body) := do
    if let some (method, uri, version) := connection.machine.inputStatusLine then
      fn (Request.mk method version uri connection.machine.inputHeaders (.stream stream))
    else
      panic! "Missing status line - Invalid state"

private def updateConnectionForClose (event : Event mode) (connection : Connection) : Connection :=
  match event with
  | .failed _ => { connection with machine := connection.machine.advance }
  | .close => { connection with machine := connection.machine.close }
  | _ => connection

private def processSpecificEvent
  (event : Event mode)
  (connection : Connection)
  (stream : ByteStream)
  (fn : Request Body → Async (Response Body))
  (response : Response Body)
    : Async (Connection × ByteStream × Option (Response Body)) := do
    match event with
    | .chunkExt _ =>
      pure (connection, stream, none)
    | .endHeaders _ => do
      let newStream := { data := (← Channel.new) }
      let response ← handleRequest connection fn newStream
      pure (connection, newStream, some response)
    | .gotData final data => do
      await (← stream.data.send data)
      if final then await (← stream.data.send none)
      pure (connection, stream, none)
    | .needMoreData => do
      let data ← receiveData connection.socket
      let connection := { connection with machine := connection.machine.incomeFeed data }
      pure (connection, stream, none)

    | .awaitingAnswer => do
      let connection ← handleResponse connection response
      pure (connection, stream, none)
    | .readyToRespond => do
      let connection := { connection with machine := connection.machine.answer response }
      pure (connection, stream, none)
    | .close | .next | .failed _ => do
      await (← stream.data.send none)
      let connection := updateConnectionForClose event connection
      pure (connection, stream, none)


-- Event processing abstraction
private def processEvent
  (connection : Connection)
  (stream : ByteStream)
  (fn : Request Body → Async (Response Body))
  : Async (Connection × ByteStream × Option (Response Body)) := do
    match connection.machine.event with
    | some event => processSpecificEvent event connection stream fn default
    | none => pure (connection, stream, none)

/--
Starts to process the socket in the machine.
-/
private partial def start (connection : Connection) (fn : Request Body → Async (Response Body)) : Async Unit := do
  let mut connection := connection

  let mut stream : ByteStream := { data := (← Channel.new) }
  let mut response : Response Body := Inhabited.default

  while true do
    match connection.machine.event with
    | some event =>
      match event with
      | .chunkExt _ =>
        pure ()
      | .endHeaders _ =>
        stream := { data := (← Channel.new) }

        if let some (method, uri, version) := connection.machine.inputStatusLine then
          response ← fn (Request.mk method version uri connection.machine.inputHeaders (.stream stream))
        else
          panic! "shoujndt happend"
      | .gotData final data =>
        await (← stream.data.send data)

        if final then
          await (← stream.data.send none)

      | .needMoreData =>

        let data ← do
          try
            let some data ← await (← connection.socket.recv? 8096)
              | break
            pure data
          catch err =>
            IO.println s!"err: {err}"
            pure .empty

        if .empty == data then
          break

        connection := { connection with machine := connection.machine.incomeFeed data }
      | .awaitingAnswer =>
        match response.body with
        | .zero =>
          connection := { connection with machine := connection.machine |>.close }
          break
        | .bytes bytes =>
          connection := { connection with machine := connection.machine.writeData bytes |>.close }
          break
        | .stream st =>
          match ← await (← st.data.recv) with
          | some data =>
            connection := { connection with machine := connection.machine.writeData data }
          | none =>
            connection := { connection with machine := connection.machine.close }
            break
      | .readyToRespond =>
         connection := { connection with machine := connection.machine.answer response }
      | .close =>
        await (← stream.data.send none)
        break
      | .next =>
        await (← stream.data.send none)
        pure ()
      | .failed _ =>
        await (← stream.data.send none)
        connection := { connection with machine := connection.machine.advance }
        break
    | none => pure ()

    connection := { connection with machine := connection.machine.resetEvent.advance }

    if connection.machine.needsFlush then
      let (machine, ba) := connection.machine.flush
      await (← connection.socket.send ba)
      connection := { connection with machine }

  let (_, ba) := connection.machine.flush

  if ba.size > 0 then
    await (← connection.socket.send ba)

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
