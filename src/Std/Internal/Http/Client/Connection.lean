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
  The server connection
  -/
  socket : α

  /--
  The processing machine for HTTP 1.1
  -/
  machine : Protocol.H1.Machine .sending

/--
A request packet to be sent through the persistent connection channel
-/
structure RequestPacket where

  /--
  The HTTP request to be sent
  -/
  request : Request Body

  /--
  A promise that resolves to the HTTP response once received
  -/
  responsePromise : IO.Promise (Except IO.Error (Response Body))

  /--
  A token used to cancel the request if needed
  -/
  cancellationToken : Std.CancellationToken

namespace RequestPacket

/--
Resolve the response promise with an error.
-/
def onError (packet : RequestPacket) (error : IO.Error) : IO Unit :=
  packet.responsePromise.resolve (.error error)

/--
Resolve the response promise with a successful response.
-/
def onResponse (packet : RequestPacket) (response : Response Body) : IO Unit :=
  packet.responsePromise.resolve (.ok response)

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
  requestChannel : CloseableChannel RequestPacket

  /--
  Shutdown Promise, resolves when the connection shuts down.
  -/
  shutdown : IO.Promise Unit

namespace PersistentConnection

/--
Send a request through the persistent connection.
-/
def send [Transport α] (pc : PersistentConnection α) (request : Request Body) : Async (Response Body) := do
  let responsePromise ← IO.Promise.new
  let cancellationToken ← Std.CancellationToken.new

  let task ← pc.requestChannel.send { request, responsePromise, cancellationToken }

  let .ok _ ← await task
    | throw (.userError "connection closed, cannot send more requests")

  Async.ofPromise (pure responsePromise)

/--
Close the persistent connection by closing the request channel.
-/
def close (pc : PersistentConnection α) : Async Unit := do
  pc.requestChannel.close

end PersistentConnection

namespace Connection

private def handle [Transport α] (connection : Connection α) (config : Client.Config) (requestChannel : CloseableChannel RequestPacket) : Async Unit := do
  let mut machine := connection.machine
  let socket := connection.socket


end Connection

/--
Create a persistent connection that can handle multiple sequential requests.

# Example

```lean
-- Connect to a server
let socket ← Socket.mk
socket.connect serverAddr

-- Create persistent connection
let pc ← createPersistentConnection socket config

-- Spawn the connection handler
async (pc.connection.handlePersistent pc.config pc.requestChannel)

-- Send multiple requests
pc.send request1 (fun response => IO.println s!"Response 1: {response.head.status}")
pc.send request2 (fun response => IO.println s!"Response 2: {response.head.status}")

-- Close when done
pc.close
```
-/
def createPersistentConnection [Transport t] (client : t) (config : Client.Config := {}) : Async (PersistentConnection t) := do
  let requestChannel ← CloseableChannel.new
  let connection := Connection.mk client { config := config.toH1Config }
  let shutdown ← IO.Promise.new

  let conn := { connection, requestChannel, shutdown }

  background (Connection.handle connection config requestChannel)

  return conn


end Std.Http.Client
