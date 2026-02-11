/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Internal.Http.Protocol.H1

public section

/-!
# Transport

This module exposes a `Transport` type class that is used to represent different transport mechanisms
that can be used with a HTTP connection.
-/

namespace Std.Http
open Std Internal IO Async TCP

set_option linter.all true

/--
Generic HTTP interface that abstracts over different transport mechanisms.
-/
class Transport (α : Type) where
  /--
  Receive data from the client connection, up to the expected size.
  Returns None if the connection is closed or no data is available.
  -/
  recv : α → UInt64 → Async (Option ByteArray)

  /--
  Send all data through the client connection.
  -/
  sendAll : α → Array ByteArray → Async Unit

  /--
  Get a selector for receiving data asynchronously.
  -/
  recvSelector : α → UInt64 → Selector (Option ByteArray)

  /--
  Close the transport connection. This is a no-op for socket-based transports.
  -/
  close : α → IO Unit := fun _ => pure ()

instance : Transport Socket.Client where
  recv client expect := client.recv? expect
  sendAll client data := client.sendAll data
  recvSelector client expect := client.recvSelector expect

open Internal.IO.Async in

/--
Shared state for a bidirectional mock connection.
-/
private structure MockLink.SharedState where
  /--
  Client to server direction.
  -/
  clientToServer : Std.CloseableChannel ByteArray

  /--
  Server to client direction.
  -/
  serverToClient : Std.CloseableChannel ByteArray

/--
Mock client endpoint for testing.
-/
structure Mock.Client where
  private shared : MockLink.SharedState

/--
Mock server endpoint for testing.
-/
structure Mock.Server where
  private shared : MockLink.SharedState

namespace Mock

/--
Create a mock server and client that are connected to each other and share the
same underlying state, enabling bidirectional communication.
-/
def new : BaseIO (Mock.Client × Mock.Server) := do
  let first ← Std.CloseableChannel.new
  let second ← Std.CloseableChannel.new

  return (⟨⟨first, second⟩⟩, ⟨⟨first, second⟩⟩)

/--
Receive data from a channel, joining all available data up to the expected size. First does a
blocking recv, then greedily consumes available data with tryRecv until `expect` bytes are reached.
-/
def recvJoined (recvChan : Std.CloseableChannel ByteArray) (expect : Option UInt64) : Async (Option ByteArray) := do
  match ← await (← recvChan.recv) with
  | none => return none
  | some first =>
    let mut result := first
    repeat
      if let some expect := expect then
        if result.size.toUInt64 ≥ expect then break

      match ← recvChan.tryRecv with
      | none => break
      | some chunk => result := result ++ chunk
    return some result

/--
Send a single ByteArray through a channel.
-/
def send (sendChan : Std.CloseableChannel ByteArray) (data : ByteArray) : Async Unit := do
  Async.ofAsyncTask ((← sendChan.send data) |>.map (Except.mapError (IO.userError ∘ toString)))

/--
Send ByteArrays through a channel.
-/
def sendAll (sendChan : Std.CloseableChannel ByteArray) (data : Array ByteArray) : Async Unit := do
  for chunk in data do
    send sendChan chunk

/--
Create a selector for receiving from a channel with joining behavior.
-/
def recvSelector (recvChan : Std.CloseableChannel ByteArray) : Selector (Option ByteArray) :=
  recvChan.recvSelector

end Mock

namespace Mock.Client

/--
Get the receive channel for a client (server to client direction).
-/
def getRecvChan (client : Mock.Client) : Std.CloseableChannel ByteArray :=
  client.shared.serverToClient

/--
Get the send channel for a client (client to server direction).
-/
def getSendChan (client : Mock.Client) : Std.CloseableChannel ByteArray :=
  client.shared.clientToServer

/--
Send a single ByteArray.
-/
def send (client : Mock.Client) (data : ByteArray) : Async Unit :=
  Mock.send (getSendChan client) data

/--
Receive data, joining all available chunks.
-/
def recv? (client : Mock.Client) (expect : Option UInt64 := none) : Async (Option ByteArray) :=
  Mock.recvJoined (getRecvChan client) expect

/--
Try to receive data without blocking, joining all immediately available chunks.
Returns `none` if no data is available.
-/
def tryRecv? (client : Mock.Client) (_expect : UInt64 := 0) : BaseIO (Option ByteArray) := do
  match ← (getRecvChan client).tryRecv with
  | none => return none
  | some first =>
    let mut result := first
    repeat
      match ← (getRecvChan client).tryRecv with
      | none => break
      | some chunk => result := result ++ chunk
    return some result

/--
Close the mock server and client.
-/
def close (client : Mock.Client) : IO Unit := do
  if !(← client.shared.clientToServer.isClosed) then client.shared.clientToServer.close
  if !(← client.shared.serverToClient.isClosed) then client.shared.serverToClient.close

end Mock.Client

namespace Mock.Server

/--
Get the receive channel for a server (client to server direction).
-/
def getRecvChan (server : Mock.Server) : Std.CloseableChannel ByteArray :=
  server.shared.clientToServer

/--
Get the send channel for a server (server to client direction).
-/
def getSendChan (server : Mock.Server) : Std.CloseableChannel ByteArray :=
  server.shared.serverToClient

/--
Send a single ByteArray.
-/
def send (server : Mock.Server) (data : ByteArray) : Async Unit :=
  Mock.send (getSendChan server) data

/--
Receive data, joining all available chunks.
-/
def recv? (server : Mock.Server) (expect : Option UInt64 := none) : Async (Option ByteArray) :=
  Mock.recvJoined (getRecvChan server) expect

/--
Try to receive data without blocking, joining all immediately available chunks. Returns `none` if no
data is available.
-/
def tryRecv? (server : Mock.Server) (_expect : UInt64 := 0) : BaseIO (Option ByteArray) := do
  match ← (getRecvChan server).tryRecv with
  | none => return none
  | some first =>
    let mut result := first
    repeat
      match ← (getRecvChan server).tryRecv with
      | none => break
      | some chunk => result := result ++ chunk
    return some result

/--
Close the mock server and client.
-/
def close (server : Mock.Server) : IO Unit := do
  if !(← server.shared.clientToServer.isClosed) then server.shared.clientToServer.close
  if !(← server.shared.serverToClient.isClosed) then server.shared.serverToClient.close


end Mock.Server

instance : Transport Mock.Client where
  recv client expect := Mock.recvJoined (Mock.Client.getRecvChan client) (some expect)
  sendAll client data := Mock.sendAll (Mock.Client.getSendChan client) data
  recvSelector client _ := Mock.recvSelector (Mock.Client.getRecvChan client)
  close client := client.close

instance : Transport Mock.Server where
  recv server expect := Mock.recvJoined (Mock.Server.getRecvChan server) (some expect)
  sendAll server data := Mock.sendAll (Mock.Server.getSendChan server) data
  recvSelector server _ := Mock.recvSelector (Mock.Server.getRecvChan server)
  close server := server.close

end Std.Http
