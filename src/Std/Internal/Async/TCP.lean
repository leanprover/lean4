/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Std.Time
import Std.Internal.UV
import Std.Internal.Async.Basic
import Std.Net.Addr

namespace Std
namespace Internal
namespace IO
namespace Async
namespace TCP

open Std.Net

namespace Socket

/--
Represents a TCP server socket, managing incoming client connections.
-/
structure Server where
  private ofNative ::
    native : Internal.UV.TCP.Socket

/--
Represents a TCP client socket, used to connect to a server.
-/
structure Client where
  private ofNative ::
    native : Internal.UV.TCP.Socket

namespace Server

/--
Creates a new TCP server socket.
-/
@[inline]
def mk : IO Server := do
  let native ← Internal.UV.TCP.Socket.new
  return Server.ofNative native

/--
Binds the server socket to the specified address. Address reuse is enabled to allow rebinding the
same address.
-/
@[inline]
def bind (s : Server) (addr : SocketAddress) : IO Unit :=
  s.native.bind addr

/--
Listens for incoming connections with the given backlog.
-/
@[inline]
def listen (s : Server) (backlog : UInt32) : IO Unit :=
  s.native.listen backlog

/--
Accepts an incoming connection.
-/
@[inline]
def accept (s : Server) : IO (AsyncTask Client) := do
  let conn ← s.native.accept
  return conn.result!.map (·.map Client.ofNative)

/--
Gets the local address of the server socket.
-/
@[inline]
def getSockName (s : Server) : IO SocketAddress :=
  s.native.getSockName

/--
Enables the Nagle algorithm for all client sockets accepted by this server socket.
-/
@[inline]
def noDelay (s : Server) : IO Unit :=
  s.native.noDelay

/--
Enables TCP keep-alive for all client sockets accepted by this server socket.
-/
@[inline]
def keepAlive (s : Server) (enable : Bool) (delay : Std.Time.Second.Offset) (_ : delay.val ≥ 1 := by decide) : IO Unit :=
  s.native.keepAlive enable.toInt8 delay.val.toNat.toUInt32

end Server

namespace Client

/--
Creates a new TCP client socket.
-/
@[inline]
def mk : IO Client := do
  let native ← Internal.UV.TCP.Socket.new
  return Client.ofNative native

/--
Binds the server socket to the specified address. Address reuse is enabled to allow rebinding the
same address.
-/
@[inline]
def bind (s : Client) (addr : SocketAddress) : IO Unit :=
  s.native.bind addr

/--
Connects the client socket to the given address.
-/
@[inline]
def connect (s : Client) (addr : SocketAddress) : IO (AsyncTask Unit) :=
  AsyncTask.ofPromise <$> s.native.connect addr

/--
Sends data through the client socket.
-/
@[inline]
def send (s : Client) (data : ByteArray) : IO (AsyncTask Unit) :=
  AsyncTask.ofPromise <$> s.native.send data

/--
Receives data from the client socket. If data is received, it’s wrapped in .some. If EOF is reached,
the result is .none, indicating no more data is available. Receiving data in parallel on the same
socket is not supported. Instead, we recommend binding multiple sockets to the same address.
-/
@[inline]
def recv? (s : Client) (size : UInt64) : IO (AsyncTask (Option ByteArray)) :=
  AsyncTask.ofPromise <$> s.native.recv? size

/--
Shuts down the write side of the client socket.
-/
@[inline]
def shutdown (s : Client) : IO (AsyncTask Unit) :=
  AsyncTask.ofPromise <$> s.native.shutdown

/--
Gets the remote address of the client socket.
-/
@[inline]
def getPeerName (s : Client) : IO SocketAddress :=
  s.native.getPeerName

/--
Gets the local address of the client socket.
-/
@[inline]
def getSockName (s : Client) : IO SocketAddress :=
  s.native.getSockName

/--
Enables the Nagle algorithm for the client socket.
-/
@[inline]
def noDelay (s : Client) : IO Unit :=
  s.native.noDelay

/--
Enables TCP keep-alive with a specified delay for the client socket.
-/
@[inline]
def keepAlive (s : Client) (enable : Bool) (delay : Std.Time.Second.Offset) (_ : delay.val ≥ 0 := by decide) : IO Unit :=
  s.native.keepAlive enable.toInt8 delay.val.toNat.toUInt32

end Client

end Socket
end TCP
end Async
end IO
end Internal
end Std
