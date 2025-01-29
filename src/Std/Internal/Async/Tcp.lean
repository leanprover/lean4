/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
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
namespace Tcp

open Std.Net

/--
A high-level wrapper around a TCP socket.
-/
structure Socket where
  private ofNative ::
    native : Internal.UV.Tcp.Socket

namespace Socket

/--
Create a new TCP socket.
-/
@[inline]
def mk : IO Socket := do
  let native ← Internal.UV.Tcp.Socket.new
  return Socket.ofNative native

/--
Bind the socket to the given address.
-/
@[inline]
def bind (s : Socket) (addr : SocketAddress) : IO Unit :=
  s.native.bind addr

/--
Connect the socket to the given address.
-/
@[inline]
def connect (s : Socket) (addr : SocketAddress) : IO (AsyncTask Unit) :=
  AsyncTask.ofPromise <$> s.native.connect addr

/--
Listen for incoming connections with the given backlog.
-/
@[inline]
def listen (s : Socket) (backlog : Int32) : IO Unit :=
  s.native.listen backlog

/--
Accept an incoming connection.
-/
@[inline]
def accept (s : Socket) : IO (AsyncTask Socket) := do
  let conn ← s.native.accept
  return conn.result.map (·.map Socket.ofNative)

/--
Send data through the socket.
-/
@[inline]
def send (s : Socket) (data : ByteArray) : IO (AsyncTask Unit) :=
  AsyncTask.ofPromise <$> s.native.send data

/--
Receive data from the socket.
-/
@[inline]
def recv (s : Socket) : IO (AsyncTask ByteArray) :=
  AsyncTask.ofPromise <$> s.native.recv

/--
Receive data from the socket.
-/
@[inline]
def shutdown (s : Socket) : IO (AsyncTask Unit) :=
  AsyncTask.ofPromise <$> s.native.shutdown

/--
Get the remote address of the connected socket.
-/
@[inline]
def getPeerName (s : Socket) : IO SocketAddress :=
  s.native.getpeername

/--
Get the local address of the socket.
-/
@[inline]
def getSockName (s : Socket) : IO SocketAddress :=
  s.native.getsockname

/--
Enable or disable the Nagle algorithm.
-/
@[inline]
def noDelay (s : Socket) : IO Unit :=
  s.native.nodelay

/--
Enable or disable TCP keep-alive with a specified delay.
-/
@[inline]
def keepAlive (s : Socket) (enable : Int32) (delay : UInt32) : IO Unit :=
  s.native.keepalive enable delay

end Socket
end Tcp
end Async
end IO
end Internal
end Std
