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
namespace TCP

open Std.Net

/--
A high-level wrapper around a TCP socket.
-/
structure Socket where
  private ofNative ::
    native : Internal.UV.TCP.Socket

namespace Socket

/--
Creates a new TCP socket.
-/
@[inline]
def mk : IO Socket := do
  let native ← Internal.UV.TCP.Socket.new
  return Socket.ofNative native

/--
Binds the socket to the given address.
-/
@[inline]
def bind (s : Socket) (addr : SocketAddress) : IO Unit :=
  s.native.bind addr

/--
Connects the socket to the given address.
-/
@[inline]
def connect (s : Socket) (addr : SocketAddress) : IO (AsyncTask Unit) :=
  AsyncTask.ofPromise <$> s.native.connect addr

/--
Listens for incoming connections with the given backlog.
-/
@[inline]
def listen (s : Socket) (backlog : UInt32) : IO Unit :=
  s.native.listen backlog

/--
Accepts an incoming connection.
-/
@[inline]
def accept (s : Socket) : IO (AsyncTask Socket) := do
  let conn ← s.native.accept
  return conn.result.map (·.map Socket.ofNative)

/--
Sends data through the socket.
-/
@[inline]
def send (s : Socket) (data : ByteArray) : IO (AsyncTask Unit) :=
  AsyncTask.ofPromise <$> s.native.send data

/--
Receives data from the socket.
-/
@[inline]
def recv (s : Socket) (size : UInt64) : IO (AsyncTask ByteArray) :=
  AsyncTask.ofPromise <$> s.native.recv size

/--
Shuts down the socket.
-/
@[inline]
def shutdown (s : Socket) : IO (AsyncTask Unit) :=
  AsyncTask.ofPromise <$> s.native.shutdown

/--
Gets the remote address of the connected socket.
-/
@[inline]
def getPeerName (s : Socket) : IO SocketAddress :=
  s.native.getpeername

/--
Gets the local address of the socket.
-/
@[inline]
def getSockName (s : Socket) : IO SocketAddress :=
  s.native.getsockname

/--
Enables the Nagle algorithm.
-/
@[inline]
def noDelay (s : Socket) : IO Unit :=
  s.native.nodelay

/--
Enables TCP keep-alive with a specified delay.
-/
@[inline]
def keepAlive (s : Socket) (enable : Bool) (delay : Std.Time.Second.Offset) (_ : delay.val ≥ 0 := by decide) : IO Unit :=
  s.native.keepalive enable delay.val.toNat.toUInt32

end Socket
end TCP
end Async
end IO
end Internal
end Std
