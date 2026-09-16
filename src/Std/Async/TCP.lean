/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Time
public import Std.Internal.UV.TCP
public import Std.Async.Select

public section

namespace Std
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
The delay passed to libuv, which takes the seconds as a `UInt32`.
-/
private def keepAliveDelay (delay : Std.Time.Second.Offset) : IO UInt32 := do
  let seconds := delay.val.toNat
  if seconds < UInt32.size then
    return seconds.toUInt32
  throw <| IO.userError s!"keep-alive delay of {seconds} s is too large"

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
def accept (s : Server) : Async Client := do
  s.native.accept
  |> Async.ofPromise
  |>.map Client.ofNative

/--
Tries to accept an incoming connection.
-/
@[inline]
def tryAccept (s : Server) : IO (Option Client) := do
  let res ← s.native.tryAccept
  let socket ← IO.ofExcept res
  return Client.ofNative <$> socket

/--
Creates a `Selector` that resolves once `s` has a connection available. Calling this function
does not start the connection wait, so it must not be called in parallel with `accept`.
-/
def acceptSelector (s : TCP.Socket.Server) : Selector Client :=
  {
    tryFn :=
      s.tryAccept

    registerFn waiter := do
      let ready ← s.native.waitAcceptable

      -- If we get cancelled the promise will be dropped so prepare for that
      IO.chainTask (t := ready.result?) fun
        | none => pure ()
        | some res =>
          waiter.race (lose := pure ()) fun promise => do
            -- A connection is pending, so this accept does not wait.
            match ← (do IO.ofExcept res; s.tryAccept).toBaseIO with
            | .ok (some client) => promise.resolve (.ok client)
            | .ok none => promise.resolve (.error (.userError "the pending connection was accepted concurrently"))
            | .error e => promise.resolve (.error e)

    unregisterFn := s.native.cancelAccept
  }

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
def keepAlive (s : Server) (enable : Bool) (delay : Std.Time.Second.Offset) (_ : delay.val ≥ 1 := by decide) : IO Unit := do
  s.native.keepAlive enable.toInt8 (← keepAliveDelay delay)

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
def connect (s : Client) (addr : SocketAddress) : Async Unit :=
  Async.ofPromise <| s.native.connect addr

/--
Sends multiple data buffers through the client socket.
-/
@[inline]
def sendAll (s : Client) (data : Array ByteArray) : Async Unit :=
  Async.ofPromise <| s.native.send data

/--
Sends data through the client socket.
-/
@[inline]
def send (s : Client) (data : ByteArray) : Async Unit :=
  Async.ofPromise <| s.native.send #[data]

/--
Receives data from the client socket. If data is received, it’s wrapped in .some. If EOF is reached,
the result is .none, indicating no more data is available. Receiving data in parallel on the same
socket is not supported. Instead, we recommend binding multiple sockets to the same address.
Furthermore calling this function in parallel with `recvSelector` is not supported.
-/
@[inline]
def recv? (s : Client) (size : UInt64) : Async (Option ByteArray) :=
  Async.ofPromise <| s.native.recv? size

/--
Creates a `Selector` that resolves once `s` has data available, up to at most `size` bytes,
and provides that data. Calling this function does not starts the data wait, so it must not be called
in parallel with `recv?`.
-/
def recvSelector (s : TCP.Socket.Client) (size : UInt64) : Selector (Option ByteArray) :=
  {
    tryFn := do
      let readableWaiter ← s.native.waitReadable

      if ← readableWaiter.isResolved then
        let res ← s.recv? size
        return some res
      else
        s.native.cancelRecv
        return none

    registerFn waiter := do
      let readableWaiter ← s.native.waitReadable

      -- If we get cancelled the promise will be dropped so prepare for that
      discard <| IO.mapTask (t := readableWaiter.result?) fun res => do
        match res with
        | none => return ()
        | some res =>
          let lose := return ()
          let win promise := do
            try
              discard <| IO.ofExcept res
              let readPromise ← s.native.recv? size
              discard <| BaseIO.mapTask (t := AsyncTask.ofPromise readPromise) promise.resolve
            catch e =>
              promise.resolve (.error e)
          waiter.race lose win

    unregisterFn := s.native.cancelRecv
  }

/--
Shuts down the write side of the client socket.
-/
@[inline]
def shutdown (s : Client) : Async Unit :=
  Async.ofPromise <| s.native.shutdown

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
def keepAlive (s : Client) (enable : Bool) (delay : Std.Time.Second.Offset) (_ : delay.val ≥ 0 := by decide) : IO Unit := do
  s.native.keepAlive enable.toInt8 (← keepAliveDelay delay)

end Client
end Socket
end TCP
end Async
end Std
