/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Time
public import Std.Internal.UV.TCP
public import Std.Internal.Async.Timer
public import Std.Internal.Async.Select
public import Std.Internal.SSL

public section

namespace Std
namespace Internal
namespace IO
namespace Async
namespace TCP
namespace SSL

open Std.Net

/--
Default chunk size used by TLS I/O loops.
-/
def ioChunkSize : UInt64 := 16 * 1024

/--
Represents a TLS-enabled TCP server socket.
-/
structure Server where
  private ofNative ::
    native : Internal.UV.TCP.Socket

/--
Represents a TLS-enabled TCP client socket.
-/
structure Client where
  private ofNative ::
    native : Internal.UV.TCP.Socket
    ssl : Std.Internal.SSL.Session

@[inline]
private def feedEncryptedChunk (ssl : Std.Internal.SSL.Session) (encrypted : ByteArray) : Async Unit := do
  if encrypted.size == 0 then
    return ()
  let consumed ← ssl.feedEncrypted encrypted
  if consumed.toNat != encrypted.size then
    throw <| IO.userError s!"TLS input short write: consumed {consumed} / {encrypted.size} bytes"

@[inline]
private partial def flushEncrypted (native : Internal.UV.TCP.Socket) (ssl : Std.Internal.SSL.Session) : Async Unit := do
  let out ← ssl.drainEncrypted
  if out.size == 0 then
    return ()
  Async.ofPromise <| native.send #[out]
  flushEncrypted native ssl

/--
Runs the TLS handshake loop until the handshake is established.
-/
private partial def handshake (native : Internal.UV.TCP.Socket) (ssl : Std.Internal.SSL.Session) (chunkSize : UInt64 := ioChunkSize) : Async Unit := do
  let done ← ssl.handshake
  flushEncrypted native ssl
  if done then
    return ()
  let encrypted? ← Async.ofPromise <| native.recv? chunkSize
  match encrypted? with
  | none =>
    throw <| IO.userError "peer closed connection before TLS handshake completed"
  | some encrypted =>
    feedEncryptedChunk ssl encrypted
    handshake native ssl chunkSize

namespace Server

/--
Configures the shared TLS server context with PEM certificate and private key files.
-/
@[inline]
def configureContext (certFile keyFile : String) : IO Unit :=
  Std.Internal.SSL.configureServerContext certFile keyFile

/--
Creates a new TLS-enabled TCP server socket.
-/
@[inline]
def mk : IO Server := do
  let native ← Internal.UV.TCP.Socket.new
  return Server.ofNative native

/--
Binds the server socket to the specified address.
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

@[inline] private def mkServerClient (native : Internal.UV.TCP.Socket) : IO Client := do
  let ssl ← Std.Internal.SSL.Session.mkServer
  return Client.ofNative native ssl

/--
Accepts an incoming TLS client connection and performs the TLS handshake.
-/
@[inline]
def accept (s : Server) (chunkSize : UInt64 := ioChunkSize) : Async Client := do
  let native ← Async.ofPromise <| s.native.accept
  let client ← mkServerClient native
  SSL.handshake client.native client.ssl chunkSize
  return client

/--
Tries to accept an incoming TLS client connection.
-/
@[inline]
def tryAccept (s : Server) : IO (Option Client) := do
  let res ← s.native.tryAccept
  let socket ← IO.ofExcept res
  match socket with
  | none => return none
  | some native => return some (← mkServerClient native)

/--
Creates a `Selector` that resolves once `s` has a connection available.
-/
def acceptSelector (s : TCP.SSL.Server) : Selector Client :=
  {
    tryFn :=
      s.tryAccept

    registerFn waiter := do
      let task ← s.native.accept

      -- If we get cancelled the promise will be dropped so prepare for that
      IO.chainTask (t := task.result?) fun res => do
        match res with
        | none => return ()
        | some res =>
          let lose := return ()
          let win promise := do
            try
              let native ← IO.ofExcept res
              let ssl ← Std.Internal.SSL.Session.mkServer
              promise.resolve (.ok (Client.ofNative native ssl))
            catch e =>
              promise.resolve (.error e)
          waiter.race lose win

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
def keepAlive (s : Server) (enable : Bool) (delay : Std.Time.Second.Offset) (_ : delay.val ≥ 1 := by decide) : IO Unit :=
  s.native.keepAlive enable.toInt8 delay.val.toNat.toUInt32

end Server

namespace Client

/--
Configures the shared TLS client context.
`caFile` may be empty to use default trust settings.
-/
@[inline]
def configureContext (caFile := "") (verifyPeer := true) : IO Unit :=
  Std.Internal.SSL.configureClientContext caFile verifyPeer

/--
Creates a new TLS-enabled TCP client socket with a client-side TLS session.
-/
@[inline]
def mk : IO Client := do
  let native ← Internal.UV.TCP.Socket.new
  let ssl ← Std.Internal.SSL.Session.mkClient
  return Client.ofNative native ssl

/--
Binds the client socket to the specified address.
-/
@[inline]
def bind (s : Client) (addr : SocketAddress) : IO Unit :=
  s.native.bind addr

/--
Sets SNI server name used during the TLS handshake.
-/
@[inline]
def setServerName (s : Client) (host : String) : IO Unit :=
  s.ssl.setServerName host

/--
Performs the TLS handshake on an established TCP connection.
-/
@[inline]
def handshake (s : Client) (chunkSize : UInt64 := ioChunkSize) : Async Unit :=
  SSL.handshake s.native s.ssl chunkSize

/--
Connects the client socket to the given address and performs the TLS handshake.
-/
@[inline]
def connect (s : Client) (addr : SocketAddress) (chunkSize : UInt64 := ioChunkSize) : Async Unit := do
  Async.ofPromise <| s.native.connect addr
  s.handshake chunkSize

/--
Attempts to write plaintext data into TLS. Returns true when accepted.
Any encrypted TLS output generated is flushed to the socket.
-/
@[inline]
def write (s : Client) (data : ByteArray) : Async Bool := do
  let accepted ← s.ssl.write data
  flushEncrypted s.native s.ssl
  return accepted

/--
Sends data through a TLS-enabled socket.
Fails if OpenSSL reports the write as pending additional I/O.
-/
@[inline]
def send (s : Client) (data : ByteArray) : Async Unit := do
  if ← s.write data then
    return ()
  else
    throw <| IO.userError "TLS write is pending additional I/O; call `recv?` or retry later"

/--
Sends multiple data buffers through the TLS-enabled socket.
-/
@[inline]
def sendAll (s : Client) (data : Array ByteArray) : Async Unit :=
  data.forM (s.send ·)

/--
Receives decrypted plaintext data from TLS.
If no plaintext is immediately available, this function pulls encrypted data from TCP first.
-/
partial def recv? (s : Client) (size : UInt64) (chunkSize : UInt64 := ioChunkSize) : Async (Option ByteArray) := do
  match ← s.ssl.read? size with
  | some plain =>
    flushEncrypted s.native s.ssl
    return some plain
  | none =>
    flushEncrypted s.native s.ssl
    let encrypted? ← Async.ofPromise <| s.native.recv? chunkSize
    match encrypted? with
    | none =>
      return none
    | some encrypted =>
      feedEncryptedChunk s.ssl encrypted
      recv? s size chunkSize

/--
Tries to receive decrypted plaintext data without blocking.
Returns `some (some data)` if plaintext is available, `some none` if the peer closed,
or `none` if no data is ready yet.
-/
partial def tryRecv (s : Client) (size : UInt64) (chunkSize : UInt64 := ioChunkSize) : Async (Option (Option ByteArray)) := do
  let pending ← s.ssl.pendingPlaintext

  if pending > 0 then
    let res ← s.recv? size
    return some res
  else
    let readableWaiter ← s.native.waitReadable

    flushEncrypted s.native s.ssl

    if ← readableWaiter.isResolved then
      let encrypted? ← Async.ofPromise <| s.native.recv? ioChunkSize
      match encrypted? with
      | none =>
        return none
      | some encrypted =>
        feedEncryptedChunk s.ssl encrypted
        tryRecv s size chunkSize
    else
      s.native.cancelRecv
      return none

/--
Feeds encrypted socket data into SSL until plaintext is pending.
Resolves the returned promise once plaintext is available. If no more socket data
is available (or the promise gets dropped), it exits without resolving.
-/
partial def waitReadable (s : Client) (chunkSize : UInt64 := ioChunkSize) : Async Unit := do
  if (← s.ssl.pendingPlaintext) > 0 then
    return ()

  let rec go : Async Unit := do
    let readable ← Async.ofPromise <| s.native.waitReadable

    if !readable then
      return ()

    let encrypted? ← Async.ofPromise <| s.native.recv? chunkSize

    match encrypted? with
    | none =>
      return ()
    | some encrypted =>
      feedEncryptedChunk s.ssl encrypted
      flushEncrypted s.native s.ssl

      if (← s.ssl.pendingPlaintext) > 0 then
        return ()
      else
        go

  go

/--
Creates a `Selector` that resolves once `s` has plaintext data available.
-/
def recvSelector (s : TCP.SSL.Client) (size : UInt64) : Selector (Option ByteArray) :=
  {
    tryFn := s.tryRecv size

    registerFn waiter := do
      let readableWaiter ← s.waitReadable.asTask

      -- If we get cancelled the promise will be dropped so prepare for that
      discard <| IO.mapTask (t := readableWaiter) fun res => do
        match res with
        | .error _ => return ()
        | .ok _ =>
          let lose := return ()
          let win promise := do
            try
              -- We know that this read should not block.
              let result ← (s.recv? size).block
              promise.resolve (.ok result)
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
Returns the X.509 verification result code for this TLS session.
-/
@[inline]
def verifyResult (s : Client) : IO UInt64 :=
  s.ssl.verifyResult

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

end SSL
end TCP
end Async
end IO
end Internal
end Std
