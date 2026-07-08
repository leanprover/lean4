/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module
prelude
public import Std.Async.TCP.SSL.Basic

/-!
TLS server socket operations: creating and configuring a `Server`, binding/listening, and accepting
incoming connections (`accept` / `acceptSelector`) with the TLS handshake driven to completion.
-/

public section

namespace Std.Async.TCP.SSL

open Std.Internal.SSL
open Std.Internal.UV.TCP
open Std Net Time
open Internal

namespace Server

/--
Creates a new TLS-enabled TCP server socket using the given context.
-/
@[inline]
def mk (serverCtx : Context.Server) : IO Server := do
  let native ← Socket.new
  return Server.ofNative native serverCtx

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

private def mkServerConn (native : Socket) (ctx : Context.Server) : IO ServerConn := do
  let ssl ← Session.Server.mk ctx
  let broken ← IO.mkRef false
  return ⟨native, .server ssl, broken⟩

private def establish (s : Server) (native : Socket) (chunkSize : UInt64)
    (timeout : Option Millisecond.Offset) : Async ServerConn := do
  let conn ← mkServerConn native s.serverCtx
  withConnection conn <| runHandshake conn.native conn.ssl.toSession chunkSize timeout
  return conn

/--
Accepts an incoming TLS connection and performs the TLS handshake.

If `timeout` is provided, each round-trip of the TLS handshake must complete
within that duration or the connection is dropped with `"TLS operation timed out"`.
Without a timeout, a stalled or malicious peer can cause this function to block
indefinitely.
-/
def accept (s : Server) (chunkSize : UInt64 := ioChunkSize) (timeout : Option Millisecond.Offset := none) : Async ServerConn := do
  let native ← Async.ofPromise <| s.native.accept
  establish s native chunkSize timeout

/--
Creates a `Selector` that resolves once `s` has accepted a connection and the TLS handshake
has completed.

The race is won as soon as a TCP connection is accepted; the TLS handshake then runs before the
selector resolves. A `Selectable.one` racing this selector against other cases therefore commits to
it at accept time (a raced timer cannot fire during the handshake — use `timeout` to bound it).
Conversely, if the selector loses the race after a TCP connection was already accepted, that raw
connection is dropped without a TLS handshake and closed by its finalizer.

If `timeout` is provided, each round-trip of the TLS handshake must complete within that
duration or the connection attempt is abandoned with `"TLS operation timed out"`.
-/
def acceptSelector (s : Server) (chunkSize : UInt64 := ioChunkSize)
    (timeout : Option Millisecond.Offset := none) : Selector ServerConn :=

  selectorFromWaiter
    (tryFn := pure none)
    (acquire := s.native.accept)
    (cont := fun native => establish s native chunkSize timeout)
    (cancel := s.native.cancelAccept)

/--
Gets the local address of the server socket.
-/
@[inline]
def getSockName (s : Server) : IO SocketAddress :=
  s.native.getSockName

/--
Disables the Nagle algorithm for all client sockets accepted by this server socket.
-/
@[inline]
def noDelay (s : Server) : IO Unit :=
  s.native.noDelay

/--
Enables TCP keep-alive for all client sockets accepted by this server socket.
`delay` must be at least 1 second.
-/
@[inline]
def keepAlive (s : Server) (enable : Bool) (delay : Std.Time.Second.Offset)
    (_ : delay.val ≥ 1 := by decide) : IO Unit :=
  s.native.keepAlive enable.toInt8 delay.val.toNat.toUInt32

end Server
end Std.Async.TCP.SSL
end
