/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module
prelude
public import Std.Async.TCP.SSL.Basic

/-!
TLS client connection setup: creating a `Client`, configuring SNI/hostname verification, and
establishing the connection (`connect` / `handshake`).
-/

public section

namespace Std.Async.TCP.SSL

open Std.Internal.SSL
open Std.Internal.UV.TCP
open Std Net Time
open Internal

namespace Client

/--
Creates a new outgoing TLS client connection using the given client context. `serverName` is set on
the role-typed client session before any handshake can run: pass `some host` to enable SNI and
certificate hostname verification, or pass `none` explicitly for connections that do not use a DNS
name.
-/
def mk (ctx : Context.Client) (serverName : Option String) : IO Client := do
  let native ← Socket.new
  let ssl ← Session.Client.mk ctx

  if let some host := serverName then
    ssl.setServerName host

  let broken ← IO.mkRef false
  return ⟨native, .client ssl, broken⟩

/--
Binds the client socket to the specified address.
-/
@[inline]
def bind (s : Client) (addr : SocketAddress) : IO Unit :=
  s.native.bind addr

/--
Performs the TLS handshake on an established TCP connection.

If `timeout` is provided, each round-trip of the handshake must complete within
that duration or the function throws `"TLS operation timed out"`. Without a
timeout, a stalled or malicious peer can cause this function to block indefinitely.
-/
def handshake (s : Client) (chunkSize : UInt64 := ioChunkSize)
    (timeout : Option Std.Time.Millisecond.Offset := none) : Async Unit := do
  withConnection s <| runHandshake s.native s.ssl.toSession chunkSize timeout

/--
Connects the client socket to the given address and performs the TLS handshake.
The server name, including the explicit choice to omit one, is configured by `Client.mk`.

If `timeout` is provided, each TCP round-trip of the TLS handshake must complete
within that duration or the function throws `"TLS operation timed out"`. Note: the
initial TCP connect itself is not covered by this timeout.
-/
def connect (s : Client) (addr : SocketAddress) (chunkSize : UInt64 := ioChunkSize)
    (timeout : Option Std.Time.Millisecond.Offset := none) : Async Unit := do

  withConnection s do
    Async.ofPromise <| s.native.connect addr
    runHandshake s.native s.ssl.toSession chunkSize timeout

end Client
end Std.Async.TCP.SSL
end
