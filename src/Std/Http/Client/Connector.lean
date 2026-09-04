/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Http.Client.Connection
import Std.Async.DNS

public section

/-!
# Connector

A `Connector` abstracts DNS resolution and TCP/transport connection establishment for the
connection pool.

The default `Connector.tcp` resolves via the system DNS and dials a raw TCP socket.
-/

namespace Std.Http.Client

open Std Async TCP
open Time

set_option linter.all true

/--
Opens a new transport connection for `origin` and wraps it in a `Connection`.

Supply your own function to customize DNS resolution or transport selection (plain TCP, TLS,
Unix socket). `origin.scheme` is provided so implementations can dispatch between plain and
encrypted transports; `config.proxySelector` names the endpoint to dial for `origin`.

The `Connection` handed back must be opened for the same `origin`, since that is the origin its
requests are addressed to and its cookies and credentials are scoped by.

Failures are reported as a typed `Error` (usually `Error.connect`). An exception thrown by a
connector is also treated as a connect failure by the client.
-/
abbrev Connector := URI.Origin → Config → Async (Except Error Connection)

/--
The default connector: resolves the origin's host via the system DNS, iterates over the returned
addresses, and opens a TCP socket to the first one that succeeds.

When `config.proxySelector` routes `origin` through a proxy, the TCP connection is made to the
proxy address instead and the origin is left for the HTTP layer to address.
-/
def Connector.tcp : Connector := fun origin config => do

  if origin.scheme.val == "https" then
    return .error (.connect "default TCP connector does not support https.")

  if origin.scheme.val != "http" then
    return .error (.connect
      s!"default TCP connector only supports http, got scheme {origin.scheme.val.quote}")

  let (connectHost, connectPort) :=
    match config.proxySelector.select origin with
    | .direct => (toString origin.host, origin.port)
    | .http proxyHost proxyPort => (proxyHost, proxyPort)
  let addrs ←
    try DNS.getAddrInfo connectHost (toString connectPort)
    catch err => return .error (.connect (toString err))

  if addrs.isEmpty then
    return .error (.connect s!"could not resolve host: {connectHost.quote}")

  let mut lastErr : Error := .connect s!"could not connect to {connectHost.quote}:{connectPort}"

  for ipAddr in addrs do
    let socketAddr : Std.Net.SocketAddress := match ipAddr with
      | .v4 ip => .v4 ⟨ip, connectPort⟩
      | .v6 ip => .v6 ⟨ip, connectPort⟩
    try
      let socket ← Socket.Client.mk
      socket.connect socketAddr
      return .ok (← Connection.new socket origin config)
    catch err =>
      lastErr := .connect (toString err)

  return .error lastErr

end Std.Http.Client
