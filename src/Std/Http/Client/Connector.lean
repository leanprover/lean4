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

  -- A scheme this connector cannot serve is the request's problem, not a failed connection: as a
  -- connect error it would count as never sent and be tried again to no purpose.
  if origin.scheme.val == "https" then
    return .error (.invalidRequest "the default TCP connector does not support https")

  if origin.scheme.val != "http" then
    return .error (.invalidRequest
      s!"the default TCP connector only supports http, got scheme {origin.scheme.val.quote}")

  let (connectHost, connectPort, literal) : String × UInt16 × Option Std.Net.IPAddr :=
    match config.proxySelector.select origin with
    | .direct =>
      let literal : Option Std.Net.IPAddr :=
        match origin.host with
        | .ipv4 ip => some (.v4 ip)
        | .ipv6 ip => some (.v6 ip)
        | .name _ => none
      (toString origin.host, origin.port, literal)
    | .http proxyHost proxyPort => (proxyHost, proxyPort, none)

  -- An IP literal is dialled as it stands: the resolver rejects the bracketed form an IPv6 host
  -- takes in a URI.
  let addrs ← match literal with
    | some ip => pure #[ip]
    | none =>
      try DNS.getAddrInfo connectHost (toString connectPort)
      catch err => return .error (.connect (toString err))

  -- The resolver can return an address once per socket type.
  let addrs := addrs.foldl (fun seen addr => if seen.contains addr then seen else seen.push addr) #[]

  if addrs.isEmpty then
    return .error (.connect s!"could not resolve host: {connectHost.quote}")

  -- Each address gets an equal share of `connectTimeout`, so one that never answers cannot use up
  -- the whole budget before the next is tried.
  let attemptTimeout := Std.Time.Millisecond.Offset.ofNat (config.connectTimeout.val.val.toNat / addrs.size)
  let mut lastErr : Error := .connect s!"could not connect to {connectHost.quote}:{connectPort}"

  for ipAddr in addrs do
    let socketAddr : Std.Net.SocketAddress := match ipAddr with
      | .v4 ip => .v4 ⟨ip, connectPort⟩
      | .v6 ip => .v6 ⟨ip, connectPort⟩
    try
      let socket ← Socket.Client.mk
      let connected ← Async.race (some <$> socket.connect socketAddr) do
        discard <| Selectable.one #[.case (← Selector.sleep attemptTimeout) pure]
        pure none
      match connected with
      | none =>
        lastErr := .connect s!"connecting to {socketAddr} timed out after {attemptTimeout}ms"
      | some () =>
        -- A request's head and body are written separately; with Nagle's algorithm the body would
        -- wait for the peer's delayed ACK of the head.
        socket.noDelay
        return .ok (← Connection.new socket origin config)
    catch err =>
      lastErr := .connect (toString err)

  return .error lastErr

end Std.Http.Client
