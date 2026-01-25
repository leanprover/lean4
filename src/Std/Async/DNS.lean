/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Time
public import Std.Internal.UV
public import Std.Async.Basic

public section

namespace Std.Async.DNS

open Std.Net Internal UV

/--
Represents a resolved hostname and service name from a socket address.
-/
structure NameInfo where
  /--
  The resolved hostname (e.g., "example.com").
  -/
  host : String

  /--
  The service name (e.g., "http" for port 80).
  -/
  service : String

/--
Asynchronously resolves a hostname and service to an array of socket addresses.
-/
@[inline]
def getAddrInfo (host : String) (service : String) (addrFamily : Option AddressFamily := none) : Async (Array IPAddr) := do
  Async.ofIOPromise <| UV.DNS.getAddrInfo
    host
    service
    (match addrFamily with
    | none => 0
    | some .ipv4 => 1
    | some .ipv6 => 2)

/--
Performs a reverse DNS lookup on a `SocketAddress`.
-/
@[inline]
def getNameInfo (host : @& SocketAddress) : Async NameInfo :=
  UV.DNS.getNameInfo host
  |> Async.ofIOPromise
  |>.map (Function.uncurry NameInfo.mk)

end Std.Async.DNS
