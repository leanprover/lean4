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
namespace DNS

open Std.Net

/--
Specifies the transport protocol for the DNS search.
-/
inductive Protocol

  /--
  TCP protocol.
  -/
  | tcp

  /--
  UDP protocol.
  -/
  | udp
deriving Repr, DecidableEq

/--
Converts an `AddressFamily` to `UInt8`.
-/
def AddressFamily.toUInt8 : AddressFamily → UInt8
  | .ipv4 => 1
  | .ipv6 => 2

/--
Converts a `Protocol` to `UInt8`.
-/
def Protocol.toUInt8 : Protocol → UInt8
  | .tcp => 0
  | .udp => 1

/--
Asynchronously resolves a hostname and service to an array of socket addresses.Asynchronously resolves a hostname and service to a list of socket addresses.
-/
@[inline]
def getAddrInfo
  (host : String)
  (service : String)
  (protocol : Protocol)
  (addressFamily : Option AddressFamily := none)
  : IO (AsyncTask (Array IPAddr)) :=
    AsyncTask.ofPromise <$> UV.DNS.getAddrInfo host service
      (AddressFamily.toUInt8 <$> addressFamily |>.getD 0)
      protocol.toUInt8

/--
Performs a reverse DNS lookup on a `SocketAddress`.
-/
@[inline]
def getNameInfo (host : @& SocketAddress) : IO (AsyncTask (String × String)) :=
    AsyncTask.ofPromise <$> UV.DNS.getNameInfo host

end DNS
end Async
end IO
end Internal
end Std
