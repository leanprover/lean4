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
Asynchronously resolves a hostname and service to an array of socket addresses.Asynchronously resolves a hostname and service to a list of socket addresses.
-/
@[inline]
def getAddrInfo (host : String) (service : String) (addressFamily : Option AddressFamily := none) :
    IO (AsyncTask (Array IPAddr)) :=
    AsyncTask.ofPromise <$> UV.DNS.getAddrInfo host service
      (match addressFamily with
      | none => 0
      | some .ipv4 => 1
      | some .ipv6 => 2)

/--
Performs a reverse DNS lookup on a `SocketAddress`.
-/
@[inline]
def getNameInfo (host : SocketAddress) : IO (AsyncTask (String × String)) :=
    AsyncTask.ofPromise <$> UV.DNS.getNameInfo host

end DNS
end Async
end IO
end Internal
end Std
