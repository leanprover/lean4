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
Asynchronously resolves a hostname and service to a list of socket addresses.
-/
@[inline]
def getAddrInfo (host : String) (service : String) : IO (AsyncTask (Array SocketAddress)) :=
  AsyncTask.ofPromise <$> UV.DNS.getAddrInfo host service

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
