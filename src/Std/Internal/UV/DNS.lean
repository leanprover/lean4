/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Init.System.Promise
public import Init.Data.SInt
public import Std.Net

@[expose] public section

namespace Std
namespace Internal
namespace UV
namespace DNS

open Std.Net

/--
Asynchronously resolves a hostname and service to an array of socket addresses.

If the event loop is torn down (at process exit) while the lookup is still in flight, the promise is
resolved with an `UV_ECANCELED` error. Once the loop is gone this function itself fails with
`UV_ECANCELED` rather than returning a promise.
-/
@[extern "lean_uv_dns_get_info"]
opaque getAddrInfo (host : @& String) (service : @& String) (family : UInt8) :
    IO (IO.Promise (Except IO.Error (Array IPAddr)))

/--
Performs a reverse DNS lookup on a `SocketAddress`.

If the event loop is torn down (at process exit) while the lookup is still in flight, the promise is
resolved with an `UV_ECANCELED` error. Once the loop is gone this function itself fails with
`UV_ECANCELED` rather than returning a promise.
-/
@[extern "lean_uv_dns_get_name"]
opaque getNameInfo (host : @& SocketAddress) : IO (IO.Promise (Except IO.Error (String × String)))

end DNS
end UV
end Internal
end Std
