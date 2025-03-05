/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving, Sofia Rodrigues
-/
prelude
import Init.System.IO
import Init.System.Promise
import Std.Net

namespace Std
namespace Internal
namespace UV
namespace TCP

open Std.Net

private opaque SocketImpl : NonemptyType.{0}

/--
Represents a TCP socket.
-/
def Socket : Type := SocketImpl.type

instance : Nonempty Socket := SocketImpl.property

namespace Socket

/--
Creates a new TCP socket.
-/
@[extern "lean_uv_tcp_new"]
opaque new : IO Socket

/--
Connects a TCP socket to the specified address.
-/
@[extern "lean_uv_tcp_connect"]
opaque connect (socket : @& Socket) (addr : SocketAddress) : IO (IO.Promise (Except IO.Error Unit))

/--
Sends data through a TCP socket.
-/
@[extern "lean_uv_tcp_send"]
opaque send (socket : @& Socket) (data : ByteArray) : IO (IO.Promise (Except IO.Error Unit))

/--
Receives data from a TCP socket with a maximum size of size bytes. The promise resolves when data is
available or an error occurs. If data is received, it’s wrapped in .some. If EOF is reached, the
result is .none, indicating no more data is available.
-/
@[extern "lean_uv_tcp_recv"]
opaque recv? (socket : @& Socket) (size : UInt64) : IO (IO.Promise (Except IO.Error (Option ByteArray)))

/--
Binds a TCP socket to a specific address.
-/
@[extern "lean_uv_tcp_bind"]
opaque bind (socket : @& Socket) (addr : SocketAddress) : IO Unit

/--
Starts listening for incoming connections on a TCP socket.
-/
@[extern "lean_uv_tcp_listen"]
opaque listen (socket : @& Socket) (backlog : UInt32) : IO Unit

/--
Accepts an incoming connection on a listening TCP socket.
-/
@[extern "lean_uv_tcp_accept"]
opaque accept (socket : @& Socket) : IO (IO.Promise (Except IO.Error Socket))

/--
Shuts down an incoming connection on a listening TCP socket.
-/
@[extern "lean_uv_tcp_shutdown"]
opaque shutdown (socket : @& Socket) : IO (IO.Promise (Except IO.Error Unit))

/--
Gets the remote address of a connected TCP socket.
-/
@[extern "lean_uv_tcp_getpeername"]
opaque getPeerName (socket : @& Socket) : IO SocketAddress

/--
Gets the local address of a bound TCP socket.
-/
@[extern "lean_uv_tcp_getsockname"]
opaque getSockName (socket : @& Socket) : IO SocketAddress

/--
Enables the Nagle algorithm for a TCP socket.
-/
@[extern "lean_uv_tcp_nodelay"]
opaque noDelay (socket : @& Socket) : IO Unit

/--
Enables TCP keep-alive for a socket. If delay is less than 1 then UV_EINVAL is returned.
-/
@[extern "lean_uv_tcp_keepalive"]
opaque keepAlive (socket : @& Socket) (enable : Int32) (delay : UInt32) : IO Unit

end Socket
end TCP
end UV
end Internal
end Std
