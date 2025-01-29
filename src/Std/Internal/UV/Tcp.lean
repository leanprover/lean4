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
namespace Tcp

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
Connect a TCP socket to the specified address.
-/
@[extern "lean_uv_tcp_connect"]
opaque connect (socket : @& Socket) (addr : SocketAddress) : IO (IO.Promise (Except IO.Error Unit))

/--
Send data through a TCP socket.
-/
@[extern "lean_uv_tcp_send"]
opaque send (socket : @& Socket) (data : ByteArray) : IO (IO.Promise (Except IO.Error Unit))

/--
Receive data from a TCP socket.
-/
@[extern "lean_uv_tcp_recv"]
opaque recv (socket : @& Socket) : IO (IO.Promise (Except IO.Error ByteArray))

/--
Bind a TCP socket to a specific address.
-/
@[extern "lean_uv_tcp_bind"]
opaque bind (socket : @& Socket) (addr : SocketAddress) : IO Unit

/--
Start listening for incoming connections on a TCP socket.
-/
@[extern "lean_uv_tcp_listen"]
opaque listen (socket : @& Socket) (backlog : Int32) : IO Unit

/--
Accept an incoming connection on a listening TCP socket.
-/
@[extern "lean_uv_tcp_accept"]
opaque accept (socket : @& Socket) : IO (IO.Promise (Except IO.Error Socket))

/--
Accept an incoming connection on a listening TCP socket.
-/
@[extern "lean_uv_tcp_shutdown"]
opaque shutdown (socket : @& Socket) : IO (IO.Promise (Except IO.Error Unit))

/--
Get the remote address of a connected TCP socket.
-/
@[extern "lean_uv_tcp_getpeername"]
opaque getpeername (socket : @& Socket) : IO SocketAddress

/--
Get the local address of a bound TCP socket.
-/
@[extern "lean_uv_tcp_getsockname"]
opaque getsockname (socket : @& Socket) : IO SocketAddress

/--
Enable or disable the Nagle algorithm for a TCP socket.
-/
@[extern "lean_uv_tcp_nodelay"]
opaque nodelay (socket : @& Socket) : IO Unit

/--
Enable or disable TCP keep-alive for a socket.
-/
@[extern "lean_uv_tcp_keepalive"]
opaque keepalive (socket : @& Socket) (enable : Int32) (delay : UInt32) : IO Unit

end Socket
end Tcp
end UV
end Internal
end Std
