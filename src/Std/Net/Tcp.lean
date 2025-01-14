/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Init.Data.SInt
import Std.Net.Addr
import Init.System

namespace Std
namespace Net

private opaque TcpSocketImpl : NonemptyType.{0}

/--
Represents a TCP socket.
-/
def TcpSocket : Type := TcpSocketImpl.type

instance : Nonempty TcpSocket := TcpSocketImpl.property

namespace TcpSocket

/--
Create a new TCP socket.
-/
@[extern "lean_uv_tcp_new"]
opaque new : IO TcpSocket

/--
Connect a TCP socket to the specified address.
-/
@[extern "lean_uv_tcp_connect"]
opaque connect (socket : TcpSocket) (addr : SocketAddress) : IO (IO.Promise (Except IO.Error Unit))

/--
Send data through a TCP socket.
-/
@[extern "lean_uv_tcp_send"]
opaque send (socket : TcpSocket) (data : ByteArray) : IO (IO.Promise (Except IO.Error Unit))

/--
Receive data from a TCP socket.
-/
@[extern "lean_uv_tcp_recv"]
opaque recv (socket : TcpSocket) : IO (IO.Promise (Except IO.Error ByteArray))

/--
Bind a TCP socket to a specific address.
-/
@[extern "lean_uv_tcp_bind"]
opaque bind (socket : TcpSocket) (addr : SocketAddress) : IO Unit

/--
Start listening for incoming connections on a TCP socket.
-/
@[extern "lean_uv_tcp_listen"]
opaque listen (socket : TcpSocket) (backlog : Int32) : IO Unit

/--
Accept an incoming connection on a listening TCP socket.
-/
@[extern "lean_uv_tcp_accept"]
opaque accept (socket : TcpSocket) : IO (IO.Promise (Except IO.Error TcpSocket))

/--
Get the remote address of a connected TCP socket.
-/
@[extern "lean_uv_tcp_getpeername"]
opaque getpeername (socket : TcpSocket) : IO SockAddr

/--
Get the local address of a bound TCP socket.
-/
@[extern "lean_uv_tcp_getsockname"]
opaque getsockname (socket : TcpSocket) : IO SockAddr

/--
Enable or disable the Nagle algorithm for a TCP socket.
-/
@[extern "lean_uv_tcp_nodelay"]
opaque nodelay (socket : TcpSocket) : IO Unit

/--
Enable or disable TCP keep-alive for a socket.
-/
@[extern "lean_uv_tcp_keepalive"]
opaque keepalive (socket : TcpSocket) (enable : Int32) (delay : UInt32) : IO Unit
