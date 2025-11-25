/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Init.System.Promise
public import Std.Net

public section

namespace Std
namespace Internal
namespace UV
namespace UDP

open Std.Net

private opaque SocketImpl : NonemptyType.{0}

/--
Represents a UDP socket.
-/
def Socket : Type := SocketImpl.type

instance : Nonempty Socket := by exact SocketImpl.property

namespace Socket

/--
Creates a new UDP socket.
-/
@[extern "lean_uv_udp_new"]
opaque new : IO Socket

/--
Binds an UDP socket to a specific address. Address reuse is enabled to allow rebinding the
same address.
-/
@[extern "lean_uv_udp_bind"]
opaque bind (socket : @& Socket) (addr : @& SocketAddress) : IO Unit

/--
Associates the UDP socket with the given address and port, so every message sent by this socket is
automatically sent to that destination.
-/
@[extern "lean_uv_udp_connect"]
opaque connect (socket : @& Socket) (addr : @& SocketAddress) : IO Unit

/--
Sends data through an UDP socket. The `addr` parameter specifies the destination address. If `addr`
is `none`, the data is sent to the default peer address set by `connect`.
-/
@[extern "lean_uv_udp_send"]
opaque send (socket : @& Socket) (data : Array ByteArray) (addr : @& Option SocketAddress) : IO (IO.Promise (Except IO.Error Unit))

/--
Receives data from an UDP socket. `size` is for the maximum bytes to receive. The promise
resolves when some data is available or an error occurs.
Furthermore calling this function in parallel with `waitReadable` is not supported.
-/
@[extern "lean_uv_udp_recv"]
opaque recv (socket : @& Socket) (size : UInt64) : IO (IO.Promise (Except IO.Error (ByteArray × Option SocketAddress)))

/--
Returns an `IO.Promise` that resolves once `socket` has data available for reading. Calling this
function twice on the same `Socket` or in parallel with `recv` is not supported.
-/
@[extern "lean_uv_udp_wait_readable"]
opaque waitReadable (socket : @& Socket) : IO (IO.Promise (Except IO.Error Unit))

/--
Cancels a receive operation in the form of `recv` or `waitReadable` if there is currently one
pending. This resolves their returned `IO.Promise` to `none`. This function is considered dangerous,
as improper use can cause data loss, and is therefore not exposed to the top-level API.
Note that this function is idempotent and as such can be called multiple times on the same socket
without causing errors, in particular also without a receive running in the first place.
-/
@[extern "lean_uv_udp_cancel_recv"]
opaque cancelRecv (socket : @& Socket) : IO Unit

/--
Receives data from an UDP socket. `size` is for the maximum bytes to receive. The promise resolves
when some data is available or an error occurs. If the socket has not been previously bound with `bind`,
it is automatically bound to `0.0.0.0` (all interfaces) with a random port.
-/
@[extern "lean_uv_udp_getpeername"]
opaque getPeerName (socket : @& Socket) : IO SocketAddress

/--
Gets the local address of a bound UDP socket.
-/
@[extern "lean_uv_udp_getsockname"]
opaque getSockName (socket : @& Socket) : IO SocketAddress

/--
Enables or disables broadcasting on a UDP socket.
-/
@[extern "lean_uv_udp_set_broadcast"]
opaque setBroadcast (socket : @& Socket) (on : Bool) : IO Unit

/--
Enables or disables multicast loopback for a UDP socket.
-/
@[extern "lean_uv_udp_set_multicast_loop"]
opaque setMulticastLoop (socket : @& Socket) (on : Bool) : IO Unit

/--
Sets the time-to-live (TTL) value for multicast packets.
-/
@[extern "lean_uv_udp_set_multicast_ttl"]
opaque setMulticastTTL (socket : @& Socket) (ttl : UInt32) : IO Unit

/--
Sets the membership for joining or leaving a multicast group. If `interfaceAddr` is `none`, the
default network interface is used.
-/
@[extern "lean_uv_udp_set_membership"]
opaque setMembership (socket : @& Socket) (multicastAddr : @& IPAddr) (interfaceAddr : @& Option IPAddr) (membership : UInt8) : IO Unit

/--
Sets the multicast interface for sending packets.
-/
@[extern "lean_uv_udp_set_multicast_interface"]
opaque setMulticastInterface (socket : @& Socket) (interfaceAddr : @& IPAddr) : IO Unit

/--
Sets the TTL value for outgoing packets.
-/
@[extern "lean_uv_udp_set_ttl"]
opaque setTTL (socket : @& Socket) (ttl : UInt32) : IO Unit

end Socket
end UDP
end UV
end Internal
end Std
