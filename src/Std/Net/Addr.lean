/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Init.System.IO
import Init.Data.Vector.Basic

/-!
This module contains Lean representations of IP and socket addresses:
- `IPv4Addr`: Representing IPv4 addresses.
- `SocketAddressV4`: Representing a pair of IPv4 address and port.
- `IPv6Addr`: Representing IPv6 addresses.
- `SocketAddressV6`: Representing a pair of IPv6 address and port.
- `IPAddr`: Can either be an `IPv4Addr` or an `IPv6Addr`.
- `SocketAddress`: Can either be a `SocketAddressV4` or `SocketAddressV6`.
-/

namespace Std
namespace Net

/--
Representation of a MAC address.
-/
structure MACAddr where
  /--
  This structure represents the address: `octets[0]:octets[1]:octets[2]:octets[3]:octets[4]:octets[5]`.
  -/
  octets : Vector UInt8 6
  deriving Inhabited, DecidableEq

/--
Representation of an IPv4 address.
-/
structure IPv4Addr where
  /--
  This structure represents the address: `octets[0].octets[1].octets[2].octets[3]`.
  -/
  octets : Vector UInt8 4
  deriving Inhabited, DecidableEq

/--
A pair of an `IPv4Addr` and a port.
-/
structure SocketAddressV4 where
  addr : IPv4Addr
  port : UInt16
  deriving Inhabited, DecidableEq

/--
Representation of an IPv6 address.
-/
structure IPv6Addr where
  /--
  This structure represents the address: `segments[0]:segments[1]:...`.
  -/
  segments : Vector UInt16 8
  deriving Inhabited, DecidableEq

/--
A pair of an `IPv6Addr` and a port.
-/
structure SocketAddressV6 where
  addr : IPv6Addr
  port : UInt16
  deriving Inhabited, DecidableEq

/--
An IP address, either IPv4 or IPv6.
-/
inductive IPAddr where
  | v4 (addr : IPv4Addr)
  | v6 (addr : IPv6Addr)
  deriving Inhabited, DecidableEq

/--
Either a `SocketAddressV4` or `SocketAddressV6`.
-/
inductive SocketAddress where
  | v4 (addr : SocketAddressV4)
  | v6 (addr : SocketAddressV6)
  deriving Inhabited, DecidableEq

/--
The kinds of address families supported by Lean, currently only IP variants.
-/
inductive AddressFamily where
  | ipv4
  | ipv6
  deriving Inhabited, DecidableEq

namespace IPv4Addr

/--
Build the IPv4 address `a.b.c.d`.
-/
def ofParts (a b c d : UInt8) : IPv4Addr :=
  { octets := #v[a, b, c, d] }

/--
Try to parse `s` as an IPv4 address, returning `none` on failure.
-/
@[extern "lean_uv_pton_v4"]
opaque ofString (s : @&String) : Option IPv4Addr

/--
Turn `addr` into a `String` in the usual IPv4 format.
-/
@[extern "lean_uv_ntop_v4"]
opaque toString (addr : @&IPv4Addr) : String

instance : ToString IPv4Addr where
  toString := toString

instance : Coe IPv4Addr IPAddr where
  coe addr := .v4 addr

end IPv4Addr

namespace SocketAddressV4

instance : Coe SocketAddressV4 SocketAddress where
  coe addr := .v4 addr

end SocketAddressV4

namespace IPv6Addr

/--
Build the IPv6 address `a:b:c:d:e:f:g:h`.
-/
def ofParts (a b c d e f g h : UInt16) : IPv6Addr :=
  { segments := #v[a, b, c, d, e, f, g, h] }

/--
Try to parse `s` as an IPv6 address according to
[RFC 2373](https://datatracker.ietf.org/doc/html/rfc2373), returning `none` on failure.
-/
@[extern "lean_uv_pton_v6"]
opaque ofString (s : @&String) : Option IPv6Addr

/--
Turn `addr` into a `String` in the IPv6 format described in
[RFC 2373](https://datatracker.ietf.org/doc/html/rfc2373).
-/
@[extern "lean_uv_ntop_v6"]
opaque toString (addr : @&IPv6Addr) : String

instance : ToString IPv6Addr where
  toString := toString

instance : Coe IPv6Addr IPAddr where
  coe addr := .v6 addr

end IPv6Addr

namespace SocketAddressV6

instance : Coe SocketAddressV6 SocketAddress where
  coe addr := .v6 addr

end SocketAddressV6

namespace IPAddr

/--
Obtain the `AddressFamily` associated with an `IPAddr`.
-/
def family : IPAddr → AddressFamily
  | .v4 .. => .ipv4
  | .v6 .. => .ipv6

def toString : IPAddr → String
  | .v4 addr => addr.toString
  | .v6 addr => addr.toString

instance : ToString IPAddr where
  toString := toString

end IPAddr

namespace SocketAddress

/--
Obtain the `AddressFamily` associated with a `SocketAddress`.
-/
def family : SocketAddress → AddressFamily
  | .v4 .. => .ipv4
  | .v6 .. => .ipv6

/--
Obtain the `IPAddr` contained in a `SocketAddress`.
-/
def ipAddr : SocketAddress → IPAddr
  | .v4 sa  => .v4 sa.addr
  | .v6 sa  => .v6 sa.addr

/--
Obtain the port contained in a `SocketAddress`.
-/
def port : SocketAddress → UInt16
  | .v4 sa | .v6 sa => sa.port

end SocketAddress

/--
Represents an interface address, including details such as the interface name,
whether it is internal, the associated address, and the network mask.
-/
structure InterfaceAddress where
  /--
  The name of the network interface.
  -/
  name : String

  /-
  The physical (MAC) address of the interface.
  -/
  physicalAddress : MACAddr

  /--
  Indicates whether the interface is a loopback interface.
  -/
  isLoopback : Bool

  /--
  The IP address assigned to the interface.
  -/
  address : IPAddr

  /--
  The subnet mask associated with the interface.
  -/
  netMask : IPAddr
  deriving Inhabited, DecidableEq

/--
Gets address information about the network interfaces on the system, including disabled ones and
multiple addresses for each interface.
-/
@[extern "lean_uv_interface_addresses"]
opaque interfaceAddresses : IO (Array InterfaceAddress)

end Net
end Std
