/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Init.Data.Vector.Basic

/-!
This module contains Lean representations of IP and socket addresses:
- `IPV4Addr`: Representing IPv4 addresses,
  equivalent to [`in_addr`](https://www.man7.org/linux/man-pages/man3/sockaddr.3type.html).
- `SockAddrV4`: Representing a pair of IPv4 address and port,
  equivalent to [`sockaddr_in`](https://www.man7.org/linux/man-pages/man3/sockaddr.3type.html).
- `IPV6Addr`: Representing IPv6 addresses,
  equivalent to [`in6_addr`](https://www.man7.org/linux/man-pages/man3/sockaddr.3type.html)
- `SockAddrV6`: Represeting a pair of IPv6 address and port,
  equivalent to [`sockaddr_in6`](https://www.man7.org/linux/man-pages/man3/sockaddr.3type.html)
- `IPAddr`: Can either be an `IPV4Addr` or an `IPV6Addr`.
- `SockAddr`: Can either be a `SockAddrV4` or `SockAddrV6`,
  equivalent to [`sockaddr`](https://www.man7.org/linux/man-pages/man3/sockaddr.3type.html)
-/

namespace Std
namespace Net

/--
Representation of an IPv4 address.
-/
structure IPV4Addr where
  /--
  This structure represents the address: `octets[0].octets[1].octets[2].octets[3]`.
  -/
  octets : Vector UInt8 4
  deriving Inhabited, DecidableEq

/--
The Lean equivalent of [`sockaddr_in`](https://man7.org/linux/man-pages/man3/sockaddr.3type.html).
-/
structure SockAddrV4 where
  addr : IPV4Addr
  port : UInt16
  deriving Inhabited, DecidableEq

/--
Representation of an IPv6 address.
-/
structure IPV6Addr where
  /--
  This structure represents the address: `segments[0]:segments[1]:...`.
  -/
  segments : Vector UInt16 8
  deriving Inhabited, DecidableEq

/--
The Lean equivalent of [`sockaddr_in6`](https://man7.org/linux/man-pages/man3/sockaddr.3type.html).
-/
structure SockAddrV6 where
  addr : IPV6Addr
  port : UInt16
  deriving Inhabited, DecidableEq

/--
An IP address, either IPv4 or IPv6.
-/
inductive IPAddr where
  | v4 (addr : IPV4Addr)
  | v6 (addr : IPV6Addr)
  deriving Inhabited, DecidableEq

/--
The Lean equivalent of [`sockaddr`](https://man7.org/linux/man-pages/man3/sockaddr.3type.html),
limited to only IPv4 or IPv6.
-/
inductive SockAddr where
  | v4 (addr : SockAddrV4)
  | v6 (addr : SockAddrV6)
  deriving Inhabited, DecidableEq

/--
The Lean equivalent of [`sa_family_t`](https://man7.org/linux/man-pages/man3/sockaddr.3type.html),
limited to only IPv4 or IPv6.
-/
inductive AddressFamily where
  /--
  The Lean equivalent of `AF_INET` for IPv4 addresses.
  -/
  | inet
  /--
  The Lean equivalent of `AF_INET6` for IPv6 addresses.
  -/
  | inet6
  deriving Inhabited, DecidableEq

namespace IPV4Addr

/--
Build the IPv4 address `a.b.c.d`.
-/
def ofParts (a b c d : UInt8) : IPV4Addr :=
  { octets := #v[a, b, c, d]}

/--
Try to parse `s` as an IPv4 address, returning `none` on failure.
-/
@[extern "lean_uv_pton_v4"]
opaque ofString (s : @&String) : Option IPV4Addr

/--
Turn `addr` into a `String` in the usual IPv4 format.
-/
@[extern "lean_uv_ntop_v4"]
opaque toString (addr : @&IPV4Addr) : String

instance : ToString IPV4Addr where
  toString := toString

instance : Coe IPV4Addr IPAddr where
  coe addr := .v4 addr

end IPV4Addr

namespace SockAddrV4

instance : Coe SockAddrV4 SockAddr where
  coe addr := .v4 addr

end SockAddrV4

namespace IPV6Addr

/--
Build the IPv6 address `a:b:c:d:e:f:g:h`.
-/
def ofParts (a b c d e f g h : UInt16) : IPV6Addr :=
  { segments := #v[a, b, c, d, e, f, g, h]}

/--
Try to parse `s` as an IPv6 address, returning `none` on failure.
-/
@[extern "lean_uv_pton_v6"]
opaque ofString (s : @&String) : Option IPV6Addr

/--
Turn `addr` into a `String` in the usual IPv6 format.
-/
@[extern "lean_uv_ntop_v6"]
opaque toString (addr : @&IPV6Addr) : String

instance : ToString IPV6Addr where
  toString := toString

instance : Coe IPV6Addr IPAddr where
  coe addr := .v6 addr

end IPV6Addr

namespace SockAddrV6

instance : Coe SockAddrV6 SockAddr where
  coe addr := .v6 addr

end SockAddrV6

namespace IPAddr

/--
Obtain the `AddressFamily` associated with an `IPAddr`.
-/
def family : IPAddr → AddressFamily
  | .v4 .. => .inet
  | .v6 .. => .inet6

def toString : IPAddr → String
  | .v4 addr => addr.toString
  | .v6 addr => addr.toString

instance : ToString IPAddr where
  toString := toString

end IPAddr

namespace SockAddr

/--
Obtain the `AddressFamily` associated with a `SockAddr`.
-/
def family : SockAddr → AddressFamily
  | .v4 .. => .inet
  | .v6 .. => .inet6

/--
Obtain the `IPAddr` contained in a `SockAddr`.
-/
def ipAddr : SockAddr → IPAddr
  | .v4 sockaddr  => .v4 sockaddr.addr
  | .v6 sockaddr  => .v6 sockaddr.addr

/--
Obtain the port contained in a `SockAddr`.
-/
def port : SockAddr → UInt16
  | .v4 sockaddr | .v6 sockaddr => sockaddr.port

end SockAddr

end Net
end Std
