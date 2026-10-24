import Std.Async
import Std.Net

/-!
Addresses survive the conversions between Lean values and the C socket structures: numeric DNS
results, the addresses and netmasks of the network interfaces, and socket addresses passed to and
returned by the kernel, port included. The values use a different byte in every position, so a
swapped byte or segment shows up. Parsing and printing are each checked against fixed values, so a
byte-order error in either direction fails, even one that a round trip would cancel out.
-/

open Std.Async
open Std.Net

def check (name : String) (cond : Bool) (detail : String := "") : IO Unit :=
  unless cond do
    throw <| IO.userError s!"{name}: {detail}"

def runAsync (x : Async α) : IO α := do
  (← x.toIO).block

-- A wrong address or port sends the datagram elsewhere, which must fail the test rather than hang
-- it.
def recvWithTimeout (s : UDP.Socket) (size : UInt64) : IO (ByteArray × Option SocketAddress) :=
  runAsync do
    let timeout ← Sleep.mk 5000
    Selectable.one #[
      .case (s.recvSelector size) pure,
      .case timeout.selector fun _ => throw <| .userError "recv: timed out"]

/--
Binds `addr`, or returns `false` for an IPv6 address on a host without IPv6 (for example, a
container with IPv6 disabled). Any other failure, such as an IPv4 loopback the kernel does not
recognize, is an error.
-/
def tryBind (bind : SocketAddress → IO Unit) (addr : SocketAddress) : IO Bool := do
  try
    bind addr
    return true
  catch e =>
    match addr, e with
    | .v6 _, .unsupportedOperation .. => return false
    | _, _ => throw e

-- Numeric hosts are converted without a lookup, so every byte of the result comes from the
-- conversion.
#eval do
  let v6 ← runAsync <| DNS.getAddrInfo "2001:db8:1234:5678:9abc:def0:1357:2468" "80"
  let expected6 := IPAddr.v6 (.ofParts 0x2001 0x0db8 0x1234 0x5678 0x9abc 0xdef0 0x1357 0x2468)
  check "numeric IPv6 host" (v6.contains expected6) s!"{v6.toList}"

  let v4 ← runAsync <| DNS.getAddrInfo "192.0.2.123" "80"
  check "numeric IPv4 host" (v4.contains (IPAddr.v4 (.ofParts 192 0 2 123))) s!"{v4.toList}"

-- The loopback interface reports its address with the matching netmask.
#eval do
  let ifaces : Array InterfaceAddress ← interfaceAddresses
  let summary := ifaces.toList.map fun (i : InterfaceAddress) =>
    s!"{i.name} {i.address}/{i.netMask}"
  let isV4Loopback (i : InterfaceAddress) :=
    i.address == IPAddr.v4 (.ofParts 127 0 0 1) && i.netMask == IPAddr.v4 (.ofParts 255 0 0 0) &&
      i.isLoopback
  check "IPv4 loopback" (ifaces.any isV4Loopback) s!"{summary}"
  for i in ifaces do
    if i.address == IPAddr.v6 (.ofParts 0 0 0 0 0 0 0 1) then
      let allOnes := IPAddr.v6 (.ofParts 0xffff 0xffff 0xffff 0xffff 0xffff 0xffff 0xffff 0xffff)
      check "IPv6 loopback netmask" (i.netMask == allOnes) s!"{summary}"

-- A socket address goes to the kernel on `bind` and `send`, and comes back from `getSockName` and
-- as the source of a received datagram.
def roundTrip (loopback : IPAddr) (mkAddr : UInt16 → SocketAddress) : IO Unit := do
  let receiver ← UDP.Socket.mk
  unless ← tryBind receiver.bind (mkAddr 0) do
    return
  let receiverAddr ← receiver.getSockName
  check "bound address" (receiverAddr.ipAddr == loopback && receiverAddr.port != 0)
    s!"{receiverAddr}"

  let sender ← UDP.Socket.mk
  sender.bind (mkAddr 0)
  let senderAddr ← sender.getSockName

  runAsync <| sender.send "ping".toUTF8 (some receiverAddr)
  let (data, source) ← recvWithTimeout receiver 64
  check "datagram" (data == "ping".toUTF8)
  check "source address" (source == some senderAddr) s!"{source}, expected {senderAddr}"

#eval roundTrip (.v4 (.ofParts 127 0 0 1)) fun port => .v4 ⟨.ofParts 127 0 0 1, port⟩
#eval roundTrip (.v6 (.ofParts 0 0 0 0 0 0 0 1)) fun port => .v6 ⟨.ofParts 0 0 0 0 0 0 0 1, port⟩

-- `ofString` converts C to Lean and `toString` converts Lean to C. Each direction is compared to
-- fixed values on its own, since a byte swap applied in both directions cancels out in a round
-- trip.
def checkV6 (text : String) (parts : IPv6Addr) : IO Unit := do
  let some parsed := IPv6Addr.ofString text
    | throw <| IO.userError s!"IPv6 {text}: not parsed"
  check s!"IPv6 {text} parsed" (parsed == parts)
    s!"{parsed.segments.toArray.toList.map UInt16.toNat}"
  check s!"IPv6 {text} printed" (parts.toString == text) parts.toString

def checkV4 (text : String) (parts : IPv4Addr) : IO Unit := do
  let some parsed := IPv4Addr.ofString text
    | throw <| IO.userError s!"IPv4 {text}: not parsed"
  check s!"IPv4 {text} parsed" (parsed == parts) s!"{parsed.octets.toArray.toList}"
  check s!"IPv4 {text} printed" (parts.toString == text) parts.toString

#eval do
  checkV6 "2001:db8:1234:5678:9abc:def0:fedc:ba98"
    (.ofParts 0x2001 0x0db8 0x1234 0x5678 0x9abc 0xdef0 0xfedc 0xba98)
  checkV6 "::1" (.ofParts 0 0 0 0 0 0 0 1)
  checkV6 "fe80::1" (.ofParts 0xfe80 0 0 0 0 0 0 1)
  checkV6 "::ffff:1.2.3.4" (.ofParts 0 0 0 0 0 0xffff 0x0102 0x0304)
  checkV4 "1.2.3.4" (.ofParts 1 2 3 4)
  checkV4 "192.0.2.123" (.ofParts 192 0 2 123)

-- A TCP socket bound to the loopback reports the same address from `getSockName`.
def tcpBound (loopback : IPAddr) (addr : SocketAddress) : IO Unit := do
  let server ← TCP.Socket.Server.mk
  unless ← tryBind server.bind addr do
    return
  let bound ← server.getSockName
  check "TCP bound address" (bound.ipAddr == loopback && bound.port != 0) s!"{bound}"

#eval tcpBound (.v4 (.ofParts 127 0 0 1)) (.v4 ⟨.ofParts 127 0 0 1, 0⟩)
#eval tcpBound (.v6 (.ofParts 0 0 0 0 0 0 0 1)) (.v6 ⟨.ofParts 0 0 0 0 0 0 0 1, 0⟩)
