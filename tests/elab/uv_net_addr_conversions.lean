import Std.Async
import Std.Net

/-!
Addresses survive the conversions between Lean values and the C socket structures: numeric DNS
results, the addresses and netmasks of the network interfaces, and socket addresses passed to and
returned by the kernel, port included. The values use a different byte in every position, so a
swapped byte or segment shows up.
-/

open Std.Async
open Std.Net

def check (name : String) (cond : Bool) (detail : String := "") : IO Unit :=
  unless cond do
    throw <| IO.userError s!"{name}: {detail}"

def runAsync (x : Async α) : IO α := do
  (← x.toIO).block

-- Numeric hosts are converted without a lookup, so every byte of the result comes from the conversion.
#eval do
  let v6 ← runAsync <| DNS.getAddrInfo "2001:db8:1234:5678:9abc:def0:1357:2468" "80"
  let expected6 := IPAddr.v6 (.ofParts 0x2001 0x0db8 0x1234 0x5678 0x9abc 0xdef0 0x1357 0x2468)
  check "numeric IPv6 host" (v6.contains expected6) s!"{v6.toList}"

  let v4 ← runAsync <| DNS.getAddrInfo "192.0.2.123" "80"
  check "numeric IPv4 host" (v4.contains (IPAddr.v4 (.ofParts 192 0 2 123))) s!"{v4.toList}"

-- The loopback interface reports its address with the matching netmask.
#eval do
  let ifaces : Array InterfaceAddress ← interfaceAddresses
  let summary := ifaces.toList.map fun (i : InterfaceAddress) => s!"{i.name} {i.address}/{i.netMask}"
  check "IPv4 loopback"
    (ifaces.any fun (i : InterfaceAddress) => i.address == IPAddr.v4 (.ofParts 127 0 0 1) && i.netMask == IPAddr.v4 (.ofParts 255 0 0 0) && i.isLoopback)
    s!"{summary}"
  for i in ifaces do
    if i.address == IPAddr.v6 (.ofParts 0 0 0 0 0 0 0 1) then
      let allOnes := IPAddr.v6 (.ofParts 0xffff 0xffff 0xffff 0xffff 0xffff 0xffff 0xffff 0xffff)
      check "IPv6 loopback netmask" (i.netMask == allOnes) s!"{summary}"

-- A socket address goes to the kernel on `bind` and `send`, and comes back from `getSockName` and as the
-- source of a received datagram.
def roundTrip (loopback : IPAddr) (mkAddr : UInt16 → SocketAddress) : IO Unit := do
  let receiver ← UDP.Socket.mk
  try receiver.bind (mkAddr 0) catch _ =>
    -- The host has no address of this family (for example, IPv6 disabled in a container).
    return
  let receiverAddr ← receiver.getSockName
  check "bound address" (receiverAddr.ipAddr == loopback && receiverAddr.port != 0) s!"{receiverAddr}"

  let sender ← UDP.Socket.mk
  sender.bind (mkAddr 0)
  let senderAddr ← sender.getSockName

  runAsync <| sender.send "ping".toUTF8 (some receiverAddr)
  let (data, source) ← runAsync <| receiver.recv 64
  check "datagram" (data == "ping".toUTF8)
  check "source address" (source == some senderAddr) s!"{source}, expected {senderAddr}"

#eval roundTrip (.v4 (.ofParts 127 0 0 1)) fun port => .v4 ⟨.ofParts 127 0 0 1, port⟩
#eval roundTrip (.v6 (.ofParts 0 0 0 0 0 0 0 1)) fun port => .v6 ⟨.ofParts 0 0 0 0 0 0 0 1, port⟩
