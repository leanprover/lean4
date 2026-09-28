import Std.Async

/-!
Setting a UDP multicast membership or interface with an IPv6 address whose text form is longer than
an IPv4 address must not abort the process. Whether the calls succeed depends on the host's network
configuration, so errors are ignored.
-/

open Std Net Internal.UV

#eval show IO Unit from do
  let socket ← UDP.Socket.new
  try socket.bind (.v6 ⟨.ofParts 0 0 0 0 0 0 0 0, 0⟩) catch _ => return
  let group := IPAddr.v6 (.ofParts 0xff15 0x1234 0x5678 0x9abc 0 0 0 1)
  let iface := IPAddr.v6 (.ofParts 0xfe80 0 0 0 0 0x1234 0x5678 0x9abc)
  try socket.setMembership group none 0 catch _ => pure ()
  try socket.setMembership group (some iface) 0 catch _ => pure ()
  try socket.setMulticastInterface iface catch _ => pure ()
