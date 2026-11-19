import Std.Async
import Std.Net.Addr

/-!
A UDP socket bound to port 0 gets a port that no other socket holds, so datagrams sent to it reach
it. With address reuse, Linux could hand out the port of another socket that also reuses addresses,
and that socket then received the datagrams, which made `uv_send_many_buffers.lean` hang.
-/

open Std.Async
open Std.Net

def loopback : SocketAddress := .v4 (SocketAddressV4.mk (.ofParts 127 0 0 1) 0)

def port : SocketAddress → UInt16
  | .v4 a => a.port
  | .v6 a => a.port

-- Each socket is in the ephemeral range of about 28000 ports, so 500 live sockets would share a
-- port about four times on average if the kernel ignored the ones already taken.
#eval show IO Unit from do
  let mut sockets := #[]
  let mut owner : Std.HashMap UInt16 Nat := {}
  for i in [0:500] do
    let socket ← UDP.Socket.mk
    socket.bind loopback
    let p := port (← socket.getSockName)
    if let some j := owner[p]? then
      throw <| IO.userError s!"socket {i} was bound to port {p}, which socket {j} still holds"
    owner := owner.insert p i
    sockets := sockets.push socket
