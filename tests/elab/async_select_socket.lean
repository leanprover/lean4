import Std.Internal.Async.Timer
import Std.Internal.Async.TCP
import Std.Internal.Async.UDP

#exit -- TODO: remove `#exit` after nondet issue is resolved.

open Std Internal IO Async

namespace TCP

def testClient (addr : Net.SocketAddress) : Async String := do
  let client ← TCP.Socket.Client.mk
  client.connect addr

  Selectable.one #[
    .case (← Selector.sleep 1000) fun _ => return "Timeout",
    .case (client.recvSelector 4096) fun data? => do
      if let some data := data? then
        return String.fromUTF8! data
      else
        return "Closed"
  ]

def test (serverFn : TCP.Socket.Server → Async Unit) (addr : Net.SocketAddress) : Async String := do
  let server ← TCP.Socket.Server.mk
  server.bind addr
  server.listen 1
  let serverTask ← async (serverFn server)
  let clientTask ← async (testClient addr)
  await serverTask
  await clientTask

def testServerSend (server : TCP.Socket.Server) : Async Unit := do
  let client ← server.accept
  client.send (String.toUTF8 "Success")

def testServerTimeout (server : TCP.Socket.Server) : Async Unit := do
  let client ← server.accept
  Async.sleep 1500
  client.shutdown

def testServerClose (server : TCP.Socket.Server) : Async Unit := do
  let client ← server.accept
  client.shutdown

/-- info: "Success" -/
#guard_msgs in
#eval test testServerSend (Net.SocketAddressV4.mk (.ofParts 127 0 0 1) 7070) |>.block

/-- info: "Closed" -/
#guard_msgs in
#eval test testServerClose (Net.SocketAddressV4.mk (.ofParts 127 0 0 1) 7071) |>.block

/-- info: "Timeout" -/
#guard_msgs in
#eval test testServerTimeout (Net.SocketAddressV4.mk (.ofParts 127 0 0 1) 7072) |>.block

end TCP

namespace UDP

def testClient (addr : Net.SocketAddress) : Async String := do
  IO.println "sending client"
  let client ← UDP.Socket.mk
  client.connect addr
  client.send "ping".toUTF8

  Selectable.one #[
    .case (← Selector.sleep 1000) fun _ => return "Timeout",
    .case (client.recvSelector 4096) fun (data, _) => do
      return String.fromUTF8! data
  ]

def test (serverFn : UDP.Socket → Async Unit) (addr : Net.SocketAddress) : Async String := do
  let server ← UDP.Socket.mk
  server.bind addr
  let serverTask ← async (serverFn server)
  let clientTask ← async (testClient addr)
  await serverTask
  await clientTask

def testServerSend (server : UDP.Socket) : Async Unit := do
  let (_, client?) ← server.recv 4096
  let client := client?.get!
  server.send (String.toUTF8 "Success") client

def testServerTimeout (server : UDP.Socket) : Async Unit := do
  let (_, client?) ← server.recv 4096
  let client := client?.get!
  Async.sleep 1500
  server.send (String.toUTF8 "Success") client

/--
info: "Success"
-/
#guard_msgs in
#eval test testServerSend (Net.SocketAddressV4.mk (.ofParts 127 0 0 1) 7075) |>.block

/--
info: "Timeout"
-/
#guard_msgs in
#eval test testServerTimeout (Net.SocketAddressV4.mk (.ofParts 127 0 0 1) 7075) |>.block

end UDP
