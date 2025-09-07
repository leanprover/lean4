import Std.Internal.Async.Timer
import Std.Internal.Async.TCP
import Std.Internal.Async.UDP

open Std Internal IO Async

namespace TCP

def testClient (addr : Net.SocketAddress) : IO (AsyncTask String) := do
  let client ← TCP.Socket.Client.mk
  (← client.connect addr).bindIO fun _ => do
    Selectable.one #[
      .case (← Selector.sleep 1000) fun _ => return AsyncTask.pure "Timeout",
      .case (← client.recvSelector 4096) fun data? => do
        if let some data := data? then
          return AsyncTask.pure <| String.fromUTF8! data
        else
          return AsyncTask.pure "Closed"
    ]

def test (serverFn : TCP.Socket.Server → IO (AsyncTask Unit)) (addr : Net.SocketAddress) :
    IO Unit := do
  let server ← TCP.Socket.Server.mk
  server.bind addr
  server.listen 1
  let serverTask ← serverFn server
  let clientTask ← testClient addr
  serverTask.block
  IO.println (← clientTask.block)

def testServerSend (server : TCP.Socket.Server) : IO (AsyncTask Unit) := do
  (← server.accept).bindIO fun client => do
    client.send (String.toUTF8 "Success")

def testServerTimeout (server : TCP.Socket.Server) : IO (AsyncTask Unit) := do
  (← server.accept).bindIO fun client => do
    (← Async.sleep 1500).bindIO fun _ => do
      client.shutdown

def testServerClose (server : TCP.Socket.Server) : IO (AsyncTask Unit) := do
  (← server.accept).bindIO fun client => client.shutdown

/-- info: Success -/
#guard_msgs in
#eval test testServerSend (Net.SocketAddressV4.mk (.ofParts 127 0 0 1) 7070)

/-- info: Closed -/
#guard_msgs in
#eval test testServerClose (Net.SocketAddressV4.mk (.ofParts 127 0 0 1) 7071)

/-- info: Timeout -/
#guard_msgs in
#eval test testServerTimeout (Net.SocketAddressV4.mk (.ofParts 127 0 0 1) 7072)

end TCP


namespace UDP

def testClient (addr : Net.SocketAddress) : IO (AsyncTask String) := do
  let client ← UDP.Socket.mk
  client.connect addr
  (← client.send "ping".toUTF8).bindIO fun _ => do
    Selectable.one #[
      .case (← Selector.sleep 1000) fun _ => return AsyncTask.pure "Timeout",
      .case (← client.recvSelector 4096) fun (data, _) => do
        return AsyncTask.pure <| String.fromUTF8! data
    ]

def test (serverFn : UDP.Socket → IO (AsyncTask Unit)) (addr : Net.SocketAddress) : IO Unit := do
  let server ← UDP.Socket.mk
  server.bind addr
  let serverTask ← serverFn server
  let clientTask ← testClient addr
  serverTask.block
  IO.println (← clientTask.block)

def testServerSend (server : UDP.Socket) : IO (AsyncTask Unit) := do
  (← server.recv 4096).bindIO fun (_, client?) => do
    let client := client?.get!
    server.send (String.toUTF8 "Success") client

def testServerTimeout (server : UDP.Socket) : IO (AsyncTask Unit) := do
  (← server.recv 4096).bindIO fun (_, client?) => do
    let client := client?.get!
    (← Async.sleep 1500).bindIO fun _ => do
      server.send (String.toUTF8 "Success") client

/-- info: Success -/
#guard_msgs in
#eval test testServerSend (Net.SocketAddressV4.mk (.ofParts 127 0 0 1) 7070)

/-- info: Timeout -/
#guard_msgs in
#eval test testServerTimeout (Net.SocketAddressV4.mk (.ofParts 127 0 0 1) 7072)

end UDP
