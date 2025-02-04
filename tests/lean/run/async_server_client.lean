import Std.Internal.Async
import Std.Internal.UV
import Std.Net.Addr

open Std.Internal.IO.Async
open Std.Net

/-- Mike is another client. -/
def runMike (client: Tcp.Socket) : IO (AsyncTask Unit) := do
  client.recv 1024 >>= fun task => task.bindIO fun mes =>
  assert! String.fromUTF8! mes == "hi mike!! :)"
  client.send (String.toUTF8 "hello robert!!") >>= fun task => task.bindIO fun _ =>
  client.shutdown

/-- Joe is another client. -/
def runJoe (client: Tcp.Socket) : IO (AsyncTask Unit) := do
  client.recv 1024 >>= fun task => task.bindIO fun mes =>
  assert! String.fromUTF8! mes == "hi joe! :)"
  client.send (String.toUTF8 "hello robert!") >>= fun task => task.bindIO fun _ =>
  client.shutdown

/-- Robert is the server. -/
def runRobert (server: Tcp.Socket) : IO (AsyncTask Unit) := do
  let joeClientTask ← server.accept
  let mikeClientTask ← server.accept

  joeClientTask |>.bindIO fun joe =>
  mikeClientTask |>.bindIO fun mike =>

  joe.send (String.toUTF8 "hi joe! :)") >>= fun task => task.bindIO fun _ =>
  joe.recv 1024 >>= fun task => task.bindIO fun mes =>
  assert! String.fromUTF8! mes == "hello robert!"

  mike.send (String.toUTF8 "hi mike!! :)") >>= fun task => task.bindIO fun _ =>
  mike.recv 1024 >>= fun task => task.bindIO fun mes =>
  assert! String.fromUTF8! mes == "hello robert!!"

  pure (AsyncTask.pure ())

def clientServer : IO Unit := do
  let addr := SocketAddressV4.mk (.ofParts 127 0 0 1) 8080

  let server ← Tcp.Socket.mk
  server.bind addr
  server.listen 128

  assert! (← server.getSockName).port == 8080

  let joe ← Tcp.Socket.mk
  let task ← joe.connect addr
  task.block

  assert! (← joe.getPeerName).port == 8080

  joe.noDelay

  let mike ← Tcp.Socket.mk
  let task ← mike.connect addr
  task.block

  assert! (← mike.getPeerName).port == 8080

  mike.noDelay

  let serverTask ← runRobert server

  discard <| runJoe joe
  discard <| runMike mike
  serverTask.block

#eval clientServer
