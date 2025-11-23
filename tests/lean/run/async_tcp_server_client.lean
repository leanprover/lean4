import Std.Internal.Async
import Std.Internal.UV
import Std.Net.Addr

open Std.Internal.IO Async
open Std.Net

-- Using this function to create IO Error. For some reason the assert! is not pausing the execution.
def assertBEq [BEq α] [ToString α] (actual expected : α) : IO Unit := do
  unless actual == expected do
    throw <| IO.userError <|
      s!"expected '{expected}', got '{actual}'"

--------------------------------------------------------------

/-- Mike is another client. -/
def runMike (client: TCP.Socket.Client) : Async Unit := do
  let mes ← client.recv? 1024
  assertBEq (String.fromUTF8? =<< mes) (some "hi mike!! :)")
  client.send (String.toUTF8 "hello robert!!")
  client.shutdown

/-- Joe is another client. -/
def runJoe (client: TCP.Socket.Client) : Async Unit := do
  let mes ← client.recv? 1024
  assertBEq (String.fromUTF8? =<< mes) (some "hi joe! :)")
  client.send (String.toUTF8 "hello robert!")
  client.shutdown

/-- Robert is the server. -/
def runRobert (server: TCP.Socket.Server) : Async Unit := do
  let joe ← server.accept
  let mike ← server.accept

  joe.send (String.toUTF8 "hi joe! :)")
  let mes ← joe.recv? 1024
  assertBEq (String.fromUTF8? =<< mes) (some "hello robert!")

  mike.send (String.toUTF8 "hi mike!! :)")
  let mes ← mike.recv? 1024
  assertBEq (String.fromUTF8? =<< mes) (some "hello robert!!")

  pure ()

def clientServer (addr : SocketAddress) : IO Unit := do
  let server ← TCP.Socket.Server.mk
  server.bind addr
  server.listen 128

  let serverTask := runRobert server

  let serverTask ← serverTask.toIO

  assertBEq (← server.getSockName).port addr.port

  let joe ← TCP.Socket.Client.mk
  let task ← joe.connect addr |>.toBaseIO
  task.block

  assertBEq (← joe.getPeerName).port addr.port

  joe.noDelay

  let mike ← TCP.Socket.Client.mk
  let task ← mike.connect addr |>.toBaseIO
  task.block

  assertBEq (← mike.getPeerName).port addr.port

  mike.noDelay

  let joeTask := runJoe joe
  let mikeTask := runMike mike

  let joeTask ← joeTask.toIO
  let mikeTask ← mikeTask.toIO

  serverTask.block
  joeTask.block
  mikeTask.block

#eval clientServer (SocketAddressV4.mk (.ofParts 127 0 0 1) 8084)
#eval clientServer (SocketAddressV6.mk (.ofParts 0 0 0 0 0 0 0 1) 9000)
