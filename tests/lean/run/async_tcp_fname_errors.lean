import Std.Internal.Async
import Std.Internal.UV
import Std.Net.Addr

open Std.Internal.IO Async
open Std.Net

def assertBEq [BEq α] [ToString α] (actual expected : α) : IO Unit := do
  unless actual == expected do
    throw <| IO.userError <|
      s!"expected '{expected}', got '{actual}'"

/-- Mike is another client. -/
def runMike (client: TCP.Socket.Client) : Async Unit := do
  let message ← client.recv? 1024
  assertBEq (String.fromUTF8? =<< message) none

/-- Joe is another client. -/
def runJoe (client: TCP.Socket.Client) : Async Unit := do
  let message ← client.recv? 1024
  assertBEq (String.fromUTF8? =<< message) none

/-- Robert is the server. -/
def runRobert (server: TCP.Socket.Server) : Async Unit := do
  discard <| server.accept
  discard <| server.accept

def clientServer : IO Unit := do
  let addr := SocketAddressV4.mk (.ofParts 127 0 0 1) 8083

  let server ← TCP.Socket.Server.mk
  server.bind addr
  server.listen 128

  assertBEq (← server.getSockName).port 8083

  let joe ← TCP.Socket.Client.mk
  let task ← joe.connect addr |>.toBaseIO
  task.block

  assertBEq (← joe.getPeerName).port 8083

  joe.noDelay

  let mike ← TCP.Socket.Client.mk
  let task ← mike.connect addr |>.toBaseIO
  task.block

  assertBEq (← mike.getPeerName).port 8083

  mike.noDelay

  let serverTask ← (runRobert server).toIO

  let joeTask ← (runJoe joe).toIO
  let mikeTask ← (runMike mike).toIO

  serverTask.block

  joeTask.block
  mikeTask.block

#eval clientServer
