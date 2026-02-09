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

/-- Joe is another client. -/
def runJoe (addr: SocketAddress) : Async Unit := do
  let client ← TCP.Socket.Client.mk

  client.connect addr
  client.send (String.toUTF8 "hello robert!")
  client.shutdown

def listenClose : IO Unit := do
  let addr := SocketAddressV4.mk (.ofParts 127 0 0 1) 8080

  let server ← TCP.Socket.Server.mk
  server.bind addr
  server.listen 128

def acceptClose : IO Unit := do
  let addr := SocketAddressV4.mk (.ofParts 127 0 0 1) 8081

  let server ← TCP.Socket.Server.mk
  server.bind addr
  server.listen 128

  let joeTask ← (runJoe addr).toIO

  let task ← server.accept |>.toBaseIO
  let client ← task.block

  let mes ← client.recv? 1024 |>.toBaseIO
  let msg ← mes.block

  assertBEq (String.fromUTF8? =<< msg) ("hello robert!")

  let mes ← client.recv? 1024 |>.toBaseIO
  let msg ← mes.block

  assertBEq (String.fromUTF8? =<< msg) none

  -- Waiting to avoid errors from escaping.
  joeTask.block

#eval listenClose
