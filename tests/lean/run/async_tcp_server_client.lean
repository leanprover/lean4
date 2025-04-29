import Std.Internal.Async
import Std.Internal.UV
import Std.Net.Addr

open Std.Internal.IO.Async
open Std.Net

-- Using this function to create IO Error. For some reason the assert! is not pausing the execution.
def assertBEq [BEq α] [ToString α] (actual expected : α) : IO Unit := do
  unless actual == expected do
    throw <| IO.userError <|
      s!"expected '{expected}', got '{actual}'"

-- Define the Async monad
structure Async (α : Type) where
  run : IO (AsyncTask α)

namespace Async

-- Monad instance for Async
instance : Monad Async where
  pure x := Async.mk (pure (AsyncTask.pure x))
  bind ma f := Async.mk do
    let task ← ma.run
    task.bindIO fun a => (f a).run

-- Await function to simplify AsyncTask handling
def await (task : IO (AsyncTask α)) : Async α :=
  Async.mk task

instance : MonadLift IO Async where
  monadLift io := Async.mk (io >>= (pure ∘ AsyncTask.pure))

--------------------------------------------------------------

/-- Mike is another client. -/
def runMike (client: TCP.Socket.Client) : Async Unit := do
  let mes ← await (client.recv? 1024)
  assertBEq (String.fromUTF8? =<< mes) (some "hi mike!! :)")
  await (client.send (String.toUTF8 "hello robert!!"))
  await (client.shutdown)

/-- Joe is another client. -/
def runJoe (client: TCP.Socket.Client) : Async Unit := do
  let mes ← await (client.recv? 1024)
  assertBEq (String.fromUTF8? =<< mes) (some "hi joe! :)")
  await (client.send (String.toUTF8 "hello robert!"))
  await client.shutdown

/-- Robert is the server. -/
def runRobert (server: TCP.Socket.Server) : Async Unit := do
  let joe ← await server.accept
  let mike ← await server.accept

  await (joe.send (String.toUTF8 "hi joe! :)"))
  let mes ← await (joe.recv? 1024)
  assertBEq (String.fromUTF8? =<< mes) (some "hello robert!")

  await (mike.send (String.toUTF8 "hi mike!! :)"))
  let mes ← await (mike.recv? 1024)
  assertBEq (String.fromUTF8? =<< mes) (some "hello robert!!")

  pure ()

def clientServer (addr : SocketAddress) : IO Unit := do
  let server ← TCP.Socket.Server.mk
  server.bind addr
  server.listen 128

  let serverTask := runRobert server

  let serverTask ← serverTask.run

  assertBEq (← server.getSockName).port addr.port

  let joe ← TCP.Socket.Client.mk
  let task ← joe.connect addr
  task.block

  assertBEq (← joe.getPeerName).port addr.port

  joe.noDelay

  let mike ← TCP.Socket.Client.mk
  let task ← mike.connect addr
  task.block

  assertBEq (← mike.getPeerName).port addr.port

  mike.noDelay

  let joeTask := runJoe joe
  let mikeTask := runMike mike

  let joeTask ← joeTask.run
  let mikeTask ← mikeTask.run

  serverTask.block
  joeTask.block
  mikeTask.block

#eval clientServer (SocketAddressV4.mk (.ofParts 127 0 0 1) 8084)
#eval clientServer (SocketAddressV6.mk (.ofParts 0 0 0 0 0 0 0 1) 9000)
