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

/-- Joe is another client. -/
def runJoe (addr: SocketAddress) : Async Unit := do
  let client ← TCP.Socket.Client.mk

  await (client.connect addr)
  await (client.send (String.toUTF8 "hello robert!"))
  await client.shutdown

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

  let joeTask ← (runJoe addr).run

  let task ← server.accept
  let client ← task.block

  let mes ← client.recv? 1024
  let msg ← mes.block

  assertBEq (String.fromUTF8? =<< msg) ("hello robert!")

  let mes ← client.recv? 1024
  let msg ← mes.block

  assertBEq (String.fromUTF8? =<< msg) none

  -- Waiting to avoid errors from escaping.
  joeTask.block

#eval acceptClose
#eval listenClose
