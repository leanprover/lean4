import Std.Internal.Async
import Std.Internal.UV
import Std.Net.Addr

open Std.Internal.IO.Async
open Std.Net

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
  await client.shutdown

def listenClose : IO Unit := do
  let addr := SocketAddressV4.mk (.ofParts 127 0 0 1) 8080

  let server ← TCP.Socket.Server.mk
  server.bind addr
  server.listen 128

def acceptClose : IO Unit := do
  let addr := SocketAddressV4.mk (.ofParts 127 0 0 1) 8080

  let server ← TCP.Socket.Server.mk
  server.bind addr
  server.listen 128

  let res ← (runJoe addr).run
  res.block

  let res ← server.accept
  discard <| res.block


#eval listenClose
