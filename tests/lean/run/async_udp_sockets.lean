import Std.Internal.Async
import Std.Internal.UV
import Std.Net.Addr

open Std.Internal.IO.Async.UDP
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
def runJoe (addr : UInt16 → SocketAddress) : Async Unit := do
  let client ← UDP.Socket.mk

  client.bind (addr 8081)
  client.connect (addr 8080)

  await (client.send (String.toUTF8 "hello robert!"))


def acceptClose (addr : UInt16 → SocketAddress) : IO Unit := do

  let server ← UDP.Socket.mk
  server.bind (addr 8080)

  let res ← (runJoe addr).run
  res.block

  let res ← server.recv 1024
  let (msg, addr) ← res.block

  assert! ("hello robert!" == String.fromUTF8! msg)
  assert! addr.port == 8081

#eval acceptClose (SocketAddress.v4 ∘ SocketAddressV4.mk (.ofParts 0 0 0 0))
#eval acceptClose (SocketAddress.v6 ∘ SocketAddressV6.mk (.ofParts 0 0 0 0 0 0 0 1))
