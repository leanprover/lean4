import Std.Internal.Async
import Std.Internal.UV
import Std.Net.Addr

open Std.Internal.IO.Async.UDP
open Std.Internal.IO.Async
open Std.Net

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
def runJoe (addr : UInt16 → SocketAddress) (first second : UInt16) : Async Unit := do
  let client ← UDP.Socket.mk

  client.bind (addr second)
  client.connect (addr first)

  await (client.send (String.toUTF8 "hello robert!"))


def acceptClose (addr : UInt16 → SocketAddress) (first second : UInt16) : IO Unit := do

  let server ← UDP.Socket.mk
  server.bind (addr first)

  let res ← (runJoe addr first second).run
  res.block

  let res ← server.recv 1024
  let (msg, addr) ← res.block

  if let some addr := addr then
    assertBEq addr.port second

  assertBEq (String.fromUTF8! msg) "hello robert!"

#eval acceptClose (SocketAddress.v4 ∘ SocketAddressV4.mk (.ofParts 127 0 0 1))  9001 9002

#eval acceptClose (SocketAddress.v6 ∘ SocketAddressV6.mk (.ofParts 0 0 0 0 0 0 0 1))  9003 9004
