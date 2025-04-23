import Std.Internal.Async
import Std.Internal.UV
import Std.Net.Addr

open Std.Internal.IO.Async
open Std.Net

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
def runDNS : Async Unit := do
  assertBEq (← await (DNS.getAddrInfo "google.com" "http")).size 2

def runReverseDNS : Async Unit := do
  let result ← await (DNS.getNameInfo (.v4 ⟨.ofParts 8 8 8 8, 53⟩))
  assertBEq result ("dns.google", "domain")

#eval runDNS.run >>= AsyncTask.block
#eval runReverseDNS.run >>= AsyncTask.block
