import Std.Internal.Async
import Std.Internal.UV
import Std.Net.Addr

open Std.Internal.IO Async
open Std.Net

open Std.Net

def assertBEq [BEq α] [ToString α] (actual expected : α) : IO Unit := do
  unless actual == expected do
    throw <| IO.userError <|
      s!"expected '{expected}', got '{actual}'"

def baseSelector (asyncWaiter : AsyncTask α) : Selector α :=
 {
    tryFn := do
      if ← IO.hasFinished asyncWaiter then
        let result ← IO.ofExcept asyncWaiter.get
        return some result
      else
        return none
    registerFn waiter := do
      discard <| AsyncTask.mapIO (x := asyncWaiter) fun data => do
        let lose := return ()
        let win promise := promise.resolve (.ok data)
        waiter.race lose win
    unregisterFn := pure ()
  }

def race (a : AsyncTask α) (b : AsyncTask β) (map : Except α β → AsyncTask γ) : IO (AsyncTask γ) := do
  Selectable.one #[
    .case (baseSelector a) fun a => return map (.error a),
    .case (baseSelector b) fun b => return map (.ok b),
  ]

def timeout (a : AsyncTask α) (time : Std.Time.Millisecond.Offset) : IO (AsyncTask α) := do
  race (← sleep time) a fun
    | .ok res => Task.pure (.ok res)
    | .error _ => Task.pure (.error (IO.userError "Timeout."))

def runDNS : Async Unit := do
  let infos ← await <| (← timeout (← DNS.getAddrInfo "google.com" "http") 10000)

  unless infos.size > 0 do
    (throw <| IO.userError <| "No DNS results for google.com" : IO _)

def runDNSNoAscii : Async Unit := do
  let infos ← await <| (← timeout (← DNS.getAddrInfo "google.com▸" "http") 10000)

  unless infos.size > 0 do
    (throw <| IO.userError <| "No DNS results for google.com" : IO _)

def runReverseDNS : Async Unit := do
  let result ← await (← DNS.getNameInfo (.v4 ⟨.ofParts 8 8 8 8, 53⟩))
  assertBEq result.service "domain"
  assertBEq result.host "dns.google"

#eval runDNS.toIO >>= AsyncTask.block

/--
error: invalid argument (error code: 22, name is not ASCII)
-/
#guard_msgs in #eval runDNSNoAscii.toIO >>= AsyncTask.block

#eval runReverseDNS.toIO >>= AsyncTask.block
