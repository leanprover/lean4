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

def timeout [Inhabited α] (a : Async α) (time : Std.Time.Millisecond.Offset) : Async α := do
  let result ← Async.race (a.map Except.ok) (sleep time |>.map Except.error)

  match result with
  | .ok res => pure res
  | .error _ => throw (.userError "timeout")

def runDNS : Async Unit := do
  let infos ← timeout (DNS.getAddrInfo "google.com" "http") 1000

  unless infos.size > 0 do
    (throw <| IO.userError <| "No DNS results for google.com" : IO _)

def runDNSNoAscii : Async Unit := do
  let infos ← timeout (DNS.getAddrInfo "google.com▸" "http") 10000

  unless infos.size > 0 do
    (throw <| IO.userError <| "No DNS results for google.com" : IO _)

def runReverseDNS : Async Unit := do
  let result ← DNS.getNameInfo (.v4 ⟨.ofParts 8 8 8 8, 53⟩)
  assertBEq result.service "domain"
  assertBEq result.host "dns.google"

#eval runDNS.toIO >>= AsyncTask.block

/--
error: invalid argument (error code: 22, name is not ASCII)
-/
#guard_msgs in #eval runDNSNoAscii.toIO >>= AsyncTask.block

#eval runReverseDNS.toIO >>= AsyncTask.block
