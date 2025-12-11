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

  let ipv4 := infos.filterMap (fun | .v4 e => some e | _ => none)

  if let some head := ipv4[0]? then
    let parts : Vector UInt8 4 := head.octets

    let isValid :=
      -- Not in 0.0.0.0/8 (current network)
      parts[0] != 0 &&
      -- Not in 10.0.0.0/8 (private)
      parts[0] != 10 &&
      -- Not in 127.0.0.0/8 (loopback)
      parts[0] != 127 &&
      -- Not in 169.254.0.0/16 (link-local)
      !(parts[0] == 169 && parts[1] == 254) &&
      -- Not in 172.16.0.0/12 (private)
      !(parts[0] == 172 && parts[1] >= 16 && parts[1] <= 31) &&
      -- Not in 192.168.0.0/16 (private)
      !(parts[0] == 192 && parts[1] == 168) &&
      -- Not in 224.0.0.0/4 (multicast)
      parts[0] < 224 &&
      -- Not 255.255.255.255 (broadcast)
      !(parts[0] == 255 && parts[1] == 255 && parts[2] == 255 && parts[3] == 255)

    unless isValid do
      throw <| IO.userError <| s!"Invalid IP address for google.com: {parts[0]}.{parts[1]}.{parts[2]}.{parts[3]}"

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
