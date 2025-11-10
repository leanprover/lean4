import Std.Internal.Async
import Std.Internal.UV
import Std.Net.Addr

open Std.Internal.IO Async
open Std.Net

/-!
# DNS Resolution Octet Test

This test specifically validates that all 4 octets of IPv4 addresses
are correctly populated by DNS resolution.

This is a regression test for a bug where `array_push` return values
were not captured in `lean_in_addr_to_ipv4_addr`, causing only the
last 2 octets to be populated (first 2 were always 0).
-/

def timeout [Inhabited α] (a : Async α) (time : Std.Time.Millisecond.Offset) : Async α := do
  let result ← Async.race (a.map Except.ok) (sleep time |>.map Except.error)
  match result with
  | .ok res => pure res
  | .error _ => throw (.userError "timeout")

/--
Test that DNS resolution returns valid IPv4 addresses with all 4 octets populated.
We use 1.1.1.1 (Cloudflare DNS) as a test case since we know the expected result.
-/
def testDNSAllOctets : Async Unit := do
  -- Resolve a known IP address to verify all octets are correct
  let infos ← timeout (DNS.getAddrInfo "1.1.1.1" "") 1000
  
  unless infos.size > 0 do
    throw <| IO.userError "No DNS results for 1.1.1.1"
  
  let ipv4 := infos.filterMap (fun | .v4 e => some e | _ => none)
  
  unless ipv4.size > 0 do
    throw <| IO.userError "No IPv4 results for 1.1.1.1"
  
  let addr := ipv4[0]!
  let octets := addr.octets
  
  -- Verify all octets are correct for 1.1.1.1
  unless octets[0] == 1 do
    throw <| IO.userError s!"First octet incorrect: expected 1, got {octets[0]}"
  
  unless octets[1] == 1 do
    throw <| IO.userError s!"Second octet incorrect: expected 1, got {octets[1]}"
  
  unless octets[2] == 1 do
    throw <| IO.userError s!"Third octet incorrect: expected 1, got {octets[2]}"
  
  unless octets[3] == 1 do
    throw <| IO.userError s!"Fourth octet incorrect: expected 1, got {octets[3]}"
  
  -- Also verify toString works correctly
  let addrStr := addr.toString
  unless addrStr == "1.1.1.1" do
    throw <| IO.userError s!"Address string incorrect: expected '1.1.1.1', got '{addrStr}'"

/--
Test that DNS resolution for google.com returns valid public IP addresses
with non-zero first octets (regression test for the array_push bug).
-/
def testDNSPublicIP : Async Unit := do
  let infos ← timeout (DNS.getAddrInfo "google.com" "") 1000
  
  unless infos.size > 0 do
    throw <| IO.userError "No DNS results for google.com"
  
  let ipv4 := infos.filterMap (fun | .v4 e => some e | _ => none)
  
  unless ipv4.size > 0 do
    throw <| IO.userError "No IPv4 results for google.com"
  
  let addr := ipv4[0]!
  let octets := addr.octets
  
  -- The bug caused the first octet to always be 0
  -- Google's IPs should never start with 0
  unless octets[0] != 0 do
    throw <| IO.userError s!"First octet is 0 - DNS resolution bug detected! Full address: {octets[0]}.{octets[1]}.{octets[2]}.{octets[3]}"
  
  -- Verify it's a valid public IP (not private/reserved)
  let isValid :=
    octets[0] != 0 &&           -- Not in 0.0.0.0/8
    octets[0] != 10 &&          -- Not in 10.0.0.0/8 (private)
    octets[0] != 127 &&         -- Not in 127.0.0.0/8 (loopback)
    !(octets[0] == 169 && octets[1] == 254) &&  -- Not in 169.254.0.0/16 (link-local)
    !(octets[0] == 172 && octets[1] >= 16 && octets[1] <= 31) &&  -- Not in 172.16.0.0/12 (private)
    !(octets[0] == 192 && octets[1] == 168) &&  -- Not in 192.168.0.0/16 (private)
    octets[0] < 224  -- Not multicast or reserved
  
  unless isValid do
    throw <| IO.userError s!"Invalid public IP for google.com: {octets[0]}.{octets[1]}.{octets[2]}.{octets[3]}"

#eval testDNSAllOctets.toIO >>= AsyncTask.block
#eval testDNSPublicIP.toIO >>= AsyncTask.block
