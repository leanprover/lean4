import Std.Async
import Std.Net

/-!
Hostile text crossing the address and DNS FFI (PR #15653): malformed, over-long or NUL-containing
address strings (including IPv6 text with a `%` zone suffix) parse to `none`, DNS names that libuv or the resolver reject fail with an error
instead of crashing, and reverse lookups of ports 0 and 65535 and of an IPv4-mapped IPv6 address
succeed. IPv6 text at the maximum `INET6_ADDRSTRLEN` length parses and prints.
-/

open Std.Async
open Std.Net

def check (name : String) (cond : Bool) (detail : String := "") : IO Unit :=
  unless cond do
    throw <| IO.userError s!"{name}: {detail}"

def runAsync (x : Async α) : IO α := do
  (← x.toIO).block

def expectError (what : String) (x : Async α) : IO Unit := do
  match ← (runAsync x).toBaseIO with
  | .error _ => pure ()
  | .ok _ => throw <| IO.userError s!"{what}: succeeded"

#eval do
  let long := String.ofList (List.replicate 5000 '1')
  for s in ["01.2.3.4", "1.2.3", "1.2.3.4.5", "256.1.1.1", " 1.2.3.4", "1.2.3.4 ", "1.2.3.4\x00junk", "", long] do
    check s!"IPv4 {repr (s.take 20).toString}" (IPv4Addr.ofString s).isNone
  -- A zone suffix is rejected rather than silently dropped, since an `IPv6Addr` has no zone.
  for s in ["1::2::3", ":::", "1:2:3:4:5:6:7:8:9", "::1\x00junk", "", "[::1]", String.ofList (List.replicate 5000 ':'),
            String.ofList (List.replicate 50 'a') ++ "%x", "::1%garbage!!", "fe80::1%", "fe80::1%lo0"] do
    check s!"IPv6 {repr (s.take 20).toString}" (IPv6Addr.ofString s).isNone
  -- 45 characters, the longest IPv6 text.
  let maxText := "ffff:ffff:ffff:ffff:ffff:ffff:255.255.255.255"
  let allOnes := IPv6Addr.ofParts 0xffff 0xffff 0xffff 0xffff 0xffff 0xffff 0xffff 0xffff
  check "longest IPv6 text" (IPv6Addr.ofString maxText == some allOnes)
  check "all-ones IPv6 text" (allOnes.toString == "ffff:ffff:ffff:ffff:ffff:ffff:ffff:ffff") allOnes.toString
  let mapped := IPv6Addr.ofParts 0 0 0 0 0 0xffff 0xffff 0xffff
  check "longest IPv4-mapped text" (mapped.toString == "::ffff:255.255.255.255") mapped.toString

#eval do
  expectError "NUL in host" <| DNS.getAddrInfo "localhost\x00evil" "80"
  expectError "NUL in service" <| DNS.getAddrInfo "localhost" "80\x00evil"
  expectError "empty host" <| DNS.getAddrInfo "" "80"
  expectError "host over 255 bytes" <| DNS.getAddrInfo (String.ofList (List.replicate 300 'a')) "80"
  expectError "host of 100000 bytes" <| DNS.getAddrInfo (String.ofList (List.replicate 100000 'a')) "80"
  expectError "non-ASCII host" <| DNS.getAddrInfo "héllo.invalid" "80"

  let mapped ← runAsync <| DNS.getAddrInfo "::ffff:127.0.0.1" "80"
  check "IPv4-mapped numeric host"
    (mapped.size > 0 && mapped.all (· == IPAddr.v6 (.ofParts 0 0 0 0 0 0xffff 0x7f00 1))) s!"{mapped}"

  for port in [0, 65535] do
    let info ← runAsync <| DNS.getNameInfo (.v4 ⟨.ofParts 127 0 0 1, port⟩)
    check s!"getNameInfo port {port}" (info.service == toString port) info.service
  let info ← runAsync <| DNS.getNameInfo (.v6 ⟨.ofParts 0 0 0 0 0 0xffff 0x7f00 1, 65535⟩)
  check "getNameInfo IPv4-mapped" (info.service == "65535" && !info.host.isEmpty) s!"{info.host} {info.service}"
