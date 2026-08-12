import Std.Internal.UV

/-!
Regression guard: a program that performs a DNS lookup must exit cleanly.

`localhost` resolves from the hosts file, so this still submits a `uv_getaddrinfo` to the threadpool
and registers it in the loop's request list without depending on a reachable resolver.
-/

open Std.Internal.UV

def main : IO Unit := do
  let promise ← DNS.getAddrInfo "localhost" "80" 0
  match promise.result?.get with
  | some _ => IO.println "lookup completed"
  | none => IO.println "lookup dropped"
