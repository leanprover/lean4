import Std.Internal.UV

/-!
Returning from `main` with `uv_getaddrinfo` requests still pending must not crash; see
`uv_random_exit`.

The awaited lookup checks that a program which performs a DNS lookup still exits cleanly. The
unawaited ones are still registered in the loop's request list when the loop thread stops.

`localhost` resolves from the hosts file, so this does not depend on a reachable resolver.
-/

open Std.Internal.UV

def main : IO Unit := do
  match (← DNS.getAddrInfo "localhost" "80" 0).result?.get with
  | some (.ok _) => IO.println "lookup completed"
  | some (.error e) => IO.println s!"lookup failed: {e}"
  | none => IO.println "lookup dropped"

  for _ in [0:32] do
    discard <| DNS.getAddrInfo "localhost" "80" 0

  IO.println "submitted"
