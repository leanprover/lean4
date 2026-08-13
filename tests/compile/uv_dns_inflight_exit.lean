import Std.Internal.UV

/-!
Exercises teardown of `uv_getaddrinfo` requests that are still registered when the process exits.

`uv_getaddrinfo` runs on the threadpool and is invisible to `uv_walk`, so the loop's request list is
the only thing that can reach these promises; without it `finalize_libuv` would block until the
resolver returns. Nothing here is awaited, so `event_loop_cancel_requests` and the drain that
`event_loop_abandon_requests` backstops run with the list non-empty.

`localhost` resolves from the hosts file, so this does not depend on a reachable resolver.
-/

open Std.Internal.UV

def main : IO Unit := do
  for _ in [0:32] do
    discard <| DNS.getAddrInfo "localhost" "80" 0

  IO.println "submitted"
