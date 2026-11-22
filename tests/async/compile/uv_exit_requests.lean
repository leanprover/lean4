import Std.Internal.UV

/-!
Returning from `main` with threadpool requests still in flight exits cleanly. The teardown at exit
cancels the `uv_random` and `uv_getaddrinfo` requests that have not started and waits for the others,
and runs none of their continuations. These requests are not handles, so only the loop's list of
requests reaches them.

The awaited calls check the completion path, including that the bytes `uv_random` wrote reach the
returned `ByteArray`. `localhost` resolves from the hosts file, so this does not depend on a reachable
resolver.
-/

open Std.Internal.UV

def main : IO Unit := do
  match (← System.random 256).result?.get with
  | some (.ok bytes) =>
    IO.println s!"size: {bytes.size}"
    IO.println s!"nonzero: {bytes.toList.any (· != 0)}"
  | some (.error e) => IO.println s!"failed: {e}"
  | none => IO.println "dropped"

  match (← DNS.getAddrInfo "localhost" "80" 0).result?.get with
  | some (.ok _) => IO.println "lookup completed"
  | some (.error e) => IO.println s!"lookup failed: {e}"
  | none => IO.println "lookup dropped"

  -- Occupies libuv's threadpool, so that the requests below are still queued at exit.
  for _ in [0:4] do
    discard <| System.random (8 * 1024 * 1024)

  for _ in [0:32] do
    discard <| System.random 4096
    discard <| DNS.getAddrInfo "localhost" "80" 0

  IO.println "submitted"
