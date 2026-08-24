import Std.Internal.UV

/-!
Covers `lean_uv_random`, the only loop-bound request that carries a Lean object (`owned`) into the
loop's request list.

The awaited call checks the completion path, including that the bytes libuv wrote into the request's
scratch buffer reach the returned `ByteArray`. The unawaited calls are still registered when
`finalize_libuv` runs, so they drive `event_loop_cancel_requests` and the teardown drain; a request
whose worker is already inside `getrandom` cannot be cancelled and is abandoned instead, which is why
that scratch buffer must not be the `ByteArray`'s payload.
-/

open Std.Internal.UV

def main : IO Unit := do
  match (← System.random 256).result?.get with
  | some (.ok bytes) =>
    IO.println s!"size: {bytes.size}"
    IO.println s!"nonzero: {bytes.toList.any (· != 0)}"
  | some (.error e) => IO.println s!"failed: {e}"
  | none => IO.println "dropped"

  for _ in [0:32] do
    discard <| System.random 4096
