import Std.Internal.UV

/-!
Returning from `main` with `uv_random` requests still pending must not crash. Their callbacks run on
the event loop thread, which used to keep running after the task manager it resolves promises
through had been freed.

The awaited call checks the completion path, including that the bytes libuv wrote reach the returned
`ByteArray`.
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
