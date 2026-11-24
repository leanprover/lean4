import Std.Internal.UV

open Std.Internal.UV

/-!
After `main` returns, finalization settles pending libuv promises on the finalizing thread, where a
`(sync := true)` continuation may call `IO.Process.exit`. That stops libuv again on the same thread
and must exit with the given code (checked through `TEST_EXIT`) instead of deadlocking.
-/

def main : IO Unit := do
  let timer ← (← Timer.mk 60000 false).nextResult
  discard <| IO.mapTask (β := Unit) (sync := true) (fun
    | some (.error e) => IO.Process.exit (if e.isCanceled then 7 else 1)
    | _ => IO.Process.exit 2) timer.result?
