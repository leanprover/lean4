import Std.Internal.UV

/-!
A `Promise.result!` continuation on a libuv promise that is still pending when the program exits
must not run.

Teardown keeps such a promise unresolved. Dropping it would resolve it to `none` and run the
continuation on the exiting thread, where `Promise.result!` panics and then blocks, so the process
would never exit.
-/

open Std.Internal.UV

def main : IO Unit := do
  let timer ← Timer.mk 3600000 false
  let fired ← timer.next
  let _ ← IO.mapTask (fun (_ : Unit) => IO.println "fired") fired.result!
  IO.println "exiting"
