import Std.Internal.UV

/-!
A `Promise.result!` continuation on a libuv promise that is still pending when the program exits
must not run.

Tearing down the event loop used to drop such a promise, resolving it to `none`: the continuation
then ran on the exiting thread, where `Promise.result!` panics and blocks forever, so the process
never exited.
-/

open Std.Internal.UV

def main : IO Unit := do
  let timer ← Timer.mk 3600000 false
  let fired ← timer.next
  let _ ← IO.mapTask (fun (_ : Unit) => IO.println "fired") fired.result!
  IO.println "exiting"
