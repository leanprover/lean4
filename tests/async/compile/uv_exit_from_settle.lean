import Std.Async.Basic
import Std.Internal.UV

open Std Async Internal.UV

/-!
When `main` returns, finalization settles pending libuv promises with a canceled error. A
`(sync := true)` continuation runs right there, on the finalizing thread, and may call
`IO.Process.exit`, which stops libuv again on the same thread. That must exit with the given code
instead of deadlocking on the lock that serializes stopping libuv.
-/

def child : IO Unit := do
  let timer ← (← Timer.mk 60000 false).nextResult
  let onSettled : Option (Except IO.Error Unit) → IO Unit := fun
    | some (.error e) => if e.isCanceled then IO.Process.exit 7 else IO.Process.exit 1
    | _ => IO.Process.exit 2
  discard <| IO.mapTask onSettled timer.result? (sync := true)

def main (args : List String) : IO Unit := do
  if args == ["child"] then
    child
    return
  let proc ← IO.Process.spawn { cmd := (← IO.appPath).toString, args := #["child"] }
  for _ in [0:100] do
    if let some code ← proc.tryWait then
      IO.println s!"exit code {code}"
      return
    IO.sleep 100
  proc.kill
  IO.println "child hung"
