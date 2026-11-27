import Std.Async

open Std Async Internal.UV

/-!
`IO.Process.exit` called from a pool task while other threads keep timers and libuv's thread pool
busy must exit with the given code: it stops libuv first, so that no thread enters libuv after
`exit()` destroys libuv's state, and must not deadlock on a thread inside libuv. The parent runs the
child 20 times.
-/

def child : IO Unit := do
  for _ in [0:16] do
    discard <| IO.asTask (prio := .dedicated) do
      let timer ← Timer.mk 0 true
      for _ in [0:100000] do
        discard <| IO.wait (← timer.nextResult).result?
    discard <| IO.asTask (prio := .dedicated) do
      for _ in [0:100000] do
        discard <| (Async.DNS.getAddrInfo "localhost" "80").block.toBaseIO
  IO.sleep 20
  discard <| IO.wait (← IO.asTask (IO.Process.exit 0 : IO Unit))

def main (args : List String) : IO Unit := do
  if args == ["child"] then
    child
    return
  for run in [1:21] do
    let out ← IO.Process.output { cmd := (← IO.appPath).toString, args := #["child"] }
    if out.exitCode != 0 then
      IO.println s!"run {run} of 20 exited with {out.exitCode}"
      return
  IO.println "ok"
