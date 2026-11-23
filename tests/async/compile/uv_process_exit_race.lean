import Std.Async

open Std Async Internal.UV

/-!
`IO.Process.exit` runs `exit()` while other threads keep running, and `exit()` runs libuv's destructor,
which destroys the thread pool's mutex. A task that started a DNS lookup afterwards locked the
destroyed mutex, and libuv aborted (about half the runs). `IO.Process.exit` now stops libuv first:
later libuv calls fail with `UV_ECANCELED`, and a thread already inside libuv keeps the exiting thread
waiting until it leaves, then waits forever.

The child keeps timers and the thread pool busy and calls `IO.Process.exit 0` from a pool task; the
parent runs it 20 times and expects every run to exit with 0.
-/

def child : IO Unit := do
  for _ in [0:16] do
    discard <| IO.asTask (prio := .dedicated) do
      let timer ← Timer.mk 0 true
      for _ in [0:100000] do
        discard <| IO.wait (← timer.next).result?
  for _ in [0:16] do
    discard <| IO.asTask (prio := .dedicated) do
      for _ in [0:100000] do
        discard <| (Async.DNS.getAddrInfo "localhost" "80").block.toBaseIO
  IO.sleep 20
  let exiting ← IO.asTask (IO.Process.exit 0 : IO Unit)
  discard <| IO.wait exiting
  IO.sleep 5000
  IO.println "IO.Process.exit returned"

def main (args : List String) : IO Unit := do
  if args.head? == some "child" then
    child
    return
  let mut codes := #[]
  for _ in [0:20] do
    let out ← IO.Process.output { cmd := (← IO.appPath).toString, args := #["child"] }
    codes := codes.push out.exitCode
  if codes.all (· == 0) then
    IO.println "ok"
  else
    IO.println s!"exit codes: {codes}"
