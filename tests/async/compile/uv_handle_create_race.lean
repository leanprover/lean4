import Std.Internal.UV

open Std.Internal.UV

/-!
Creating a libuv handle while the program finishes must not crash it: stopping libuv reads every
handle's `data` field as its Lean owner, so the constructors must set it before releasing the loop
lock. The child creates handles of one kind on a dedicated thread until creating one fails, and
returns from `main` or calls `IO.Process.exit` after 2 ms. Where `taskset` exists (Linux) the child
is pinned to one CPU, where the creating thread is often preempted inside the window, and each case
runs 40 times; elsewhere 10 times.
-/

def kinds : List (String × IO Unit) := [
  ("timer", discard <| Timer.mk 1000 false),
  -- SIGWINCH
  ("signal", discard <| Signal.mk 28 false),
  ("tcp", discard TCP.Socket.new),
  ("udp", discard UDP.Socket.new)]

def child (mk : IO Unit) (how : String) : IO Unit := do
  discard <| IO.asTask (prio := .dedicated) do
    while (← mk.toBaseIO) matches .ok _ do pure ()
  IO.sleep 2
  if how == "exit" then
    IO.Process.exit 0

def main (args : List String) : IO Unit := do
  if let ["child", kind, how] := args then
    return (← child (kinds.lookup kind).get! how)
  let probe ← (IO.Process.output { cmd := "taskset", args := #["-c", "0", "true"] }).toBaseIO
  let pinned := probe matches .ok { exitCode := 0, .. }
  let pin := if pinned then #["taskset", "-c", "0"] else #[]
  let n := if pinned then 40 else 10
  for how in ["return", "exit"] do
    for (kind, _) in kinds do
      let argv := pin ++ #[(← IO.appPath).toString, "child", kind, how]
      for run in [1:n+1] do
        let out ← IO.Process.output { cmd := argv[0]!, args := argv.extract 1 }
        if out.exitCode != 0 then
          IO.println s!"{kind} created during {how}: run {run} of {n} exited with {out.exitCode}"
          return
  IO.println "ok"
