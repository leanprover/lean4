import Std.Internal.UV

/-!
`IO.sleep` finishes while its thread is interrupted by signals at a high rate. Linux reports the
remaining time of an interrupted `nanosleep` including the timer slack, so a sleep that restarts with
that remaining time never ends once signals arrive more often than the slack (50 µs by default).

A child process sends SIGUSR1 to this process in a tight loop, which can reach that rate on a
machine with many cores, while four threads each sleep 1 ms a hundred times. Eight repeating
SIGUSR1 handlers stay installed so that the signal never takes its default action; with a single
handler the storm interrupts the sleeping threads too rarely to show the problem.
-/

open Std.Internal.UV

def sleeper : IO Unit := do
  for _ in [0:100] do
    IO.sleep 1

def main : IO Unit := do
  if System.Platform.isWindows then
    IO.println "ok"
    return
  let guards ← (List.range 8).mapM fun _ => do
    let s ← Signal.mk 10 true
    discard <| s.next
    return s
  let pid ← IO.Process.getPID
  let storm ← IO.Process.spawn {
    cmd := "sh", args := #["-c", s!"while kill -USR1 {pid} 2>/dev/null; do :; done"] }
  let tasks ← (List.range 3).mapM fun _ => IO.asTask (prio := .dedicated) sleeper
  sleeper
  for t in tasks do
    IO.ofExcept (← IO.wait t)
  storm.kill
  discard <| storm.wait
  for s in guards do
    s.stop
  IO.println "ok"
