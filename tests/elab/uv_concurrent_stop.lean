import Std.Async
import Std.Internal.UV

open Std.Async
open Std.Internal.UV

/-!
Races two `stop` calls against one libuv handle (timer and signal) to check the handle is released
exactly once. `sigwinch` is the only signal in `Std.Async.Signal` that libuv accepts on every
platform: on Windows the others map to `signum = 0` and `uv_signal_start` rejects them with
`UV_EINVAL`.
-/

/-- Hammers the event-loop mutex without touching any timer. -/
def hammer : IO Unit := do
  for _ in [0:3000] do
    let _ ← Loop.alive

def onceTimer : IO Unit := do
  let t ← Timer.mk 10000 true
  let p ← t.next
  let _ ← IO.wait p.result!
  let h ← IO.asTask (prio := .dedicated) hammer
  let a ← IO.asTask (prio := .dedicated) t.stop
  let b ← IO.asTask (prio := .dedicated) t.stop
  let _ ← IO.wait a; let _ ← IO.wait b; let _ ← IO.wait h

def onceSignal : IO Unit := do
  let w ← Signal.Waiter.mk .sigwinch (repeating := true)
  let _ ← w.wait
  let t1 ← IO.asTask (prio := .dedicated) w.stop
  let t2 ← IO.asTask (prio := .dedicated) w.stop
  let _ ← IO.wait t1; let _ ← IO.wait t2

def main : IO Unit := do
  for _ in [0:3000] do onceTimer
  for _ in [0:5000] do onceSignal
  IO.println "survived"

#eval main
