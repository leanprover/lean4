import Std.Async
import Std.Internal.UV

/-!
Two threads call `stop` on the same running repeating timer or signal waiter at once; in the timer
case a third thread keeps taking the event loop lock meanwhile. `stop` used to read or update the
handle's state outside the lock, so both calls could find the handle running and each release the
loop's reference to it.
-/

open Std.Async
open Std.Internal.UV

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
  for _ in [0:300] do onceTimer
  for _ in [0:500] do onceSignal
  IO.println "survived"

#eval main
