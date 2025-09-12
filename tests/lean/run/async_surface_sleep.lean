import Std.Internal.Async.Timer

/-
these tests are just some preliminary ones as `async_sleep.lean` already contains extensive tests
for the entire timer state machine and `Async.Timer` is merely a light wrapper around it.
-/

open Std.Internal.IO.Async

def BASE_DURATION : Std.Time.Millisecond.Offset := 10

namespace SleepTest

def oneSleep : IO Unit := do
  let task ← go.block
  assert! task == 37
where
  go : Async Nat := do
    let sleep ← Sleep.mk BASE_DURATION
    sleep.wait
    return 37

def doubleSleep : IO Unit := do
  let task ← go.block
  assert! task == 37
where
  go : Async Nat := do
    let sleep ← Sleep.mk BASE_DURATION
    sleep.wait
    sleep.wait
    return 37

def resetSleep : IO Unit := do
  let task ← go.block
  assert! task == 37
where
  go : Async Nat := do
    let sleep ← Sleep.mk BASE_DURATION
    sleep.wait
    sleep.reset
    sleep.wait
    return 37

def simpleSleep : IO Unit := do
  let task ← go.block
  assert! task == 37
where
  go : Async Nat := do
    sleep BASE_DURATION
    return 37

#eval oneSleep
#eval doubleSleep
#eval resetSleep
#eval simpleSleep

end SleepTest

namespace IntervalTest

def oneSleep : IO Unit := do
  let task ← go.block
  assert! task == 37
where
  go : Async Nat := do
    let interval ← Interval.mk BASE_DURATION
    interval.tick
    interval.stop
    return 37

def doubleSleep : IO Unit := do
  let task ← go.block
  assert! task == 37
where
  go : Async Nat := do
    let interval ← Interval.mk BASE_DURATION
    interval.tick
    interval.tick
    interval.stop
    return 37

def resetSleep : IO Unit := do
  let task ← go.block
  assert! task == 37
where
  go : Async Nat := do
    let interval ← Interval.mk BASE_DURATION
    interval.tick
    let waiter := interval.tick
    interval.reset
    waiter
    interval.stop
    return 37

#eval oneSleep
#eval doubleSleep
#eval resetSleep

end IntervalTest
