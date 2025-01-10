import Std.Internal.Async.Timer

/-
these tests are just some preliminary ones as `async_sleep.lean` already contains extensive tests
for the entire timer state machine and `Async.Timer` is merely a light wrapper around it.
-/

open Std.Internal.IO.Async

def BASE_DURATION : Std.Time.Millisecond.Offset := 10

namespace SleepTest

def oneSleep : IO Unit := do
  let task ← go
  assert! (← task.block) == 37
where
  go : IO (AsyncTask Nat) := do
    let sleep ← Sleep.mk BASE_DURATION
    (← sleep.wait).mapIO fun _ =>
      return 37

def doubleSleep : IO Unit := do
  let task ← go
  assert! (← task.block) == 37
where
  go : IO (AsyncTask Nat) := do
    let sleep ← Sleep.mk BASE_DURATION
    (← sleep.wait).bindIO fun _ => do
    (← sleep.wait).mapIO fun _ =>
      return 37

def resetSleep : IO Unit := do
  let task ← go
  assert! (← task.block) == 37
where
  go : IO (AsyncTask Nat) := do
    let sleep ← Sleep.mk BASE_DURATION
    let waiter ← sleep.wait
    sleep.reset
    waiter.mapIO fun _ =>
      return 37

def simpleSleep : IO Unit := do
  let task ← go
  assert! (← task.block) == 37
where
  go : IO (AsyncTask Nat) := do
    (← sleep BASE_DURATION).mapIO fun _ =>
      return 37

#eval oneSleep
#eval doubleSleep
#eval resetSleep
#eval simpleSleep

end SleepTest

namespace IntervalTest

def oneSleep : IO Unit := do
  let task ← go
  assert! (← task.block) == 37
where
  go : IO (AsyncTask Nat) := do
    let interval ← Interval.mk BASE_DURATION
    (← interval.tick).mapIO fun _ => do
      interval.stop
      return 37

def doubleSleep : IO Unit := do
  let task ← go
  assert! (← task.block) == 37
where
  go : IO (AsyncTask Nat) := do
    let interval ← Interval.mk BASE_DURATION
    (← interval.tick).bindIO fun _ => do
    (← interval.tick).mapIO fun _ => do
      interval.stop
      return 37

def resetSleep : IO Unit := do
  let task ← go
  assert! (← task.block) == 37
where
  go : IO (AsyncTask Nat) := do
    let interval ← Interval.mk BASE_DURATION
    (← interval.tick).bindIO fun _ => do
      let waiter ← interval.tick
      interval.reset
      waiter.mapIO fun _ => do
        interval.stop
        return 37

#eval oneSleep
#eval doubleSleep
#eval resetSleep

end IntervalTest
