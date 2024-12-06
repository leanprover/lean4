import Std.Internal.Async

open Std.Internal.IO.Async

def assertElapsed (t1 t2 : Nat) (should : Nat) (eps : Nat) : IO Unit := do
  let dur := t2 - t1
  if (Int.ofNat dur - Int.ofNat should).natAbs > eps then
    throw <| .userError s!"elapsed time was too different, measured {dur}, should: {should}, tolerance: {eps}"

def assertDuration (x : IO (AsyncTask α)) (should : Nat) (eps : Nat) : IO Unit := do
  let t1 ← IO.monoMsNow
  discard <| AsyncTask.spawnBlocking <| x
  let t2 ← IO.monoMsNow
  assertElapsed t1 t2 should eps

-- generous tolerance for slow CI systems
def EPS : Nat := 3

namespace SleepTest

def timerSleep : IO Unit := do
  assertDuration go 20 EPS
where
  go : IO (AsyncTask Unit) := do
    let timer ← Sleep.mk 20
    timer.wait

def oneShotSleep : IO Unit := do
  assertDuration (sleep 20) 20 EPS

def promiseBehavior1 : IO Unit := do
  let timer ← Sleep.mk 20
  let prom ← timer.wait
  assert! (← prom.getState) != .finished
  IO.sleep (20 + EPS).toUInt32
  assert! (← prom.getState) == .finished

def promiseBehavior2 : IO Unit := do
  let timer ← Sleep.mk 20
  let prom1 ← timer.wait
  let prom2 ← timer.wait
  assert! (← prom1.getState) != .finished
  assert! (← prom2.getState) != .finished
  IO.sleep (20 + EPS).toUInt32
  assert! (← prom1.getState) == .finished
  assert! (← prom2.getState) == .finished

def promiseBehavior3 : IO Unit := do
  let timer ← Sleep.mk 20
  let prom1 ← timer.wait
  assert! (← prom1.getState) != .finished
  IO.sleep (20 + EPS).toUInt32
  assert! (← prom1.getState) == .finished
  let prom2 ← timer.wait
  assert! (← prom2.getState) == .finished

def resetBehavior : IO Unit := do
  let timer ← Sleep.mk 20
  let prom ← timer.wait
  assert! (← prom.getState) != .finished

  IO.sleep 10
  assert! (← prom.getState) != .finished
  timer.reset

  IO.sleep 10
  assert! (← prom.getState) != .finished

  IO.sleep (10 + EPS).toUInt32
  assert! (← prom.getState) == .finished

def parallelSleep : IO Unit := do
  assertDuration go 20 EPS
where
  go : IO (AsyncTask Unit) := do
    let s1 ← sleep 20
    let s2 ← sleep 10
    s1.bindIO fun _ =>
    s2.mapIO fun _ =>
      ()

def sequentialSleep1 : IO Unit := do
  assertDuration go 20 EPS
where
  go : IO (AsyncTask Unit) := do
    (← sleep 10).bindIO fun _ => do
    (← sleep 10).mapIO fun _ =>
      ()

def sequentialSleep2 : IO Unit := do
  assertDuration go 20 EPS
where
  go : IO (AsyncTask Unit) := do
    let s1 ← Sleep.mk 10
    let s2 ← Sleep.mk 10
    (← s1.wait).bindIO fun _ => do
    (← s2.wait).mapIO fun _ =>
      ()

#eval timerSleep
#eval oneShotSleep
#eval promiseBehavior1
#eval promiseBehavior2
#eval promiseBehavior3
#eval resetBehavior
#eval parallelSleep
#eval sequentialSleep1
#eval sequentialSleep2

end SleepTest

namespace IntervalTest

def sleepFirst : IO Unit := do
  assertDuration go 0 EPS
where
  go : IO (AsyncTask Unit) := do
    let timer ← Interval.mk 20
    timer.tick

def sleepSecond : IO Unit := do
  assertDuration go 20 EPS
where
  go : IO (AsyncTask Unit) := do
    let timer ← Interval.mk 20
    (← timer.tick).bindIO fun _ => timer.tick

def promiseBehavior1 : IO Unit := do
  let timer ← Interval.mk 20
  let p1 ← timer.tick
  IO.sleep EPS.toUInt32
  assert! (← p1.getState) == .finished
  let p2 ← timer.tick
  assert! (← p2.getState) != .finished
  IO.sleep (20 + EPS).toUInt32
  assert! (← p2.getState) == .finished

def promiseBehavior2 : IO Unit := do
  let timer ← Interval.mk 20
  let p1 ← timer.tick
  IO.sleep EPS.toUInt32
  assert! (← p1.getState) == .finished

  let prom1 ← timer.tick
  let prom2 ← timer.tick
  assert! (← prom1.getState) != .finished
  assert! (← prom2.getState) != .finished
  IO.sleep (20 + EPS).toUInt32
  assert! (← prom1.getState) == .finished
  assert! (← prom2.getState) == .finished

def promiseBehavior3 : IO Unit := do
  let timer ← Interval.mk 20
  let p1 ← timer.tick
  IO.sleep EPS.toUInt32
  assert! (← p1.getState) == .finished

  let prom1 ← timer.tick
  assert! (← prom1.getState) != .finished
  IO.sleep (20 + EPS).toUInt32
  assert! (← prom1.getState) == .finished
  let prom2 ← timer.tick
  assert! (← prom2.getState) != .finished
  IO.sleep (20 + EPS).toUInt32
  assert! (← prom2.getState) == .finished

def delayedTickBehavior : IO Unit := do
  let timer ← Interval.mk 20
  let p1 ← timer.tick
  IO.sleep EPS.toUInt32
  assert! (← p1.getState) == .finished

  IO.sleep 10
  let p2 ← timer.tick
  assert! (← p2.getState) != .finished
  IO.sleep (10 + EPS).toUInt32
  assert! (← p2.getState) == .finished

def skippedTickBehavior : IO Unit := do
  let timer ← Interval.mk 20
  let p1 ← timer.tick
  IO.sleep EPS.toUInt32
  assert! (← p1.getState) == .finished

  IO.sleep 30
  let p2 ← timer.tick
  assert! (← p2.getState) != .finished
  IO.sleep (10 + EPS).toUInt32
  assert! (← p2.getState) == .finished

def resetBehavior : IO Unit := do
  let timer ← Interval.mk 20
  let p1 ← timer.tick
  IO.sleep EPS.toUInt32
  assert! (← p1.getState) == .finished

  let prom ← timer.tick
  assert! (← prom.getState) != .finished

  IO.sleep 10
  assert! (← prom.getState) != .finished
  timer.reset

  IO.sleep 10
  assert! (← prom.getState) != .finished

  IO.sleep (10 + EPS).toUInt32
  assert! (← prom.getState) == .finished

def sequentialSleep : IO Unit := do
  assertDuration go 20 EPS
where
  go : IO (AsyncTask Unit) := do
    let t ← Interval.mk 10
    -- 0th interval ticks instantly
    (← t.tick).bindIO fun _ => do
    (← t.tick).bindIO fun _ => do
    (← t.tick).mapIO fun _ => ()

#eval sleepFirst
#eval sleepSecond
#eval promiseBehavior1
#eval promiseBehavior2
#eval promiseBehavior3
#eval delayedTickBehavior
#eval skippedTickBehavior
#eval resetBehavior
#eval sequentialSleep

end IntervalTest
