import Std.Async.Watchdog
import Std.Async.Timer

open Std Async

/-!
Tests `Std.Async.Watchdog`: a wait that outlives its deadline cancels the context with `.deadline`,
a wait disarmed in time does not, arming again replaces the deadline, an earlier deadline wakes a
watchdog that sleeps until a later one, other cancellations are not reported as its own, and
`armAfter` times a wait from when its task finishes unless a later call replaced it. `disarm`
reports a late wait even when the watchdog itself could not run, and a reported timeout always
matches the context's cancellation reason.
-/

/-- A wait that outlives its deadline cancels the context, never before the deadline. -/
def firesAfterDeadline : Async (Bool × Bool × Bool × Bool) := do
  let ctx ← CancellationContext.new
  let wd ← Watchdog.new ctx
  let start ← IO.monoMsNow
  wd.arm 50
  await (← ctx.done)
  let elapsed := (← IO.monoMsNow) - start
  let fired ← wd.disarm
  -- Arming after the deadline passed changes nothing.
  wd.arm 10
  return (fired, (← ctx.getCancellationReason) == some .deadline, elapsed ≥ 50, ← wd.disarm)

/-- info: (true, true, true, true) -/
#guard_msgs in
#eval firesAfterDeadline.block

/-- A wait disarmed before its deadline leaves the context alone. -/
def disarmedInTime : Async (Bool × Bool) := do
  let ctx ← CancellationContext.new
  let wd ← Watchdog.new ctx
  wd.arm 200
  let fired ← wd.disarm
  sleep 400
  return (fired, ← ctx.isCancelled)

/-- info: (false, false) -/
#guard_msgs in
#eval disarmedInTime.block

/-- Many waits that each end in time, as on an idle keep-alive connection, never fire. -/
def manyWaitsInTime : Async (Bool × Bool) := do
  let ctx ← CancellationContext.new
  let wd ← Watchdog.new ctx
  let mut fired := false
  for _ in *...1000 do
    wd.arm 200
    fired := fired || (← wd.disarm)
  sleep 300
  return (fired, ← ctx.isCancelled)

/-- info: (false, false) -/
#guard_msgs in
#eval manyWaitsInTime.block

/-- Arming again during a wait replaces its deadline, also with a later one. -/
def rearmExtends : Async (Bool × Bool × Bool) := do
  let ctx ← CancellationContext.new
  let wd ← Watchdog.new ctx
  let start ← IO.monoMsNow
  wd.arm 50
  wd.arm 1000
  sleep 300
  let cancelledEarly ← ctx.isCancelled
  await (← ctx.done)
  let elapsed := (← IO.monoMsNow) - start
  return (cancelledEarly, ← wd.disarm, elapsed ≥ 1000)

/-- info: (false, true, true) -/
#guard_msgs in
#eval rearmExtends.block

/--
A deadline earlier than the one the watchdog sleeps until wakes it up: the wait fires after about
50 ms, not after the first wait's 60 s.
-/
def earlierDeadlineWakes : Async (Bool × Bool) := do
  let ctx ← CancellationContext.new
  let wd ← Watchdog.new ctx
  wd.arm 60000
  sleep 20
  discard <| wd.disarm
  let start ← IO.monoMsNow
  wd.arm 50
  await (← ctx.done)
  let elapsed := (← IO.monoMsNow) - start
  return (← wd.disarm, elapsed < 30000)

/-- info: (true, true) -/
#guard_msgs in
#eval earlierDeadlineWakes.block

/-- After many deadlines that move earlier, each restarting the timer, the watchdog still fires. -/
def manyRestarts : Async (Bool × Bool) := do
  let ctx ← CancellationContext.new
  let wd ← Watchdog.new ctx
  for _ in *...500 do
    wd.arm 20000
    wd.arm 10000
    discard <| wd.disarm
  wd.arm 50
  await (← ctx.done)
  return (← wd.disarm, (← ctx.getCancellationReason) == some .deadline)

/-- info: (true, true) -/
#guard_msgs in
#eval manyRestarts.block

/-- A context cancelled for another reason is not reported as the watchdog's own timeout. -/
def otherCancellation : Async (Bool × Bool × Bool) := do
  let ctx ← CancellationContext.new
  let wd ← Watchdog.new ctx
  wd.arm 10000
  ctx.cancel .shutdown
  sleep 50
  return (← wd.disarm, ← wd.hasFired, (← ctx.getCancellationReason) == some .shutdown)

/-- info: (false, false, true) -/
#guard_msgs in
#eval otherCancellation.block

/-- A watchdog on a forked context cancels only that context. -/
def childOnly : Async (Bool × Bool) := do
  let parent ← CancellationContext.new
  let child ← parent.fork
  let wd ← Watchdog.new child
  wd.arm 50
  await (← child.done)
  return (← wd.disarm, ← parent.isCancelled)

/-- info: (true, false) -/
#guard_msgs in
#eval childOnly.block

/--
`armAfter` starts timing only once its task finishes, and drops a deadline the wait had before, so
the watchdog does not fire while the task runs.
-/
def armAfterWaitsForTask : Async (Bool × Bool × Bool) := do
  let ctx ← CancellationContext.new
  let wd ← Watchdog.new ctx
  let task ← IO.Promise.new (α := Unit)
  wd.arm 30
  wd.armAfter task.result? 100
  sleep 200
  let cancelledEarly ← ctx.isCancelled
  let start ← IO.monoMsNow
  task.resolve ()
  await (← ctx.done)
  let elapsed := (← IO.monoMsNow) - start
  return (cancelledEarly, ← wd.disarm, elapsed ≥ 100)

/-- info: (false, true, true) -/
#guard_msgs in
#eval armAfterWaitsForTask.block

/-- A wait that ends before the task of `armAfter` finishes arms nothing. -/
def armAfterEndedWait : Async (Bool × Bool) := do
  let ctx ← CancellationContext.new
  let wd ← Watchdog.new ctx
  let task ← IO.Promise.new (α := Unit)
  wd.armAfter task.result? 30
  let fired ← wd.disarm
  task.resolve ()
  sleep 200
  return (fired, ← ctx.isCancelled)

/-- info: (false, false) -/
#guard_msgs in
#eval armAfterEndedWait.block

/-- An `arm` after `armAfter` replaces its deadline, also once the task of `armAfter` finishes. -/
def armAfterThenArm : Async Bool := do
  let ctx ← CancellationContext.new
  let wd ← Watchdog.new ctx
  let task ← IO.Promise.new (α := Unit)
  wd.armAfter task.result? 30
  wd.arm 5000
  task.resolve ()
  sleep 300
  let cancelled ← ctx.isCancelled
  ctx.cancel .cancel
  return cancelled

/-- info: false -/
#guard_msgs in
#eval armAfterThenArm.block

/-- A later `armAfter` replaces an earlier one whose task finishes first. -/
def armAfterThenArmAfter : Async Bool := do
  let ctx ← CancellationContext.new
  let wd ← Watchdog.new ctx
  let first ← IO.Promise.new (α := Unit)
  let second ← IO.Promise.new (α := Unit)
  wd.armAfter first.result? 30
  wd.armAfter second.result? 30
  first.resolve ()
  sleep 300
  let cancelled ← ctx.isCancelled
  -- Keeps `second` alive until here, since dropping a promise finishes its task.
  second.resolve ()
  ctx.cancel .cancel
  return cancelled

/-- info: false -/
#guard_msgs in
#eval armAfterThenArmAfter.block

/-- A wait that `armAfter` armed and that ends in time is not reported. -/
def armAfterDisarmedInTime : Async (Bool × Bool) := do
  let ctx ← CancellationContext.new
  let wd ← Watchdog.new ctx
  let task ← IO.Promise.new (α := Unit)
  wd.armAfter task.result? 200
  task.resolve ()
  sleep 20
  let fired ← wd.disarm
  sleep 300
  return (fired, ← ctx.isCancelled)

/-- info: (false, false) -/
#guard_msgs in
#eval armAfterDisarmedInTime.block

/--
A wait disarmed after its deadline is reported even when the watchdog could not run, here because
every worker of the task pool is busy.
-/
def lateDisarmUnderLoad : IO (Bool × Option CancellationReason) := do
  let ctx ← CancellationContext.new
  let wd ← Watchdog.new ctx
  let release ← IO.mkRef false
  wd.arm 50
  let blockers ← (List.range 128).mapM fun _ => IO.asTask do
    while !(← release.get) do
      IO.sleep 1
  IO.sleep 300
  let fired ← wd.disarm
  let reason ← ctx.getCancellationReason
  release.set true
  for blocker in blockers do
    discard <| IO.wait blocker
  return (fired, reason)

/-- info: (true, some (Std.CancellationReason.deadline)) -/
#guard_msgs in
#eval lateDisarmUnderLoad

/-- A late wait whose context was cancelled for another reason first is not reported. -/
def lateAfterOtherCancellation : Async (Bool × Bool × Option CancellationReason) := do
  let ctx ← CancellationContext.new
  let wd ← Watchdog.new ctx
  wd.arm 50
  ctx.cancel .shutdown
  sleep 150
  return (← wd.disarm, ← wd.hasFired, ← ctx.getCancellationReason)

/-- info: (false, false, some (Std.CancellationReason.shutdown)) -/
#guard_msgs in
#eval lateAfterOtherCancellation.block

/--
When a deadline races with another cancellation, `hasFired` is `true` exactly when the context was
cancelled with `.deadline`. Returns the number of runs where they disagree.
-/
def firedMatchesReason : IO Nat := do
  let mut mismatches := 0
  for _ in *...2000 do
    let ctx ← CancellationContext.new
    let wd ← Watchdog.new ctx
    wd.arm 0
    ctx.cancel .shutdown
    discard <| IO.wait (← ctx.done)
    let fired ← wd.hasFired
    let deadline := (← ctx.getCancellationReason) == some .deadline
    if fired != deadline then
      mismatches := mismatches + 1
  return mismatches

/-- info: 0 -/
#guard_msgs in
#eval firedMatchesReason
