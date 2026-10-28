import Std.Async.Watchdog
import Std.Async.Timer

open Std Async

/-!
Tests `Std.Async.Watchdog`: a wait that outlives its deadline cancels the context with `.deadline`,
a wait disarmed in time does not, arming again replaces the deadline, an earlier deadline wakes a
watchdog that sleeps until a later one, and other cancellations are not reported as its own.
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
