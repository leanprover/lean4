/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Time
public import Std.Internal.UV.Timer
public import Std.Sync.CancellationContext

public section

/-!
This module provides `Watchdog`, which enforces deadlines on a sequence of waits with a single
background timer.
-/

namespace Std
namespace Async

namespace Watchdog

/--
The state shared between a watchdog and the code that arms it.
-/
private structure State where
  /-- Whether a timed wait is in progress. -/
  waiting : Bool := false
  /-- When the current wait expires, as a value of `IO.monoMsNow`. -/
  deadline : Nat := 0
  /--
  Whether a wait outlived its deadline. Once it is set, the watchdog stops and the context is
  cancelled with `.deadline`, unless it was cancelled for another reason first.
  -/
  fired : Bool := false
  /-- The deadline the watchdog's timer is set for, or `none` while it waits without a timer. -/
  scheduled : Option Nat := none
  /--
  Counts the calls that arm or end a wait, so that `armAfter` applies its deadline only if no later
  call replaced it.
  -/
  epoch : Nat := 0

private inductive Step where
  | stop
  | fire
  | park
  | sleep (ms : Nat)

/--
What the watchdog does next at time `now`, and the state it leaves behind.
-/
private def State.next (now : Nat) (s : State) : Step × State :=
  if s.fired then
    (.stop, s)
  else if s.waiting then
    if now ≥ s.deadline then
      (.fire, { s with fired := true, waiting := false, scheduled := none })
    else
      (.sleep (s.deadline - now), { s with scheduled := some s.deadline })
  else
    (.park, { s with scheduled := none })

end Watchdog

/--
Enforces deadlines on a sequence of waits with a single background timer. A wait starts with
`arm` and ends with `disarm`; when one outlives its deadline, the watchdog cancels its context with
`.deadline` and stops. The context is never cancelled before the deadline.

Waits whose deadlines keep moving later, such as idle timeouts, cost no timer operation each: only
a deadline earlier than the one the timer is set for restarts it.

The context is cancelled from a task on the shared task pool, so while every worker is busy, a late
wait may stay uncancelled until one is free. `disarm` reports a late wait regardless.

The watchdog and its timer stay alive until the context is cancelled, so the context should be
cancelled once the watchdog is no longer needed.
-/
structure Watchdog where
  /-- Assembles a watchdog from its parts without starting its background task. -/
  private mk ::
  private ctx : CancellationContext
  private state : IO.Ref Watchdog.State
  /--
  The promise whose resolution makes the watchdog re-read `state`. Each round of the watchdog
  replaces it.
  -/
  private wake : IO.Ref (IO.Promise Unit)
  /-- The timer of the watchdog's current round, stopped when the next round starts. -/
  private timer : IO.Ref (Option Internal.UV.Timer)

namespace Watchdog

/--
Marks the watchdog as fired and cancels its context.
-/
private def fire (wd : Watchdog) : BaseIO Unit := do
  wd.state.modify fun s => { s with fired := true, waiting := false, scheduled := none }
  wd.ctx.cancel .deadline

/--
Runs one round of the watchdog: re-reads the state, then fires, stops, or waits until a timer or a
call that needs it to re-read the state wakes it. Each round is started by the previous one's
wake-up, so a long-lived watchdog does not build up nested tasks.
-/
private partial def round (wd : Watchdog) : BaseIO Unit := do
  if let some timer ← wd.timer.swap none then
    discard <| timer.stop.toBaseIO

  -- Publish the next wake-up before reading the state, so that an `arm` or a cancellation that
  -- comes after the read resolves this round's promise.
  let wake ← IO.Promise.new
  wd.wake.set wake
  if ← wd.ctx.isCancelled then
    return

  match ← wd.state.modifyGet (·.next (← IO.monoMsNow)) with
  | .stop => return
  | .fire => wd.ctx.cancel .deadline
  | .park => BaseIO.chainTask wake.result? fun _ => round wd
  | .sleep ms =>
    let started ← EIO.toBaseIO do
      let timer ← Internal.UV.Timer.mk (.ofNatClamp ms) false
      let elapsed ← timer.next
      wd.timer.set (some timer)
      BaseIO.chainTask (sync := true) elapsed.result? fun _ => wake.resolve ()
    match started with
    -- A deadline that cannot be enforced is treated as passed.
    | .error _ => wd.fire
    | .ok () => BaseIO.chainTask wake.result? fun _ => round wd

/--
Creates a watchdog that cancels `ctx` with `.deadline` when a wait outlives its deadline.

The watchdog and its timer stay alive until `ctx` is cancelled, so `ctx` should be cancelled once
the watchdog is no longer needed.
-/
def new (ctx : CancellationContext) : IO Watchdog := do
  let wd : Watchdog := {
    ctx
    state := ← IO.mkRef {}
    wake := ← IO.mkRef (← IO.Promise.new)
    timer := ← IO.mkRef none
  }
  BaseIO.chainTask (sync := true) (← ctx.done) fun _ => do (← wd.wake.get).resolve ()
  round wd
  return wd

/--
Sets the deadline of the current wait, unless the watchdog has fired or `epoch` is given and a later
call has armed or ended a wait since.
-/
private def armUntilIf (wd : Watchdog) (epoch : Option Nat) (deadline : Nat) : BaseIO Unit := do
  let wake ← wd.state.modifyGet fun s =>
    if s.fired || epoch.any (· != s.epoch) then
      (false, s)
    else
      -- Only a watchdog without a timer, or with one set for a later deadline, has to re-read it.
      (s.scheduled.all (deadline < ·),
        { s with waiting := true, deadline, epoch := s.epoch + 1 })
  if wake then
    (← wd.wake.get).resolve ()

/--
Starts a wait that must end by `deadline`, a value of `IO.monoMsNow`. Arming again before `disarm`
replaces the deadline. Does nothing once the watchdog has fired.
-/
def armUntil (wd : Watchdog) (deadline : Nat) : BaseIO Unit :=
  wd.armUntilIf none deadline

/--
Starts a wait that must end within `timeout` of `task` finishing, and that does not time out before
then: a deadline set for the current wait is dropped. If the wait ends, or is armed again, before
`task` finishes, nothing is armed. Does nothing once the watchdog has fired.
-/
def armAfter (wd : Watchdog) (task : Task α) (timeout : Std.Time.Millisecond.Offset) :
    BaseIO Unit := do
  let epoch ← wd.state.modifyGet fun s =>
    if s.fired then (s.epoch, s)
    else (s.epoch + 1, { s with waiting := false, epoch := s.epoch + 1 })
  BaseIO.chainTask (sync := true) task fun _ => do
    wd.armUntilIf (some epoch) ((← IO.monoMsNow) + timeout.toInt.toNat)

/--
Starts a wait that must end within `timeout`. Arming again before `disarm` replaces the deadline.
Does nothing once the watchdog has fired.
-/
def arm (wd : Watchdog) (timeout : Std.Time.Millisecond.Offset) : BaseIO Unit := do
  wd.armUntil ((← IO.monoMsNow) + timeout.toInt.toNat)

/--
Reports a wait marked as late: cancels the context with `.deadline` and returns whether that is its
reason, which it is not if the context was cancelled for another reason first. Cancelling here too
settles the reason while the watchdog's round has marked the wait late but not cancelled yet.
-/
private def settle (wd : Watchdog) : BaseIO Bool := do
  wd.ctx.cancel .deadline
  return (← wd.ctx.getCancellationReason) == some .deadline

/--
Ends the current wait. Returns `true` if a wait outlived its deadline, in which case the context is
cancelled with `.deadline`. A wait whose context was cancelled for another reason first is not
reported.
-/
def disarm (wd : Watchdog) : BaseIO Bool := do
  let now ← IO.monoMsNow
  -- The wait is checked here too, so that the verdict does not depend on the watchdog's own round
  -- having run, which needs a free worker of the task pool.
  let late ← wd.state.modifyGet fun s =>
    if s.fired then
      (true, s)
    else if s.waiting && now ≥ s.deadline then
      (true, { s with fired := true, waiting := false, scheduled := none })
    else
      (false, { s with waiting := false, epoch := s.epoch + 1 })
  if late then wd.settle else return false

/--
Returns `true` if a wait outlived its deadline and its context was cancelled with `.deadline`. If
the watchdog has marked a wait as late but not cancelled the context yet, this cancels it first.
-/
def hasFired (wd : Watchdog) : BaseIO Bool := do
  if (← wd.state.get).fired then wd.settle else return false

end Watchdog
end Async
end Std
