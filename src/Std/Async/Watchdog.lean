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
  /-- A timed wait is in progress. -/
  waiting : Bool := false
  /-- When the current wait expires, as a value of `IO.monoMsNow`. -/
  deadline : Nat := 0
  /-- A wait outlived its deadline. The watchdog has then stopped. -/
  fired : Bool := false
  /-- The deadline the watchdog's timer is set for, or `none` while it waits without a timer. -/
  scheduled : Option Nat := none
  /-- How many waits have ended, so that `armAfter` can tell whether its wait is still in progress. -/
  ended : Nat := 0

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
`.deadline` and stops.

`arm` and `disarm` only update shared state. The timer is restarted only when a deadline is earlier
than the one it is set for, so waits that keep moving the deadline later, such as idle timeouts,
cost no timer operation each. The watchdog checks deadlines against `IO.monoMsNow` itself, so a
timer that fires early never cancels the context before the deadline.

The watchdog runs until its context is cancelled, so the context should be cancelled once the
watchdog is no longer needed.
-/
structure Watchdog where
  private mk ::
  private ctx : CancellationContext
  private state : IO.Ref Watchdog.State
  /-- Resolved to make the watchdog re-read `state`. Each round of the watchdog replaces it. -/
  private wake : IO.Ref (IO.Promise Unit)
  /-- The timer of the watchdog's current round, stopped when the next round starts. -/
  private timer : IO.Ref (Option Internal.UV.Timer)

namespace Watchdog

private def timeoutOf (ms : Nat) : UInt64 :=
  if ms < UInt64.size then ms.toUInt64 else (UInt64.size - 1).toUInt64

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
      let timer ← Internal.UV.Timer.mk (timeoutOf ms) false
      let elapsed ← timer.next
      wd.timer.set (some timer)
      BaseIO.chainTask (sync := true) elapsed.result? fun _ => wake.resolve ()
    match started with
    -- A deadline that cannot be enforced is treated as passed.
    | .error _ => wd.fire
    | .ok () => BaseIO.chainTask wake.result? fun _ => round wd

/--
Creates a watchdog that cancels `ctx` with `.deadline` when a wait outlives its deadline.
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
Sets the deadline of the current wait, unless the watchdog has fired or `ended` is given and is no
longer the number of waits that have ended.
-/
private def armUntilIf (wd : Watchdog) (ended : Option Nat) (deadline : Nat) : BaseIO Unit := do
  let wake ← wd.state.modifyGet fun s =>
    if s.fired || ended.any (· != s.ended) then
      (false, s)
    else
      -- Only a watchdog without a timer, or with one set for a later deadline, has to re-read it.
      (s.scheduled.all (deadline < ·), { s with waiting := true, deadline })
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
then. If the wait ends before `task` finishes, nothing is armed.
-/
def armAfter (wd : Watchdog) (task : Task α) (timeout : Std.Time.Millisecond.Offset) :
    BaseIO Unit := do
  let ended := (← wd.state.get).ended
  BaseIO.chainTask (sync := true) task fun _ => do
    wd.armUntilIf (some ended) ((← IO.monoMsNow) + timeout.toInt.toNat)

/--
Starts a wait that must end within `timeout`. Arming again before `disarm` replaces the deadline.
Does nothing once the watchdog has fired.
-/
def arm (wd : Watchdog) (timeout : Std.Time.Millisecond.Offset) : BaseIO Unit := do
  wd.armUntil ((← IO.monoMsNow) + timeout.toInt.toNat)

/--
Ends the current wait. Returns `true` if a wait outlived its deadline, in which case the watchdog
cancels its context with `.deadline`.
-/
def disarm (wd : Watchdog) : BaseIO Bool :=
  wd.state.modifyGet fun s =>
    if s.fired then (true, s) else (false, { s with waiting := false, ended := s.ended + 1 })

/--
Returns `true` if a wait outlived its deadline.
-/
def hasFired (wd : Watchdog) : BaseIO Bool :=
  return (← wd.state.get).fired

end Watchdog
end Async
end Std
