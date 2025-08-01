/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Std.Time
public import Std.Internal.UV.Timer
public import Std.Internal.Async.Select

public section


namespace Std
namespace Internal
namespace IO
namespace Async

/--
`Sleep` can be used to sleep for some duration once.
The underlying timer has millisecond resolution.
-/
structure Sleep where
  private ofNative ::
    native : Internal.UV.Timer

namespace Sleep

/--
Set up a `Sleep` that waits for `duration` milliseconds.
This function only initializes but does not yet start the timer.
-/
@[inline]
def mk (duration : Std.Time.Millisecond.Offset) : Async Sleep := do
  let native ← Internal.UV.Timer.mk duration.toInt.toNat.toUInt64 false
  return ofNative native

/--
If:
- `s` is not yet running start it and return an `Async` that will resolve once the previously
   configured `duration` has run out.
- `s` is already or not anymore running return the same `Async` as the first call to `wait`.
-/
@[inline]
def wait (s : Sleep) : Async Unit :=
  Async.ofPurePromise s.native.next

/--
If:
- `s` is still running the timer restarts counting from now and finishes after `duration`
  milliseconds.
- `s` is not yet or not anymore running this is a no-op.
-/
@[inline]
def reset (s : Sleep) : Async Unit :=
  s.native.reset

/--
If:
- `s` is still running this stops `s` without resolving any remaining `Async`s that were created
  through `wait`. Note that if another `Async` is binding on any of these it is going hang
  forever without further intervention.
- `s` is not yet or not anymore running this is a no-op.
-/
@[inline]
def stop (s : Sleep) : IO Unit :=
  s.native.stop

/--
Create a `Selector` that resolves once `s` has finished. Note that calling this function starts `s`
if it hasn't already started.
-/
def selector (s : Sleep) : Async (Selector Unit) := do
  let sleepWaiter ← s.wait.asTask
  return {
    tryFn := do
      if ← IO.hasFinished sleepWaiter then
        return some ()
      else
        return none
    registerFn waiter := do
      discard <| AsyncTask.mapIO (x := sleepWaiter) fun _ => do
        let lose := return ()
        let win promise := promise.resolve (.ok ())
        waiter.race lose win
    unregisterFn := pure ()
  }

end Sleep

/--
Return an `Async` that resolves after `duration`.
-/
def sleep (duration : Std.Time.Millisecond.Offset) : Async Unit := do
  let sleeper ← Sleep.mk duration
  sleeper.wait

/--
Return a `Selector` that resolves after `duration`.
-/
def Selector.sleep (duration : Std.Time.Millisecond.Offset) : Async (Selector Unit) := do
  let sleeper ← Sleep.mk duration
  sleeper.selector

/--
`Interval` can be used to repeatedly wait for some duration like a clock.
The underlying timer has millisecond resolution.
-/
structure Interval where
  private ofNative ::
    native : Internal.UV.Timer


namespace Interval

/--
Setup up an `Interval` that waits for `duration` milliseconds.
This function only initializes but does not yet start the timer.
-/
@[inline]
def mk (duration : Std.Time.Millisecond.Offset) (_ : 0 < duration := by decide) : IO Interval := do
  let native ← Internal.UV.Timer.mk duration.toInt.toNat.toUInt64 true
  return ofNative native

/--
If:
- `i` is not yet running start it and return an `Async` that resolves right away as the 0th
  multiple of `duration` has elapsed.
- `i` is already running and:
  - the tick from the last call of `i` has not yet finished return the same `Async` as the last
    call
  - the tick from the last call of `i` has finished return a new `Async` that waits for the
    closest next tick from the time of calling this function.
- `i` is not running anymore this is a no-op.
-/
@[inline]
def tick (i : Interval) : Async Unit := do
  Async.ofPurePromise i.native.next

/--
If:
- `Interval.tick` was called on `i` before the timer restarts counting from now and the next tick
   happens in `duration`.
- `i` is not yet or not anymore running this is a no-op.
-/
@[inline]
def reset (i : Interval) : IO Unit :=
  i.native.reset

/--
If:
- `i` is still running this stops `i` without resolving any remaining `Async` that were created
  through `tick`. Note that if another `Async` is binding on any of these it is going hang
  forever without further intervention.
- `i` is not yet or not anymore running this is a no-op.
-/
@[inline]
def stop (i : Interval) : IO Unit :=
  i.native.stop

end Interval

end Async
end IO
end Internal
end Std
