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
- `s` is not yet running start it and return an `Async` computation that will complete once the previously
   configured `duration` has elapsed.
- `s` is already or not anymore running return the same `Async` computation as the first call to `wait`.
-/
@[inline]
def wait (s : Sleep) : Async Unit :=
  Async.ofPurePromise s.native.next

/--
If:
- `s` is still running the timer restarts counting from now and completes after `duration`
  milliseconds.
- `s` is not yet or not anymore running this is a no-op.
-/
@[inline]
def reset (s : Sleep) : Async Unit :=
  s.native.reset

/--
If:
- `s` is still running this stops `s` without completing any remaining `Async` computations that were created
  through `wait`. Note that if another `Async` computation is binding on any of these it will hang
  forever without further intervention.
- `s` is not yet or not anymore running this is a no-op.
-/
@[inline]
def stop (s : Sleep) : IO Unit :=
  s.native.stop

/--
Create a `Selector` that resolves once `s` has finished. `s` only starts when it runs inside of a Selectable.
-/
def selector (s : Sleep) : Selector Unit :=
  {
    tryFn := do
      let sleepWaiter ← s.native.next
      if ← sleepWaiter.isResolved then
        return some ()
      else
        s.native.cancel
        return none

    registerFn waiter := do
      let sleepWaiter ← s.native.next
      BaseIO.chainTask sleepWaiter.result? fun
        | none => do
          return ()
        | some _ =>
          let lose := return ()
          let win promise := promise.resolve (.ok ())
          waiter.race lose win

    unregisterFn := s.native.cancel
  }

end Sleep

/--
Return an `Async` computation that completes after `duration`.
-/
def sleep (duration : Std.Time.Millisecond.Offset) : Async Unit := do
  let sleeper ← Sleep.mk duration
  sleeper.wait

/--
Return a `Selector` that completes after `duration`.
-/
def Selector.sleep (duration : Std.Time.Millisecond.Offset) : Async (Selector Unit) := do
  let sleeper ← Sleep.mk duration
  return sleeper.selector

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
- `i` is not yet running start it and return an `Async` computation that completes right away as the 0th
  multiple of `duration` has elapsed.
- `i` is already running and:
  - the tick from the last call of `i` has not yet finished return the same `Async` computation as the last
    call
  - the tick from the last call of `i` has finished return a new `Async` computation that waits for the
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
- `i` is still running this stops `i` without completing any remaining `Async` computations that were created
  through `tick`. Note that if another `Async` computation is binding on any of these it will hang
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
