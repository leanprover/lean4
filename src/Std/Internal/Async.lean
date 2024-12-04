/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Std.Time
import Std.Internal.UV


namespace Std
namespace Internal
namespace IO
namespace Async

/--
A `Task` that may resolve to a value or an `IO.Error`.
-/
def AsyncTask (α : Type u) : Type u := Task (Except IO.Error α)

namespace AsyncTask

@[inline]
protected def pure (x : α) : AsyncTask α := Task.pure <| .ok x

instance : Pure AsyncTask where
  pure := AsyncTask.pure

@[inline]
protected def bind (x : AsyncTask α) (f : α → AsyncTask β) : AsyncTask β :=
  Task.bind x fun r =>
    match r with
    | .ok a => f a
    | .error e => Task.pure <| .error e

-- TODO: variants with explicit error handling

@[inline]
def bindIO (x : AsyncTask α) (f : α → IO (AsyncTask β)) : BaseIO (AsyncTask β) :=
  IO.bindTask x fun r =>
    match r with
    | .ok a => f a
    | .error e => .error e

@[inline]
def mapIO (f : α → β) (x : AsyncTask α) : BaseIO (AsyncTask β) :=
  IO.mapTask (t := x) fun r =>
    match r with
    | .ok a => pure (f a)
    | .error e => .error e

/--
Run the `AsyncTask` in `x` and block until it finishes.
-/
def spawnBlocking (x : IO (AsyncTask α)) : IO α := do
  let t ← x
  let res := t.get
  match res with
  | .ok a => return a
  | .error e => .error e

@[inline]
def spawn (x : IO α) : BaseIO (AsyncTask α) := do
  IO.asTask x

@[inline]
def ofPromise (x : IO.Promise α) : AsyncTask α :=
  x.result.map pure

@[inline]
def getState (x : AsyncTask α) : BaseIO IO.TaskState :=
  IO.getTaskState x

end AsyncTask

/--
`Sleep` can be used to sleep for some duration once.
The underlying timer has millisecond resolution.
-/
structure Sleep where
  private ofNative ::
    native : Internal.UV.Timer

-- TODO: provable constraints on duration after changes in Std.Time

namespace Sleep

/--
Set up a `Sleep` that waits for `duration` milliseconds.
This function only initializes but does not yet start the underlying timer.
-/
def mk (duration : Std.Time.Millisecond.Offset) : IO Sleep := do
  let native ← Internal.UV.Timer.mk duration.toInt.toNat.toUInt64 false
  return ofNative native

/--
Start the underlying timer of `s` and return an `AsyncTask` that will resolve once the previously
configured duration has run out. Running this function twice returns the same `AsyncTask`.
-/
def wait (s : Sleep) : IO (AsyncTask Unit) := do
  let promise ← s.native.next
  return .ofPromise promise

/--
If:
- `Sleep.wait` was previously called on `s` this makes the timer wait for `duration` counting from
  the call of this function.
- `Sleep.wait` was never called on `s` before this is a no-op.
-/
def reset (s : Sleep) : IO Unit :=
  s.native.reset

end Sleep

/--
Return an `AsyncTask` that resolves after `duration`.
-/
def sleep (duration : Std.Time.Millisecond.Offset) : IO (AsyncTask Unit) := do
  let sleeper ← Sleep.mk duration
  sleeper.wait

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
This function only initializes but does not yet start the underlying timer.
-/
def mk (duration : Std.Time.Millisecond.Offset) : IO Interval := do
  let native ← Internal.UV.Timer.mk duration.toInt.toNat.toUInt64 true
  return ofNative native

/--
Start the underlying timer of `s` and return an `AsyncTask` that will resolve upon the next tick
of `i`. In particular:
- calling this function for the first time starts the underlying timer of `i` and returns an
  `AsyncTask` that instantly resolves as the 0th multiple of `duration` has elapsed.
- calling this function while the tick from the last call has not yet finished returns the same
  `AsyncTask` as the last call.
- calling this function when the tick from the last call has finished returns a new `AsyncTask`
  that waits for the closest next tick from the time of calling this function.
-/
def tick (i : Interval) : IO (AsyncTask Unit) := do
  let promise ← i.native.next
  return .ofPromise promise

/--
If:
- `Interval.tick` was called on `i` before the next internal timer restarts counting from now and
  the next tick happens in `duration`.
- `Interval.tick` was never called on `i` before this is a no-op.
-/
def reset (i : Interval) : IO Unit :=
  i.native.reset

end Interval

end Async
end IO
end Internal
end Std
