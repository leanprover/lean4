import Std.Async

open Std Async

/-!
Timer and signal promises are `Except`s, so a timer or signal handler can fail. The failure must
reach whoever waits: `Sleep.wait`, `Interval.tick` and `Signal.Waiter.wait` fail with the error, and
a `Selectable.one` whose timer or signal selector failed returns that error, both when the failure is
already there when the select starts (`tryFn`) and when it happens while the select waits
(`registerFn`). It must not hang, and it must not count as the timer firing or the signal arriving.

The tests make the promise fail by resolving it themselves, which the holder of a promise from
`next` may do.
-/

def boom : IO.Error := .userError "boom"

/-- Runs `x` in a task and waits for it for at most 5 s. -/
def bounded (x : IO α) : IO α := do
  let task ← IO.asTask x
  let timeout ← IO.asTask (IO.sleep 5000)
  match ← IO.waitAny [task.map some, timeout.map fun _ => none] with
  | some res => IO.ofExcept res
  | none => throw <| .userError "timed out"

def expectBoom (what : String) (x : IO α) : IO Unit := do
  match ← (bounded x).toBaseIO with
  | .ok _ => IO.println s!"{what}: succeeded"
  | .error e => IO.println s!"{what}: {e}"

/-- Gives a select started in another task time to register its waiters. -/
def letSelectRegister : IO Unit := IO.sleep 100

/--
info: Sleep.wait: boom
Interval.tick: boom
Signal.Waiter.wait: boom
-/
#guard_msgs in
#eval show IO Unit from do
  let sleep ← (Sleep.mk 60000).block
  (← sleep.native.nextResult).resolve (.error boom)
  expectBoom "Sleep.wait" sleep.wait.block
  sleep.stop

  let interval ← Interval.mk 60000
  -- The 0th tick resolves at once; the next one is 60 s away.
  interval.tick.block
  let tick ← IO.asTask interval.tick.block
  letSelectRegister
  (← interval.native.nextResult).resolve (.error boom)
  expectBoom "Interval.tick" (IO.ofExcept =<< IO.wait tick)
  interval.stop

  let waiter ← Signal.Waiter.mk .sigwinch false
  (← waiter.native.nextResult).resolve (.error boom)
  expectBoom "Signal.Waiter.wait" do IO.ofExcept (← IO.wait (← waiter.wait))
  waiter.stop

/--
info: timer failed before the select: boom
timer fails during the select: boom
signal failed before the select: boom
signal fails during the select: boom
-/
#guard_msgs in
#eval show IO Unit from do
  let other ← (Sleep.mk 60000).block

  let sleep ← (Sleep.mk 60000).block
  (← sleep.native.nextResult).resolve (.error boom)
  expectBoom "timer failed before the select"
    (Selectable.one #[.case sleep.selector pure, .case other.selector pure]).block
  sleep.stop

  let sleep ← (Sleep.mk 60000).block
  let select ← IO.asTask (Selectable.one #[.case sleep.selector pure, .case other.selector pure]).block
  letSelectRegister
  (← sleep.native.nextResult).resolve (.error boom)
  expectBoom "timer fails during the select" (IO.ofExcept =<< IO.wait select)
  sleep.stop

  let waiter ← Signal.Waiter.mk .sigwinch false
  (← waiter.native.nextResult).resolve (.error boom)
  expectBoom "signal failed before the select"
    (Selectable.one #[.case waiter.selector pure, .case other.selector pure]).block
  waiter.stop

  let waiter ← Signal.Waiter.mk .sigwinch false
  let select ← IO.asTask (Selectable.one #[.case waiter.selector pure, .case other.selector pure]).block
  letSelectRegister
  (← waiter.native.nextResult).resolve (.error boom)
  expectBoom "signal fails during the select" (IO.ofExcept =<< IO.wait select)
  waiter.stop

  other.stop
