import Std.Async

open Std Async

/-!
A failed timer or signal promise reaches whoever waits: `Sleep.wait` and a `Selectable.one` whose
selector failed before the select (`tryFn`) or while it waits (`registerFn`) fail with the error
instead of hanging or counting as fired. The tests fail a promise from `nextResult` by resolving it
themselves. `uv_finalize_cancels` covers a timer selector failing during the select. The promise of
`Signal.next` stays pending when the promise it follows fails.
-/

def boom : IO.Error := .userError "boom"

/--
Runs `x` in a task and waits for it for at most 5 s. The timeout sleeps on a thread of its own: on
a pool worker it could hold up `x`, which then finishes only as the timeout does.
-/
def bounded (x : IO α) : IO α := do
  let task ← IO.asTask x
  let timeout ← IO.asTask (prio := .dedicated) (IO.sleep 5000)
  match ← IO.waitAny [task.map some, timeout.map fun _ => none] with
  | some res => IO.ofExcept res
  | none => throw <| .userError "timed out"

def expectBoom (what : String) (x : IO α) : IO Unit := do
  match ← (bounded x).toBaseIO with
  | .ok _ => IO.println s!"{what}: succeeded"
  | .error e => IO.println s!"{what}: {e}"

/--
info: Sleep.wait: boom
timer failed before the select: boom
signal failed before the select: boom
signal fails during the select: boom
-/
#guard_msgs in
#eval show IO Unit from do
  let sleep ← (Sleep.mk 60000).block
  (← sleep.native.nextResult).resolve (.error boom)
  expectBoom "Sleep.wait" sleep.wait.block
  sleep.stop

  let other ← (Sleep.mk 60000).block

  let sleep ← (Sleep.mk 60000).block
  (← sleep.native.nextResult).resolve (.error boom)
  expectBoom "timer failed before the select"
    (Selectable.one #[.case sleep.selector pure, .case other.selector pure]).block
  sleep.stop

  let waiter ← Signal.Waiter.mk .sigwinch false
  (← waiter.native.nextResult).resolve (.error boom)
  expectBoom "signal failed before the select"
    (Selectable.one #[.case waiter.selector pure, .case other.selector pure]).block
  waiter.stop

  let waiter ← Signal.Waiter.mk .sigwinch false
  let select ← IO.asTask (Selectable.one #[.case waiter.selector pure, .case other.selector pure]).block
  IO.sleep 100
  (← waiter.native.nextResult).resolve (.error boom)
  expectBoom "signal fails during the select" (IO.ofExcept =<< IO.wait select)
  waiter.stop

  other.stop

/--
info: signal fails: pending
-/
#guard_msgs in
#eval show IO Unit from do
  -- SIGWINCH
  let signal ← Internal.UV.Signal.mk 28 false
  let received ← signal.next
  (← signal.nextResult).resolve (.error boom)
  IO.sleep 50
  IO.println s!"signal fails: {if ← received.isResolved then "resolved" else "pending"}"
  signal.stop
