import Std.Internal.UV

/-!
Repeating timers and signals hand the loop's reference back as soon as their promise resolves, so one
dropped without `stop` is freed at once instead of lingering until one more tick or delivery, which it
used to consume (#14202). Drives every way of leaving a repeating handle behind: dropped after its
promise resolved, while a promise is pending, after `cancel`, and after the caller resolved the
promise itself. Also checks that a repeating timer with a 0 ms period keeps ticking rather than
firing once.
-/

open Std.Internal.UV

/--
Waits for `p`, failing after 5 s instead of hanging the test. The deadline is a timer promise rather
than a sleeping task: exit waits for running tasks, but keeps a pending timer promise unresolved.
-/
def awaitBounded {α : Type} (what : String) (p : IO.Promise α) : IO Unit := do
  let deadline ← (← Timer.mk 5000 false).next
  let resolved ← IO.waitAny [p.result?.map (·.isSome), deadline.result?.map (fun _ => false)]
  unless resolved do
    throw <| IO.userError s!"{what}: not resolved within 5 s"

def timers : IO Unit := do
  let zero ← Timer.mk 0 true
  for i in [0:5] do
    awaitBounded s!"0 ms period, tick {i}" (← zero.next)
  zero.stop

  for _ in [0:20] do
    -- Dropped right after its promise resolved.
    let t ← Timer.mk 3600000 true
    awaitBounded "0th tick" (← t.next)

    -- Dropped with a promise pending.
    let t ← Timer.mk 3600000 true
    awaitBounded "0th tick" (← t.next)
    discard <| t.next

    -- Re-armed after `cancel`, then dropped after `cancel`.
    let t ← Timer.mk 2 true
    awaitBounded "0th tick" (← t.next)
    discard <| t.next
    t.cancel
    awaitBounded "tick after cancel" (← t.next)
    discard <| t.next
    t.cancel

    -- The caller resolves the promise before the loop does.
    let t ← Timer.mk 2 true
    awaitBounded "0th tick" (← t.next)
    let p ← t.next
    p.resolve ()
    awaitBounded "tick after a caller-resolved promise" (← t.next)

def signals : IO Unit := do
  -- SIGWINCH, which libuv accepts on every platform and whose default action is to ignore it.
  for _ in [0:20] do
    let s ← Signal.mk 28 true
    discard <| s.next
    let s ← Signal.mk 28 true
    discard <| s.next
    s.cancel
    let s ← Signal.mk 28 true
    discard <| s.next
    s.stop

  if System.Platform.isWindows then
    return

  -- Dropped right after a delivery resolved its promise. Each delivery also reaches the handles
  -- dropped above with a promise pending, which are then freed from inside their callback.
  let pid ← IO.Process.getPID
  for i in [0:5] do
    let s ← Signal.mk 28 true
    let p ← s.next
    discard <| IO.Process.output { cmd := "kill", args := #["-WINCH", toString pid] }
    awaitBounded s!"SIGWINCH delivery {i}" p

def main : IO Unit := do
  timers
  signals
  IO.println "done"
