import Std.Async

/-!
Re-entrant calls on a raw `Std.Internal.UV.Signal` from a `(sync := true)` continuation of the promise
that a delivery resolves (#15667). Such a continuation runs inline on the event loop thread, inside the
signal callback and under the loop lock, so it sees the signal halfway through the delivery. For
repeating and one-shot signals it calls `next`, `stop` or `cancel`, drops the last reference to the
signal, or drops or stops other signals for the same signal number, whose messages libuv dispatches
in the same loop iteration. Each case checks the resulting promises and that the loop ends up idle.

SIGWINCH is used because its default action is to ignore it.
-/

open Std.Internal.UV

/-- Waits up to `n * 10` ms for the event loop to have no live handles. -/
def waitForIdleLoop : Nat → IO Bool
  | 0 => return !(← Loop.alive)
  | n + 1 => do
    if ← Loop.alive then
      IO.sleep 10
      waitForIdleLoop n
    else
      return true

/-- Sends SIGWINCH, whose default action is to be ignored, to this process. -/
def sendWinch : IO Unit := do
  discard <| IO.Process.output { cmd := "kill", args := #["-WINCH", toString (← IO.Process.getPID)] }

def check (cond : Bool) (msg : String) : IO Unit :=
  unless cond do throw <| IO.userError msg

/-- Runs `k` as a `(sync := true)` continuation of `p`: inline on the thread that resolves `p`. -/
def onResolve (p : IO.Promise Int) (k : Int → IO α) : BaseIO (Task (Except IO.Error α)) :=
  IO.mapTask (sync := true) (t := p.result?) fun
    | some v => k v
    | none => throw <| IO.userError "promise dropped"

/-- Sends SIGWINCH and returns the result of the continuation that the delivery runs. -/
def deliver (t : Task (Except IO.Error α)) : IO α := do
  sendWinch
  IO.ofExcept (← IO.wait t)

def startIdle : IO Unit := do
  check (← waitForIdleLoop 500) "loop not idle at start"

-- Repeating, `next` in the continuation: a fresh pending promise, resolved by the following signal.
#eval show IO Unit from do
  if System.Platform.isWindows then return
  startIdle
  let s ← Signal.mk 28 true
  let p ← s.next
  let mainTid ← IO.getTID
  let t ← onResolve p fun v => do
    check ((← IO.getTID) != mainTid) "continuation did not run on the resolving thread"
    let q ← s.next
    let q' ← s.next
    return (v, q, q')
  let (v, q, q') ← deliver t
  check (v == 28) "wrong signal number"
  check (!(← q.isResolved)) "`next` inside the delivery returned a resolved promise"
  check (!(← q'.isResolved)) "second `next` inside the delivery returned a resolved promise"
  sendWinch
  check ((← IO.wait q.result?) == some 28) "promise from `next` inside the delivery not resolved"
  check ((← IO.wait q'.result?) == some 28) "second promise from `next` inside the delivery not resolved"
  s.stop
  check (← waitForIdleLoop 500) "loop not idle after stop"

-- Repeating, `stop` in the continuation: the signal stops listening at once.
#eval show IO Unit from do
  if System.Platform.isWindows then return
  startIdle
  let s ← Signal.mk 28 true
  let p ← s.next
  let t ← onResolve p fun _ => s.stop
  deliver t
  check (← waitForIdleLoop 500) "signal stopped inside the delivery still listening"
  let q ← s.next
  sendWinch
  IO.sleep 100
  check (!(← q.isResolved)) "`next` after a `stop` inside the delivery was resolved"

-- Repeating, `next` then `stop` in the continuation: the promise of that `next` is dropped.
#eval show IO Unit from do
  if System.Platform.isWindows then return
  startIdle
  let s ← Signal.mk 28 true
  let p ← s.next
  let t ← onResolve p fun _ => do
    let q ← s.next
    s.stop
    return q.result?
  let r ← deliver t
  check ((← IO.wait r) == none) "promise dropped by `stop` inside the delivery has a value"
  check (← waitForIdleLoop 500) "signal stopped inside the delivery still listening"

-- Repeating, `cancel` in the continuation is a no-op, and `next` then `cancel` keeps listening:
-- the following signal is reported by the next `next`.
#eval show IO Unit from do
  if System.Platform.isWindows then return
  startIdle
  let s ← Signal.mk 28 true
  let p ← s.next
  let t ← onResolve p fun _ => do
    s.cancel
    discard <| s.next
    s.cancel
  deliver t
  -- The cancelled signal is still installed; a second signal on a barrier tells when it was handled.
  let barrier ← Signal.mk 28 true
  let b ← barrier.next
  sendWinch
  discard <| IO.wait b.result?
  barrier.stop
  let q ← s.next
  check (← q.isResolved) "signal after `cancel` inside the delivery was not kept"
  let q' ← s.next
  check (!(← q'.isResolved)) "kept signal reported twice"
  s.stop
  check (← waitForIdleLoop 500) "loop not idle after stop"

/-- A repeating or one-shot signal referenced only through a cell that the continuation of its first
promise empties, after calling `next` when `nextFirst`. Returns that continuation. -/
def dropInside (repeating nextFirst : Bool) : IO (Task (Except IO.Error (Option (IO.Promise Int)))) := do
  let cell ← IO.mkRef (some (← Signal.mk 28 repeating))
  let some s ← cell.get | unreachable!
  let p ← s.next
  onResolve p fun _ => do
    let some s ← cell.get | throw <| IO.userError "signal already dropped"
    let q ← if nextFirst then some <$> s.next else pure none
    cell.set none
    return q

-- Repeating and one-shot, dropping the last reference in the continuation frees the signal there.
#eval show IO Unit from do
  if System.Platform.isWindows then return
  for repeating in [true, false] do
    startIdle
    let t ← dropInside repeating false
    discard <| deliver t
    check (← waitForIdleLoop 500) s!"signal dropped inside the delivery not freed (repeating: {repeating})"

-- Repeating, `next` then drop in the continuation: the pending promise keeps the signal alive, and the
-- following signal resolves it.
#eval show IO Unit from do
  if System.Platform.isWindows then return
  startIdle
  let t ← dropInside true true
  let some q ← deliver t | throw <| IO.userError "no promise"
  IO.sleep 100
  check (← Loop.alive) "dropped signal with a pending promise stopped listening"
  check (!(← q.isResolved)) "pending promise resolved without a signal"
  sendWinch
  check ((← IO.wait q.result?) == some 28) "pending promise of a dropped signal not resolved"
  check (← waitForIdleLoop 500) "signal not freed after its last promise resolved"

-- One-shot, `next`, `stop` and `cancel` in the continuation: the signal is already finished, so
-- `next` returns the resolved promise and `stop` and `cancel` change nothing.
#eval show IO Unit from do
  if System.Platform.isWindows then return
  startIdle
  let s ← Signal.mk 28 false
  let p ← s.next
  let t ← onResolve p fun _ => do
    let q ← s.next
    let resolved ← q.isResolved
    s.cancel
    s.stop
    return (resolved, q)
  let (resolved, q) ← deliver t
  check resolved "`next` inside a one-shot delivery returned a pending promise"
  check ((← IO.wait q.result?) == some 28) "wrong value from `next` inside a one-shot delivery"
  let q' ← s.next
  check ((← IO.wait q'.result?) == some 28) "one-shot lost its promise after `stop`/`cancel` inside the delivery"
  check (← waitForIdleLoop 500) "finished one-shot signal still listening"

/-- Signals for the same signal number, each started and then cancelled, so that they listen with no
promise pending, and referenced only through `cell`. -/
def listeners (cell : IO.Ref (Array Signal)) (repeating : Bool) (n : Nat) : IO Unit := do
  for _ in [0:n] do
    let b ← Signal.mk 28 repeating
    discard <| b.next
    b.cancel
    cell.modify (·.push b)

-- A delivery's continuation drops other signals for the same signal number, created both before and
-- after the delivering one, that libuv dispatches the same signal to in the same loop iteration.
#eval show IO Unit from do
  if System.Platform.isWindows then return
  for (repeating, others) in [(true, true), (true, false), (false, true), (false, false)] do
    startIdle
    let cell ← IO.mkRef #[]
    listeners cell others 8
    let s ← Signal.mk 28 repeating
    listeners cell others 8
    let p ← s.next
    let t ← onResolve p fun _ => cell.set #[]
    deliver t
    s.stop
    check (← waitForIdleLoop 500) s!"signals dropped inside another's delivery still listening ({repeating}, {others})"

-- A delivery's continuation stops other signals for the same signal number that wait on a promise:
-- each of their promises is either resolved by this signal or dropped by the `stop`.
#eval show IO Unit from do
  if System.Platform.isWindows then return
  for repeating in [true, false] do
    startIdle
    -- Only the signal holds each promise, so that `stop` drops it.
    let mk : IO (Signal × Task (Option Int)) := do
      let b ← Signal.mk 28 repeating
      return (b, (← b.next).result?)
    let before ← (List.range 8).mapM fun _ => mk
    let s ← Signal.mk 28 repeating
    let after ← (List.range 8).mapM fun _ => mk
    let others := before ++ after
    let p ← s.next
    let t ← onResolve p fun _ => others.forM fun (b, _) => b.stop
    deliver t
    for (_, q) in others do
      let r ← IO.wait q
      check (r == some 28 || r == none) s!"unexpected value {r}"
    s.stop
    check (← waitForIdleLoop 500) s!"signals stopped inside another's delivery still listening ({repeating})"

-- A signal created and started inside a delivery is not resolved by that delivery, only by the next.
#eval show IO Unit from do
  if System.Platform.isWindows then return
  startIdle
  let s ← Signal.mk 28 true
  let p ← s.next
  let t ← onResolve p fun _ => do
    let c ← Signal.mk 28 false
    return (c, ← c.next)
  let (c, q) ← deliver t
  IO.sleep 100
  check (!(← q.isResolved)) "signal started inside a delivery received that delivery"
  sendWinch
  check ((← IO.wait q.result?) == some 28) "signal started inside a delivery not resolved by the next one"
  s.stop
  c.stop
  check (← waitForIdleLoop 500) "loop not idle at the end"
