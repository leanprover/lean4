import Std.Internal.UV

/-!
Races between `Std.Internal.UV.Signal` calls on other threads and the deliveries of a SIGUSR1 storm
that a child process sends (#15667). A repeating signal releases the event loop's reference with its
promise when it delivers, so each section checks an invariant that a lost or doubled reference, a
use after free, or a lost wakeup would break:

- `(sync := true)` continuations of a delivered promise that call `next`, `stop` or `cancel` or drop
  the last reference, for repeating and one-shot signals;
- several threads calling `next`, `cancel`, dropping and recreating signals, on their own signals and
  on a shared one: after the storm, a fresh `next` on each of them is resolved by one more signal;
- signals dropped on worker threads, with and without a pending promise, while they are delivered to;
  once the storm ends every one of them is freed;
- `next` from several threads, with every promise resolved by a later delivery.

A repeating guard signal stays installed throughout, so SIGUSR1 never takes its default action.
-/

open Std.Internal.UV

def check (cond : Bool) (msg : String) : IO Unit :=
  unless cond do throw <| IO.userError msg

def spin (us : Nat) : IO Unit := do
  let deadline := (← IO.monoNanosNow) + us * 1000
  while (← IO.monoNanosNow) < deadline do
    pure ()

/-- Waits up to `ms` milliseconds for `t`, throwing `what` on a timeout. -/
def waitFor (t : Task α) (ms : Nat) (what : String) : IO α := do
  let deadline := (← IO.monoMsNow) + ms
  while !(← IO.hasFinished t) do
    if (← IO.monoMsNow) > deadline then
      throw <| IO.userError s!"timed out: {what}"
    IO.sleep 1
  return t.get

def sigusr1 : Int32 := 10

def sendOne : IO Unit := do
  discard <| IO.Process.output { cmd := "kill", args := #["-USR1", toString (← IO.Process.getPID)] }

/-- After the storm, a pending `next` on the repeating signal `s` must be resolved by one more signal. -/
def resolvesAfterStorm (s : Signal) (what : String) : IO Unit := do
  let mut p ← s.next
  -- At most one signal is kept from the storm.
  if ← p.isResolved then
    p ← s.next
  check (!(← p.isResolved)) s!"{what}: kept more than one signal"
  sendOne
  check ((← waitFor p.result? 5000 what) == some 10) s!"{what}: wrong value"

def reentrant (n : Nat) : IO Unit := do
  for i in [0:n] do
    let repeating := i % 2 == 0
    let cell ← IO.mkRef (some (← Signal.mk sigusr1 repeating))
    let some s ← cell.get | unreachable!
    let p ← s.next
    let shape := (i / 2) % 5
    let t ← IO.mapTask (sync := true) (t := p.result?) fun _ => do
      let some s ← cell.get | return none
      match shape with
      | 0 => return some (← s.next)
      | 1 => s.stop; return none
      | 2 => s.cancel; return none
      | 3 => cell.set none; return none
      | _ => let q ← s.next; cell.set none; return some q
    if let some q ← IO.ofExcept (← waitFor t 5000 s!"continuation {shape}") then
      check ((← waitFor q.result? 5000 s!"`next` in continuation {shape}") == some 10) "wrong value"
    if let some s ← cell.get then
      s.stop

def workers (threads iters : Nat) (shared : Signal) : IO (Array Signal) := do
  let tasks ← (List.range threads).mapM fun k => IO.asTask (prio := .dedicated) do
    let mut own ← Signal.mk sigusr1 (k % 2 == 0)
    for i in [0:iters] do
      match (i + k) % 7 with
      | 0 => discard <| own.next
      | 1 => own.cancel
      | 2 => own ← Signal.mk sigusr1 (i % 2 == 0)
      | 3 => discard <| waitFor (← own.next).result? 5000 s!"own signal on thread {k}"
      | 4 => discard <| waitFor (← shared.next).result? 5000 s!"shared signal on thread {k}"
      | 5 => shared.cancel
      | _ => discard <| shared.next
      spin ((i * 7 + k) % 50)
    let left ← Signal.mk sigusr1 true
    discard <| left.next
    return left
  tasks.toArray.mapM fun t => do IO.ofExcept (← IO.wait t)

def finalizers (rounds : Nat) : IO Unit := do
  for _ in [0:rounds] do
    let mut tasks := #[]
    for j in [0:16] do
      -- Dropped after a delivery, after `cancel`, or with a pending promise (repeating, one-shot).
      let s ← Signal.mk sigusr1 (j % 4 != 3)
      let p ← s.next
      if j % 4 == 0 then
        discard <| waitFor p.result? 5000 "delivery before drop"
      else if j % 4 == 1 then
        s.cancel
      let ref ← IO.mkRef (some s)
      tasks := tasks.push (← IO.asTask (prio := .dedicated) do spin (j * 13 % 60); ref.set none)
    for t in tasks do
      IO.ofExcept (← IO.wait t)

def concurrentNext (threads iters : Nat) : IO Unit := do
  let shared ← Signal.mk sigusr1 true
  let tasks ← (List.range threads).mapM fun k => IO.asTask (prio := .dedicated) do
    let own ← Signal.mk sigusr1 true
    for i in [0:iters] do
      let p ← (if k % 2 == 0 then own else shared).next
      discard <| waitFor p.result? 5000 s!"`next` on thread {k}, iteration {i}"
    own.stop
  for t in tasks do
    IO.ofExcept (← IO.wait t)
  shared.stop

def main : IO Unit := do
  if System.Platform.isWindows then
    IO.println "ok"
    return
  let guard ← Signal.mk sigusr1 true
  discard <| guard.next
  let shared ← Signal.mk sigusr1 true
  let pid ← IO.Process.getPID
  let storm ← IO.Process.spawn {
    cmd := "sh", args := #["-c", s!"while kill -USR1 {pid} 2>/dev/null; do :; done"] }
  let result ← (do
    reentrant 200
    let left ← workers 4 400 shared
    finalizers 10
    concurrentNext 4 100
    return left).toBaseIO
  storm.kill
  discard <| storm.wait
  -- Lets the last signals of the storm arrive, so that each check below sees its own signal.
  IO.sleep 100
  let left ← IO.ofExcept result
  resolvesAfterStorm shared "shared signal"
  for s in left do
    resolvesAfterStorm s "worker's signal"
    s.stop
  shared.stop
  resolvesAfterStorm guard "guard"
  guard.stop
  -- The signals above also reached the dropped signals still pending, so all of them are freed.
  let mut idle := false
  for _ in [0:300] do
    if !(← Loop.alive) then
      idle := true
      break
    IO.sleep 10
  check idle "dropped signals still listening after the storm"
  IO.println "ok"
