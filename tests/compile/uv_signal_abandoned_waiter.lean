import Std.Async

/-!
A `Signal.Waiter` that a select checked keeps listening, but once it is dropped it must stop
listening and restore the signal's default action: the event loop must not keep it alive. A child
copy of this program abandons such a waiter and then sends itself SIGINT; it must die from it. This
covers a one-shot waiter that lost a select, and a repeating waiter that `tryOne` found with the
signal already received.
-/

open Std Async

/--
Waits up to `n * 10` ms for the event loop to have no live handles. The select's last reference to
the waiter is released by pool tasks that may still be running after `block` returns.
-/
def waitForIdleLoop : Nat → IO Unit
  | 0 => pure ()
  | n + 1 => do
    if ← Internal.UV.Loop.alive then
      IO.sleep 10
      waitForIdleLoop n

def sendSigint : IO Unit := do
  let pid ← IO.Process.getPID
  discard <| IO.Process.output { cmd := "kill", args := #["-INT", toString pid] }

/-- Polls `tryOne` for up to `n * 10` ms until it reports the signal. -/
def pollUntilReady (waiter : Signal.Waiter) : Nat → IO Unit
  | 0 => pure ()
  | n + 1 => do
    if (← (Selectable.tryOne #[.case waiter.selector pure]).block).isNone then
      IO.sleep 10
      pollUntilReady waiter n

def abandonOneShot : IO Unit :=
  (do
    let waiter ← Signal.Waiter.mk .sigint false
    let sleep ← Selector.sleep 50
    discard <| Selectable.one #[
      .case waiter.selector (fun _ => pure ()),
      .case sleep (fun _ => pure ())]
    : Async Unit).block

def abandonRepeating : IO Unit := do
  let waiter ← Signal.Waiter.mk .sigint true
  -- Starts the waiter, so that the SIGINT below is kept for a later `tryOne`.
  discard <| (Selectable.tryOne #[.case waiter.selector pure]).block
  sendSigint
  pollUntilReady waiter 1000

def child (abandon : IO Unit) : IO Unit := do
  abandon
  waitForIdleLoop 1000
  sendSigint
  IO.sleep 2000
  IO.println "survived SIGINT"

def run (mode : String) : IO Unit := do
  if System.Platform.isWindows then
    IO.println s!"{mode} exit code: 130"
  else
    let proc ← IO.Process.spawn { cmd := (← IO.appPath).toString, args := #[mode] }
    IO.println s!"{mode} exit code: {← proc.wait}"

def main (args : List String) : IO Unit := do
  match args with
  | ["one-shot"] => child abandonOneShot
  | ["repeating"] => child abandonRepeating
  | _ =>
    run "one-shot"
    run "repeating"
