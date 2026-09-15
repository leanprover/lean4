import Std.Internal.UV

/-!
Timer finalizers racing the end of the program.

Detached tasks keep creating timers and dropping them once they have fired while `main` returns, so
finalizers run on worker threads until the task manager has drained, right before the event loop is
torn down. Each dropped timer is `FINISHED` with a resolved promise attached and no loop reference
keeping it alive, so its finalizer is what releases that promise.
-/

open Std.Internal.UV

partial def churn (n : Nat) : IO Unit := do
  if n == 0 then return ()
  let mut ts := #[]
  for _ in [0:64] do
    let t ← Timer.mk 1 false
    let p ← t.next
    ts := ts.push (t, p)
  for (_, p) in ts do
    discard <| IO.wait p.result?
  -- `ts` dies here: 64 timers are finalized at once, each with a resolved promise attached.
  churn (n - 1)

def main : IO Unit := do
  for _ in [0:8] do
    discard <| (churn 50).asTask
  IO.println "exiting"
