import Std.Internal.UV

/-!
Regression guard for libuv teardown racing handle finalizers.

`finalize_libuv` runs before the task manager is destroyed, so worker threads are still dropping
references while the teardown walk inspects handles. A handle finalizer that touched its state
before consulting the loop state used to leave a stale `m_promise` behind, which the walk then
resolved and released a second time — a refcount underflow that corrupted the heap and crashed
roughly a third of the runs.

Detached tasks churn timers that have already fired (so they are `FINISHED` with a promise still
attached and no loop reference keeping them alive) while `main` returns and teardown starts.
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
    match p.result!.get with
    | .ok _ => pure ()
    | .error _ => pure ()
  -- `ts` dies here: 64 timers are finalized at once, each with a resolved promise attached.
  churn (n - 1)

def main : IO Unit := do
  for _ in [0:8] do
    discard <| (churn 100000).asTask
  IO.sleep 300
  IO.println "exiting"
