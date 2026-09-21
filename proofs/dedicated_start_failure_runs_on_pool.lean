module
import all Lean.Shell

/-!
Change: `spawn_dedicated_worker` returns `false` when its thread cannot start, and `enqueue_core`
then queues the task on the pool at `LEAN_MAX_PRIO`.

Before, the failed start threw a C++ exception that Lean code cannot catch. On a direct spawn or a
map of a finished task, it leaked the task and its closure, and exit hung on the dedicated-worker
count. On a map of a task that finishes later, it threw out of the resolving thread in the middle of
`handle_finished`, leaving the source's other dependents unqueued.

Run: `lean --run proofs/dedicated_start_failure_runs_on_pool.lean`
* with the change:    `1`, `2`, `3`
* without the change: `failed to create thread: ...`, exit status 1
-/

public def main : IO Unit := do
  discard <| IO.wait (← IO.asTask (pure ()))
  let p ← IO.Promise.new
  Lean.Internal.setThreadStackSize ((1 : USize) <<< 60)
  let spawned ← IO.asTask (prio := .dedicated) (pure 1)
  let mapped ← IO.mapTask (prio := .dedicated) (t := Task.pure 2) pure
  let deferred ← IO.mapTask (prio := .dedicated) (t := p.result!) pure
  p.resolve 3
  for t in [spawned, mapped, deferred] do
    IO.println (← IO.ofExcept (← IO.wait t))
