module

/-!
Change: `scoped_waiting` only counts waiters; the shutdown wake-up in `wait_for` is skipped for pool
workers, whose own replacement branch already starts one.

During shutdown, a pool task calls `Task.get` on queued work. The pool branch of `wait_for` spawns
one replacement worker. Without the change, `scoped_waiting` spawns a second one, so queued work
that nobody waits for runs concurrently with the awaited task.

`waited` has the highest priority, so a single worker runs it first and `unwaited` only runs
afterwards. `waited` polls for 1 s to see whether `unwaited` ran in the meantime.

Run: `lean --run proofs/pool_get_double_spawn.lean`
* with the change:    `unwaited ran concurrently: false`
* without the change: `unwaited ran concurrently: true`
-/

public def main : IO Unit := do
  discard <| IO.asTask do
    -- Wait until exit has started, and give idle workers time to exit.
    while !(← IO.checkCanceled) do IO.sleep 10
    IO.sleep 200
    let ran ← IO.mkRef false
    discard <| IO.asTask (ran.set true)
    let waited ← IO.asTask (prio := .max) do
      for _ in [0:20] do
        if ← ran.get then break
        IO.sleep 50
      ran.get
    match waited.get with
    | .ok b => IO.println s!"unwaited ran concurrently: {b}"
    | .error e => IO.println s!"error: {e}"
