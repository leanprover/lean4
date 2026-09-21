/-!
While exit waits for a running task, the work it waits for runs within the worker limit. The task
waits for each of many queued tasks in turn, and every wait from a pool task starts a replacement
worker; at most `LEAN_NUM_THREADS` of the queued tasks may run at once.
-/

def main : IO Unit := do
  let running ← IO.mkRef 0
  let peak ← IO.mkRef 0
  let started ← IO.Promise.new
  discard <| IO.asTask do
    started.resolve ()
    while !(← IO.checkCanceled) do IO.sleep 10
    let tasks ← (List.range 40).mapM fun _ => IO.asTask do
      let n ← running.modifyGet fun n => (n + 1, n + 1)
      peak.modify (max n)
      IO.sleep 20
      running.modify (· - 1)
    for t in tasks do discard <| IO.wait t
    IO.println s!"peak within limit: {decide ((← peak.get) ≤ 2)}"
  discard <| IO.wait started.result?
