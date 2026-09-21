module

/-!
Change: during shutdown a worker over the limit exits instead of skipping the throttle, and
`enqueue_core` counts live workers (`m_num_std_workers`) instead of `m_std_workers.size()`.

After `main` returns, a pool task waits for each of 300 queued tasks in turn. Each wait starts a
replacement worker, and without the throttle every one of them also runs queued work, so the thread
count grows with the number of waits instead of staying at the limit.

Run: `LEAN_NUM_THREADS=2 lean --run -j2 proofs/exit_worker_limit.lean`
* with the change:    `peak: 2`
* without the change: a peak far above 2
-/

public def main : IO Unit := do
  let running ← IO.mkRef 0
  let peak ← IO.mkRef 0
  let started ← IO.Promise.new
  discard <| IO.asTask do
    started.resolve ()
    while !(← IO.checkCanceled) do IO.sleep 10
    let tasks ← (List.range 300).mapM fun _ => IO.asTask do
      let n ← running.modifyGet fun n => (n + 1, n + 1)
      peak.modify (max n)
      IO.sleep 5
      running.modify (· - 1)
    for t in tasks do discard <| IO.wait t
    IO.println s!"peak: {← peak.get}"
  discard <| IO.wait started.result?
