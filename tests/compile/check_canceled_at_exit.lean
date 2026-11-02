/-!
A task that polls `IO.checkCanceled` is still running when `main` returns. The shutdown of the task
manager makes `IO.checkCanceled` return `true`, so the task stops and the program exits. The
ThreadSanitizer CI job runs this test to check that the shutdown flag is read without a data race.
-/

def main : IO Unit := do
  let started ← IO.Promise.new
  discard <| IO.asTask (prio := .dedicated) do
    started.resolve ()
    for _ in [0:10000] do
      if (← IO.checkCanceled) then
        IO.println "canceled at exit"
        return
      IO.sleep 1
    IO.println "not canceled"
  discard <| IO.wait started.result?
