/-!
A task queued after the pool's workers have exited during shutdown must not leak.

`main` returns while a dedicated task is still running. The task waits until the task manager is
shutting down and its idle workers have exited, then queues a pool task that nobody waits for. That task
never runs, but it and everything its closure captures (here a 1 MB array) must still be freed. The leak
is only reported by LeakSanitizer, i.e. in the sanitize build. The program is compiled, as the interpreter
exits differently, hence `.no_interpret`.
-/

def main : IO Unit := do
  discard <| IO.asTask (prio := .dedicated) do
    -- `IO.checkCanceled` holds for every task once the task manager shuts down.
    while !(← IO.checkCanceled) do
      IO.sleep 10
    -- Long enough for the idle workers to exit.
    IO.sleep 100
    -- Sized at runtime, so that the array is allocated here rather than compiled to a constant.
    let payload := ByteArray.mk (Array.replicate (1024 * 1024 + (← IO.monoMsNow) % 2) 7)
    discard <| IO.asTask do
      -- Indexed at runtime, so that the closure captures the array rather than a value computed from it.
      IO.println s!"the queued task ran: {payload.get! ((← IO.monoMsNow) % payload.size)}"
  IO.println "main returns"
