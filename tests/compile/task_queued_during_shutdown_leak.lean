/-!
A task queued during the exit still runs, so it does not leak.

`main` returns while a dedicated task is still running. The task waits until the task manager is
shutting down, then queues a pool task that nobody waits for. That task must still run, and it and
everything its closure captures (here a 1 MB array) must be freed. A leak is only reported by
LeakSanitizer, i.e. in the sanitize build. The program is compiled, as the interpreter exits differently,
hence `.no_interpret`.
-/

def main : IO Unit := do
  discard <| IO.asTask (prio := .dedicated) do
    -- `IO.checkCanceled` holds for every task once the task manager shuts down.
    while !(← IO.checkCanceled) do
      IO.sleep 10
    -- Sized at runtime, so that the array is allocated here rather than compiled to a constant.
    let payload := ByteArray.mk (Array.replicate (1024 * 1024 + (← IO.monoMsNow) % 2) 7)
    discard <| IO.asTask do
      -- Indexed at runtime, so that the closure captures the array rather than a value computed from it.
      IO.println s!"the queued task ran: {payload.get! ((← IO.monoMsNow) % payload.size)}"
  IO.println "main returns"
