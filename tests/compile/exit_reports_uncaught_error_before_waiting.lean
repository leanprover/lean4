/-!
An uncaught exception from `main` must be reported before exit waits for the remaining tasks, as
`lean --run` does. Otherwise a program whose background task never finishes hangs without ever
reporting the error.
-/

def main : IO Unit := do
  discard <| IO.asTask (prio := .dedicated) do
    IO.sleep 300
    IO.eprintln "task finished"
  throw <| IO.userError "boom"
