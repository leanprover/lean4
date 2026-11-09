/-!
`IO.Process.Child.kill` sends `SIGKILL` by default and `SIGTERM` with `force := false`, to the whole
process group if the child was spawned with `setsid`. A process killed by a signal reports 128 plus
the signal number as its exit code: 137 for `SIGKILL` and 143 for `SIGTERM`. Windows has no
signals, so the test does nothing there.
-/

open IO.Process

def check (name : String) (cond : Bool) (detail : String := "") : IO Unit :=
  unless cond do
    throw <| IO.userError s!"{name}: {detail}"

/-- Runs `script` in `sh` and waits until it prints `ready`, so that its traps are installed. -/
def spawnReady (script : String) (setsid := false) : IO (Child { stdout := .piped }) := do
  let child ← spawn { cmd := "sh", args := #["-c", script], stdout := .piped, setsid }
  let line ← child.stdout.getLine
  check "ready" (line == "ready\n") line.quote
  return child

#eval do
  if System.Platform.isWindows then
    return
  -- The default is `SIGKILL`, which ends even a process that ignores `SIGTERM`.
  let child ← spawnReady "trap '' TERM; echo ready; while :; do sleep 0.1; done"
  child.kill
  let code ← child.wait
  check "default kill" (code == 137) s!"{code}"

  let child ← spawn { cmd := "sleep", args := #["30"] }
  child.kill (force := false)
  let code ← child.wait
  check "SIGTERM" (code == 143) s!"{code}"

  -- `SIGTERM` can be handled.
  let child ← spawnReady "trap 'exit 3' TERM; echo ready; while :; do sleep 0.1; done"
  child.kill (force := false)
  let code ← child.wait
  check "handled SIGTERM" (code == 3) s!"{code}"

  -- The background subshell would print `survived` if it did not receive the signal as well.
  let child ← spawnReady (setsid := true) "(sleep 5; echo survived) & echo ready; wait"
  child.kill (force := false)
  let code ← child.wait
  check "SIGTERM with setsid" (code == 143) s!"{code}"
  let rest ← child.stdout.readToEnd
  check "SIGTERM reaches the process group" (rest == "") rest.quote
