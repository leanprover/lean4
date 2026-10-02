import Lean

/-!
Benchmark: per-command overhead of the frontend on a file with many trivial commands.

The `Command.State` of every command is captured by the tasks spawned for that command, so any
part of the state that grows with the number of commands must be a persistent data structure.
A flat `Array` that is pushed to once per command is shared with those tasks, so the push copies
it, and the cost of a command grows linearly with its position in the file.

The input is generated as a string and elaborated with `Lean.Elab.process` in an environment that
imports only `Init`, with the options the command line driver sets, so the run is the same as
`lean file.lean` on the generated input. The time for `2n` commands should be about twice the
time for `n` commands.
-/

open Lean Elab

/-- `numCmds` trivial theorems. -/
def mkInput (numCmds : Nat) : String := Id.run do
  let mut s := ""
  for i in [0:numCmds] do
    s := s ++ s!"theorem t{i} : ({i} : Nat) = {i} := rfl\n"
  return s

def runBench (numCmds : Nat) : IO Unit := do
  let input := mkInput numCmds
  unsafe enableInitializersExecution
  let env ← importModules #[{ module := `Init }] {} (loadExts := true)
  let opts := internal.cmdlineSnapshots.set {} true
  let opts := Elab.async.set opts true
  let t0 ← IO.monoMsNow
  let (_, msgs) ← Lean.Elab.process input env opts
  let t1 ← IO.monoMsNow
  if msgs.hasErrors then
    for msg in msgs.toArray do
      IO.println (← msg.toString)
    throw <| IO.userError "unexpected errors"
  IO.println s!"measurement: cmds_{numCmds} {(t1 - t0).toFloat / 1000.0} s"

#eval show IO Unit from do
  let bench := (← IO.getEnv "TEST_BENCH") == some "1"
  if bench then
    runBench 16000
    runBench 32000
  else
    runBench 200
