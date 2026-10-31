import Lean

/-!
Benchmark: elaboration of a single list literal with `n` distinct `Nat` numerals, for growing `n`.
-/

open Lean Elab

def mkInput (n : Nat) : String :=
  let elems := String.intercalate ", " ((List.range n).map toString)
  s!"noncomputable def xs : List Nat := [{elems}]\n"

def runBench (n : Nat) : IO Unit := do
  let input := mkInput n
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
  IO.println s!"measurement: list_nat_{n} {(t1 - t0).toFloat / 1000.0} s"

#eval show IO Unit from do
  let bench := (← IO.getEnv "TEST_BENCH") == some "1"
  let ns := if bench then [1000, 2000, 4000, 8000, 16000] else [10, 100]
  for n in ns do
    runBench n
