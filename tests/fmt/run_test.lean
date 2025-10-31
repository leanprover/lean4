import Lean.Fmt
import Lean.Language.Lean

/-!
Formats the file that is given as the only argument with `Lean.Fmt.fileMain` and prints the
result to stdout.
-/

open Lean

def main (args : List String) : IO UInt32 := do
  let [file] := args
    | IO.eprintln "usage: lean --run run_test.lean <file>"
      return 2
  let contents ← IO.FS.readFile file
  let inputCtx := Parser.mkInputContext contents file
  unsafe enableInitializersExecution
  let opts := Elab.inServer.set {} true
  let setup headerStx :=
    return .ok {
      mainModuleName := .anonymous
      isModule := headerStx.isModule
      imports := headerStx.imports
      opts
    }
  let initialSnap ← Language.Lean.process setup none { inputCtx with }
  match ← Fmt.fileMain initialSnap with
  | .error err =>
    IO.eprintln s!"error: {err}"
    return 1
  | .ok formatted =>
    IO.print formatted
    return 0
